import asyncio, contextvars, pathlib, html, io, json, logging, math, os, re, sqlite3, time
from datetime import datetime, timezone
from collections import Counter
from contextlib import closing
from html.parser import HTMLParser

import httpx
from telegram import (InlineKeyboardButton, InlineKeyboardMarkup as Markup,
                      LabeledPrice, Update, BotCommand, InputMediaPhoto)
from telegram.error import BadRequest, TelegramError
from telegram.ext import (Application, ApplicationHandlerStop, CallbackQueryHandler,
                          CommandHandler, ContextTypes, MessageHandler, PreCheckoutQueryHandler,
                          TypeHandler, filters)

def Btn(text, *, style=None, **kwargs):
    data = str(kwargs.get("callback_data") or "")
    if style is None:
        if (data.startswith(("adm_del", "adm_prd")) or data == "cop_rm"
                or (data.startswith("apbad:") and data.endswith(":no"))
                or text.lstrip().startswith(("🗑", "❌", "🔕"))):
            style = "danger"
        elif (data in ("home", "co_back", "lang")
              or data.startswith(("adm", "cfg_")) and not data.startswith("adm_add")
              or text.lstrip().startswith(("⬅", "➡", "Вперёд", "Back", "Next"))):
            style = "primary"
        else:
            style = "success"
    api_kwargs = dict(kwargs.pop("api_kwargs", None) or {})
    api_kwargs["style"] = style
    return InlineKeyboardButton(text, api_kwargs=api_kwargs, **kwargs)

BASE_DIR = os.path.dirname(os.path.abspath(__file__))

def _load_env():
    for filename in ("config.env",):
        path = os.path.join(BASE_DIR, filename)
        if os.path.exists(path):
            with open(path, encoding="utf-8") as fh:
                for line in fh:
                    line = line.strip().lstrip("\ufeff")
                    if line and not line.startswith("#") and "=" in line:
                        k, v = line.split("=", 1)
                        os.environ.setdefault(k.strip(), v.strip().strip('"').strip("'"))

_load_env()
BOT_TOKEN = os.getenv("BOT_TOKEN", "")
ADMIN_IDS = {int(x) for x in os.getenv("ADMIN_IDS", "").replace(" ", "").replace(";", ",").split(",")
             if x.lstrip("-").isdigit()}
DB_FILE = os.path.join(BASE_DIR, "shop.db")
REPLACE_DAYS = 7
MAX_PAYMENT_RUB = 10_000
MAX_KEYS_FILE_BYTES = 2 * 1024 * 1024
MAX_IMPORT_KEYS = 10_000

logging.basicConfig(format="%(asctime)s %(levelname)s %(message)s", level=logging.INFO)
log = logging.getLogger("shop")


db = sqlite3.connect(DB_FILE, check_same_thread=False, isolation_level=None)
db.row_factory = sqlite3.Row
SCHEMA = """
CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY, username TEXT, name TEXT, joined INTEGER,
    lang TEXT DEFAULT 'ru', balance INTEGER DEFAULT 0, ref_by INTEGER, banned INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS sections(id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT, photo TEXT, description TEXT DEFAULT '');
CREATE TABLE IF NOT EXISTS products(id INTEGER PRIMARY KEY AUTOINCREMENT, section_id INTEGER,
    name TEXT, description TEXT, price INTEGER, photo TEXT, instruction TEXT,
    duration INTEGER DEFAULT 0, price_rub INTEGER DEFAULT 0, unlimited INTEGER DEFAULT 0, pinned INTEGER DEFAULT 0, sort_order INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS keys(id INTEGER PRIMARY KEY AUTOINCREMENT, product_id INTEGER,
    value TEXT, sold_to INTEGER, sold_at INTEGER, kind TEXT DEFAULT 'text', bad INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS orders(id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, payer INTEGER DEFAULT 0,
    product_id INTEGER DEFAULT 0, product_name TEXT, key_value TEXT, stars INTEGER DEFAULT 0,
    rub INTEGER DEFAULT 0, value INTEGER DEFAULT 0, bal_used INTEGER DEFAULT 0, promo_id INTEGER DEFAULT 0,
    charge_id TEXT, ts INTEGER, expires INTEGER DEFAULT 0, refunded INTEGER DEFAULT 0,
    cashback INTEGER DEFAULT 0, ref_bonus INTEGER DEFAULT 0, ref_to INTEGER DEFAULT 0,
    method TEXT DEFAULT 'stars', replace_status TEXT DEFAULT '');
CREATE TABLE IF NOT EXISTS order_keys(order_id INTEGER, key_id INTEGER);
CREATE TABLE IF NOT EXISTS reviews(id INTEGER PRIMARY KEY AUTOINCREMENT, order_id INTEGER UNIQUE,
    product_id INTEGER, user_id INTEGER, stars INTEGER, comment TEXT, ts INTEGER);
CREATE TABLE IF NOT EXISTS tickets(id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, text TEXT,
    status TEXT DEFAULT 'open', ts INTEGER);
CREATE TABLE IF NOT EXISTS promos(id INTEGER PRIMARY KEY AUTOINCREMENT, code TEXT UNIQUE, kind TEXT,
    value INTEGER, max_uses INTEGER DEFAULT 0, used INTEGER DEFAULT 0, expires INTEGER DEFAULT 0,
    active INTEGER DEFAULT 1, owner INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS promo_uses(promo_id INTEGER, user_id INTEGER, PRIMARY KEY(promo_id, user_id));
CREATE TABLE IF NOT EXISTS admins(id INTEGER PRIMARY KEY);
CREATE TABLE IF NOT EXISTS restock_subs(user_id INTEGER, product_id INTEGER, PRIMARY KEY(user_id, product_id));
CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
CREATE TABLE IF NOT EXISTS payments(id TEXT PRIMARY KEY, payer INTEGER, owner INTEGER, pid INTEGER,
    promo_id INTEGER DEFAULT 0, bal_used INTEGER DEFAULT 0, final INTEGER, rub INTEGER, method INTEGER,
    status TEXT DEFAULT 'pending', ts INTEGER);
CREATE TABLE IF NOT EXISTS topups(id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER, method TEXT,
    paid INTEGER, credited INTEGER, charge_id TEXT UNIQUE, ts INTEGER);
"""

def _add_col(table, col, ddl, connection=None):
    target = connection if connection is not None else db
    cols = {r["name"] for r in target.execute(f"PRAGMA table_info({table})")}
    if col not in cols: target.execute(f"ALTER TABLE {table} ADD COLUMN {col} {ddl}")

def init_shop_extensions(target):
    for table, col, ddl in (
        ("products", "delivery_type", "TEXT DEFAULT 'key'"),
        ("products", "delivery_config", "TEXT DEFAULT '{}'"),
        ("products", "low_threshold", "INTEGER DEFAULT 3"),
        ("products", "low_notified", "INTEGER DEFAULT 0"),
        ("admins", "role", "TEXT DEFAULT 'manager'"),
        ("orders", "delivery_type", "TEXT DEFAULT 'key'"),
        ("orders", "delivery_config", "TEXT DEFAULT '{}'"),
    ): _add_col(table, col, ddl, target)
    target.executescript("""
    CREATE TABLE IF NOT EXISTS favorites(user_id INTEGER, product_id INTEGER,
        PRIMARY KEY(user_id,product_id));
    CREATE TABLE IF NOT EXISTS balance_history(id INTEGER PRIMARY KEY, user_id INTEGER,
        delta INTEGER, balance_after INTEGER, ts INTEGER, actor INTEGER DEFAULT 0);
    CREATE TABLE IF NOT EXISTS audit_log(id INTEGER PRIMARY KEY, actor INTEGER,
        entity TEXT, entity_id INTEGER, action TEXT, ts INTEGER);
    CREATE TRIGGER IF NOT EXISTS balance_ledger AFTER UPDATE OF balance ON users
    WHEN NEW.balance != OLD.balance BEGIN
        INSERT INTO balance_history(user_id,delta,balance_after,ts,actor)
        VALUES(NEW.id,NEW.balance-OLD.balance,NEW.balance,strftime('%s','now'),shop_actor());
    END;
    CREATE TRIGGER IF NOT EXISTS order_delivery_snapshot AFTER INSERT ON orders BEGIN
        UPDATE orders SET delivery_type=COALESCE((SELECT delivery_type FROM products WHERE id=NEW.product_id),'key'),
        delivery_config=COALESCE((SELECT delivery_config FROM products WHERE id=NEW.product_id),'{}') WHERE id=NEW.id;
    END;
    """)
    _add_col("balance_history", "reason", "TEXT DEFAULT 'Изменение баланса'", target)
    target.execute("DROP TRIGGER IF EXISTS balance_ledger")
    target.executescript("""CREATE TRIGGER balance_ledger AFTER UPDATE OF balance ON users
        WHEN NEW.balance != OLD.balance BEGIN
        INSERT INTO balance_history(user_id,delta,balance_after,ts,actor,reason)
        VALUES(NEW.id,NEW.balance-OLD.balance,NEW.balance,strftime('%s','now'),shop_actor(),shop_reason()); END;""")
    for table in ("products", "sections", "keys", "admins", "settings", "promos"):
        key = "rowid"
        for action in ("INSERT", "UPDATE", "DELETE"):
            ref = "OLD" if action == "DELETE" else "NEW"
            target.execute(f"""CREATE TRIGGER IF NOT EXISTS audit_{table}_{action}
                AFTER {action} ON {table} BEGIN
                INSERT INTO audit_log(actor,entity,entity_id,action,ts)
                VALUES(shop_actor(),'{table}',{ref}.{key},'{action}',strftime('%s','now')); END""")

ACTOR = contextvars.ContextVar("shop_actor", default=0)
BALANCE_REASON = contextvars.ContextVar("balance_reason", default="Изменение баланса")
def balance_change(reason,sql,args):
    token=BALANCE_REASON.set(reason)
    try: return db.execute(sql,args)
    finally: BALANCE_REASON.reset(token)

def init_db(connection=None):
    target = connection if connection is not None else db
    target.create_function("shop_actor", 0, lambda: ACTOR.get())
    target.create_function("shop_reason", 0, lambda: BALANCE_REASON.get())
    target.executescript(SCHEMA)
    _add_col("payments", "upd", "INTEGER DEFAULT 0", target)
    _add_col("payments", "reserved", "INTEGER DEFAULT 0", target)
    target.execute("UPDATE payments SET reserved=0 WHERE status IN ('expired','canceled')")
    _add_col("orders", "reminded", "INTEGER DEFAULT 0", target)
    _add_col("products", "pinned", "INTEGER DEFAULT 0", target)
    _add_col("products", "sort_order", "INTEGER DEFAULT 0", target)
    _add_col("products", "replace_days", f"INTEGER DEFAULT {REPLACE_DAYS}", target)
    init_shop_extensions(target)

    target.execute("DELETE FROM settings WHERE key IN ('text_ru_b_catalog','text_en_b_catalog')")
    target.execute("UPDATE products SET sort_order=id WHERE sort_order=0")
    _add_col("sections", "description", "TEXT DEFAULT ''", target)
    _add_col("users", "promo_pending", "INTEGER DEFAULT 0", target)

def _tables():
    return {r[0] for r in db.execute("SELECT name FROM sqlite_master WHERE type='table'")}


_LEGACY_DB = {"users"} <= _tables() and "payments" not in _tables()
init_db()

def q(sql, a=()): return db.execute(sql, a).fetchall()
def one(sql, a=()): return db.execute(sql, a).fetchone()
def now(): return int(time.time())
def begin():
    if db.in_transaction: db.execute("ROLLBACK")
    db.execute("BEGIN IMMEDIATE")

DEFAULTS = {
    "levels": "0:5,300:7,1000:10,3000:12", "ref_percent": "10",
    "rub_per_star": "1.7", "platega_merchant": "", "platega_secret": "",
    "platega_methods": "2,11", "replace_days": str(REPLACE_DAYS),
    "log_chat": "", "stars_enabled": "1",
}
ENV_KEYS = {"ref_percent": "REF_PERCENT", "rub_per_star": "RUB_PER_STAR", "platega_methods": "PLATEGA_METHODS",
            "replace_days": "REPLACE_DAYS", "log_chat": "SHOP_LOG_CHAT",
            "platega_merchant": "PLATEGA_MERCHANT", "platega_secret": "PLATEGA_SECRET"}
def cfg(k):

    r = one("SELECT value FROM settings WHERE key=?", (k,))
    if r and r["value"] != "": return r["value"]
    env = os.getenv(ENV_KEYS[k], "") if k in ENV_KEYS else ""
    return env if env != "" else DEFAULTS.get(k, "")
def set_cfg(k, v):
    if v in ("", None): db.execute("DELETE FROM settings WHERE key=?", (k,))
    else: db.execute("INSERT OR REPLACE INTO settings(key,value) VALUES(?,?)", (k, str(v)))

def star_rate():
    try: v = float(str(cfg("rub_per_star")).replace(",", "."))
    except ValueError: v = 1.7
    return v if math.isfinite(v) and v > 0 else 1.7

def ref_percent():
    try: return min(max(int(float(cfg("ref_percent") or 0)), 0), 100)
    except (ValueError, OverflowError): return 0

def migrate_balances():
    if cfg("balance_unit") == "rub": return
    if _LEGACY_DB:
        balance_change("Перевод старого баланса в рубли","UPDATE users SET balance=CAST(ROUND(balance*?) AS INTEGER) WHERE balance>0", (star_rate(),))
        log.warning("Балансы конвертированы из ⭐ в ₽ по курсу %s", star_rate())
    set_cfg("balance_unit", "rub")
migrate_balances()

def migrate_price_texts():
    star_after = r"(\{(?:price|v)\}(?:</?[a-zA-Z]+>)*)\s*⭐"
    rules = {
        "p_price":  [(star_after, r"\1 ₽")],
        "co_base":  [(star_after, r"\1 ₽")],
        "co_disc":  [(star_after, r"\1 ₽")],
        "co_total": [(star_after, r"\1 ₽")],
        "b_buy": {"ru": [(r"⭐\s*Купить за \{price\}(?!\s*₽)", "🛒 Купить за {price} ₽")],
                  "en": [(r"⭐\s*Buy for \{price\}(?!\s*₽)", "🛒 Buy for {price} ₽")]},
        "b_pay": {"ru": [(r"⭐\s*Оплатить \{v\}(?:\s*₽\s*звёздами)*", "⭐ Оплатить {v} ₽ звёздами")],
                  "en": [(r"⭐\s*Pay \{v\}(?:\s*₽\s*with Stars)*", "⭐ Pay {v} ₽ with Stars")]},
    }
    changed = []
    for lg in ("ru", "en"):
        for name, spec in rules.items():
            pairs = spec.get(lg, []) if isinstance(spec, dict) else spec
            key = f"text_{lg}_{name}"
            row = one("SELECT value FROM settings WHERE key=?", (key,))
            if not row or not row["value"]:
                continue
            value = row["value"]
            for pat, repl in pairs:
                value = re.sub(pat, repl, value)
            if value != row["value"]:
                set_cfg(key, value)
                changed.append(key)
    if changed:
        log.warning("Исправлены тексты цен: %s", ", ".join(changed))
    return changed

migrate_price_texts()


T = {
 "ru": {
  "welcome": "👋 Добро пожаловать!",
  "b_catalog": "🛍 Каталог", "b_search": "🔍 Поиск", "b_orders": "📦 Мои покупки",
  "b_profile": "👤 Профиль", "b_support": "🆘 Поддержка", "b_faq": "📄 Документы",
  "b_agreement": "📜 Соглашение и правила", "b_rules": "📋 Правила", "b_privacy": "🔒 Политика конфиденциальности",
  "b_lang": "🌐 English", "b_admin": "⚙️ Админ-панель", "b_back": "⬅️ Назад", "b_home": "🏠 Главное меню",
  "catalog_text": "🛍 <b>Каталог товаров</b>\n\nВыберите нужный раздел:",
  "cat_empty": "Каталог пока пуст.", "sec_pick": "Выберите товар:",
  "p_price": "💰 Цена: <b>{price} ₽</b>", "p_stock": "📦 В наличии: <b>{n}</b>",
  "p_stock_unl": "📦 Всегда в наличии", "p_none": "❌ Нет в наличии",
  "b_buy": "🛒 Купить за {price} ₽", "b_notify": "🔔 Сообщить о поступлении",
  "b_notify_off": "🔕 Не уведомлять", "nf_on": "🔔 Сообщу, когда появится!",
  "nf_off": "🔕 Отключено.", "out_stock": "Нет в наличии",
  "b_promo": "🎁 Промокод", "b_promo_rm": "❌ Убрать {code}",
  "b_usebal": "💰 Списать баланс ({bal} ₽)", "b_usebal_on": "✅ Баланс ({bal} ₽)",
  "co_balance": "\n💰 Ваш баланс: <b>{bal} ₽</b>",
  "co_need": "\n\n⚠️ Недостаточно средств. Не хватает: <b>{need} ₽</b>.\nПополните баланс и вернитесь к оформлению заказа.",
  "b_pay_bal": "💳 Оплатить с баланса — {v} ₽", "b_topup": "➕ Пополнить баланс",
  "b_pay": "⭐ Оплатить {v} ₽ звёздами", "b_free": "✅ Получить",
  "b_pay_rub": "💳 Карта/СБП — {v} ₽",
  "pm_title": "💳 <b>Способ оплаты</b>\nСумма: <b>{v} ₽</b>",
  "pay_link": "💳 К оплате: <b>{v} ₽</b>\nОплатите по кнопке — товар придёт сюда автоматически.",
  "b_open_pay": "💳 Оплатить {v} ₽", "b_chk": "🔄 Проверить оплату",
  "pay_pending": "⏳ Оплата ещё не поступила", "pay_cancel": "❌ Платёж отменён",
  "pay_err": "⚠️ Не удалось создать платёж. Попробуйте позже.",
  "pay_nostock": "⚠️ Оплата получена, но товар кончился. {v} ₽ зачислено на баланс.",
  "co_title": "🧾 <b>Оформление</b>\n\n<b>{name}</b>\n", "co_base": "Цена: {v} ₽",
  "co_disc": "Промокод <code>{code}</code>: −{v} ₽", "co_bal": "С баланса: −{v} ₽",
  "co_total": "\n<b>К оплате: {v} ₽</b>",
  "promo_ask": "🎁 Отправьте промокод:", "promo_ok": "✅ Промокод применён!",
  "promo_bad": "❌ Не найден", "promo_exp": "❌ Истёк", "promo_lim": "❌ Исчерпан",
  "promo_used": "❌ Вы уже использовали",
  "paid_head": "✅ <b>Готово!</b>\n\n", "paid_item": "<b>{name}</b>\n<code>{val}</code>\n",
  "paid_until": "\n⏳ До {d}", "paid_ins": "\n📖 <b>Инструкция:</b>\n{ins}\n",
  "paid_saved": "\nКлюч сохранён в «📦 Мои покупки».",
  "refunded_stock": "😔 Товар кончился, звёзды возвращены.",
  "rate_ask": "⭐ Оцените «{name}»:",
  "orders_title": "📦 <b>Ваши покупки:</b>\n\n", "orders_none": "Покупок пока нет.",
  "until": "до {d}", "ord_hint": "\n\n📥 — получить заново, ⚠️ — ключ не подошёл",
  "bad_sent": "✅ Заявка на замену отправлена админу. Ответ придёт сюда.",
  "bad_limit": "⚠️ Срок замены истёк или заявка уже обработана.",
  "bad_approved": "🔄 <b>Ключ заменён админом:</b>\n\n", "bad_rejected": "❌ Админ отклонил замену ключа.",
  "prof": ("👤 <b>Профиль</b>\n\n🆔 <code>{id}</code>\n💰 Баланс: <b>{bal} ₽</b>\n"
           "👥 Приглашено: <b>{refs}</b> (бонус {rp}%)\n\n"
           "🔗 Ссылка:\n<code>{link}</code>"),
  "search_ask": "🔍 Введите название:", "search_none": "Ничего не найдено.",
  "sup_text": "🆘 Напишите вопрос одним сообщением — ответ придёт сюда.",
  "tk_sent": "✅ Отправлено!", "tk_reply": "💬 <b>Ответ поддержки:</b>\n\n{text}",
  "banned": "🚫 Вы заблокированы.", "cancelled": "Отменено. /start",
  "remind": "⏰ Подписка <b>{name}</b> заканчивается {d}. Продлить?",
  "b_renew": "🔄 Продлить", "bal_added": "💰 Баланс: {v:+d} ₽",
  "ref_bonus": "🤝 Друг купил — вам +{v} ₽", "slow": "⏳ Не так быстро",
  "pm_2": "СБП", "pm_3": "ЕРИП", "pm_11": "Карта", "pm_12": "Межд. карта",
  "pm_14": "SberPay", "restock": "🔔 <b>{name}</b> снова в наличии!",
  "b_open": "Открыть",
  "faq_text": "📄 <b>Документы</b>\n\nВыберите документ, который хотите открыть.",
  "agreement_text": "📜 <b>Пользовательское соглашение и правила</b>\n\nДобавьте текст соглашения и правил магазина через админ-панель.",
  "privacy_text": "🔒 <b>Политика конфиденциальности</b>\n\nУкажите, какие данные бот получает от пользователей, для каких целей они используются, как хранятся и как связаться с владельцем магазина по вопросам обработки данных. Отредактируйте этот текст в админ-панели с учётом фактической работы вашего бота.",
  "rules_text": "📋 <b>Правила</b>\n\nДобавьте правила магазина через админ-панель.",
 },
 "en": {
  "welcome": "👋 Welcome!",
  "b_catalog": "🛍 Catalog", "b_search": "🔍 Search", "b_orders": "📦 My purchases",
  "b_profile": "👤 Profile", "b_support": "🆘 Support", "b_faq": "📄 Documents",
  "b_agreement": "📜 Agreement and rules", "b_rules": "📋 Rules", "b_privacy": "🔒 Privacy policy",
  "b_lang": "🌐 Русский", "b_admin": "⚙️ Admin panel", "b_back": "⬅️ Back", "b_home": "🏠 Main menu",
  "catalog_text": "🛍 <b>Product catalog</b>\n\nChoose a category:",
  "cat_empty": "The catalog is empty.", "sec_pick": "Choose a product:",
  "p_price": "💰 Price: <b>{price} ₽</b>", "p_stock": "📦 In stock: <b>{n}</b>",
  "p_stock_unl": "📦 Always in stock", "p_none": "❌ Out of stock",
  "b_buy": "🛒 Buy for {price} ₽", "b_notify": "🔔 Notify me",
  "b_notify_off": "🔕 Stop notifying", "nf_on": "🔔 OK, I'll notify you!",
  "nf_off": "🔕 Disabled.", "out_stock": "Out of stock",
  "b_promo": "🎁 Promo code", "b_promo_rm": "❌ Remove {code}",
  "b_usebal": "💰 Use balance ({bal} ₽)", "b_usebal_on": "✅ Balance ({bal} ₽)",
  "co_balance": "\n💰 Your balance: <b>{bal} ₽</b>",
  "co_need": "\n\n⚠️ Insufficient funds. Missing: <b>{need} ₽</b>.\nTop up your balance and return to checkout.",
  "b_pay_bal": "💳 Pay from balance — {v} ₽", "b_topup": "➕ Top up balance",
  "b_pay": "⭐ Pay {v} ₽ with Stars", "b_free": "✅ Get it",
  "b_pay_rub": "💳 Card/SBP — {v} ₽",
  "pm_title": "💳 <b>Payment method</b>\nAmount: <b>{v} ₽</b>",
  "pay_link": "💳 To pay: <b>{v} ₽</b>\nPay with the button — the item will arrive automatically.",
  "b_open_pay": "💳 Pay {v} ₽", "b_chk": "🔄 Check payment",
  "pay_pending": "⏳ Not received yet", "pay_cancel": "❌ Payment cancelled",
  "pay_err": "⚠️ Could not create the payment. Try later.",
  "pay_nostock": "⚠️ Paid, but item sold out. {v} ₽ added to your balance.",
  "co_title": "🧾 <b>Checkout</b>\n\n<b>{name}</b>\n", "co_base": "Price: {v} ₽",
  "co_disc": "Promo <code>{code}</code>: −{v} ₽", "co_bal": "From balance: −{v} ₽",
  "co_total": "\n<b>To pay: {v} ₽</b>",
  "promo_ask": "🎁 Send the promo code:", "promo_ok": "✅ Promo applied!",
  "promo_bad": "❌ Not found", "promo_exp": "❌ Expired", "promo_lim": "❌ Exhausted",
  "promo_used": "❌ Already used",
  "paid_head": "✅ <b>Done!</b>\n\n", "paid_item": "<b>{name}</b>\n<code>{val}</code>\n",
  "paid_until": "\n⏳ Until {d}", "paid_ins": "\n📖 <b>Instructions:</b>\n{ins}\n",
  "paid_saved": "\nSaved in «📦 My purchases».",
  "refunded_stock": "😔 Sold out, Stars refunded.",
  "rate_ask": "⭐ Rate «{name}»:",
  "orders_title": "📦 <b>Your purchases:</b>\n\n", "orders_none": "No purchases yet.",
  "until": "until {d}", "ord_hint": "\n\n📥 — re-deliver, ⚠️ — key doesn't work",
  "bad_sent": "✅ Replacement request sent to admin.",
  "bad_limit": "⚠️ Replacement window expired or already processed.",
  "bad_approved": "🔄 <b>Key replaced by admin:</b>\n\n", "bad_rejected": "❌ Admin rejected the replacement.",
  "prof": ("👤 <b>Profile</b>\n\n🆔 <code>{id}</code>\n💰 Balance: <b>{bal} ₽</b>\n"
           "👥 Invited: <b>{refs}</b> ({rp}% bonus)\n\n"
           "🔗 Link:\n<code>{link}</code>"),
  "search_ask": "🔍 Enter a name:", "search_none": "Nothing found.",
  "sup_text": "🆘 Describe your issue in one message — the reply will come here.",
  "tk_sent": "✅ Sent!", "tk_reply": "💬 <b>Support reply:</b>\n\n{text}",
  "banned": "🚫 You are banned.", "cancelled": "Cancelled. /start",
  "remind": "⏰ Your subscription <b>{name}</b> ends {d}. Renew?",
  "b_renew": "🔄 Renew", "bal_added": "💰 Balance: {v:+d} ₽",
  "ref_bonus": "🤝 Your friend purchased — you got +{v} ₽", "slow": "⏳ Slow down",
  "pm_2": "SBP", "pm_3": "ERIP", "pm_11": "Card", "pm_12": "Intl card",
  "pm_14": "SberPay", "restock": "🔔 <b>{name}</b> is back in stock!",
  "b_open": "Open",
  "faq_text": "📄 <b>Documents</b>\n\nChoose the document you want to open.",
  "agreement_text": "📜 <b>User agreement and rules</b>\n\nAdd the user agreement and shop rules text in the admin panel.",
  "privacy_text": "🔒 <b>Privacy policy</b>\n\nDescribe what user data the bot collects, why it is used, how it is stored, and how users can contact the shop owner about data processing. Edit this text in the admin panel to match your bot’s actual behavior.",
  "rules_text": "📋 <b>Rules</b>\n\nAdd the shop rules in the admin panel.",
 },
}


T["ru"].update({
    "bal_topup_title": "➕ <b>Пополнение баланса</b>",
    "bal_topup_desc": "Выберите способ пополнения. Баланс зачисляется в рублях. Максимум за одно пополнение — 10 000 ₽.",
    "bal_rub_button": "💳 Пополнить рублями",
    "bal_star_button": "⭐ Пополнить звёздами",
    "bal_stars_pay_button": "Оплатить {amount} ⭐",
    "bal_amount_invalid": "Отправьте целое число от 10 до {max} {unit}.",
    "bal_amount_range": "Сумма должна быть от 10 до {max} {unit}.",
    "bal_minmax": "Укажите сумму от 10 до {max} {unit}",
    "bal_amount_prompt": "✍️ Отправьте сумму пополнения от 10 до {max} {unit}. Лимит за одно пополнение — 10 000 ₽.",
    "support_contact_text": "🆘 <b>Поддержка магазина</b>\n\nПо вопросам покупки или оплаты свяжитесь с {contact}.\nНажмите «Написать в поддержку» — откроется чат поддержки в Telegram. Там опишите проблему и укажите номер заказа, если он есть.",
    "b_contact_support": "✍️ Написать в поддержку",
    "pay_limit": "⚠️ Максимальная сумма одной оплаты — 10 000 ₽.",
    "bal_platega_missing": "Пополнение через Platega не настроено.",
    "bal_choose_method": "Пополнение: <b>{amount} ₽</b>\nВыберите способ оплаты:",
    "bal_pay_button": "💳 Оплатить {amount} ₽",
    "bal_check_button": "🔎 Проверить оплату",
    "bal_pay_instructions": "💳 <b>Пополнение баланса</b>\n\nСумма: <b>{amount} ₽</b>\nПосле оплаты нажмите «Проверить оплату».",
    "ref_screen_title": "👥 <b>Реферальная программа</b>",
    "ref_invited": "Приглашено пользователей: <b>{refs}</b>",
    "ref_bonus_line": "Бонус с покупок приглашённых: <b>{percent}%</b>",
    "ref_link_label": "Твоя ссылка для приглашения:",
    "ref_screen_text": "{title}\n\n{invited}\n{bonus}\n\n{link_label}\n<code>{link}</code>",
    "pay_stars_disabled": "⭐ Оплата звёздами временно отключена. Выберите другой способ оплаты.",
    "admin_only_owner": "⛔ Только владелец может добавлять администраторов.",
    "admin_id_number": "Нужен числовой Telegram ID. Попробуйте ещё раз.",
    "admin_id_positive": "ID должен быть положительным числом.",
    "price_integer": "Цена должна быть целым числом. Попробуйте ещё раз.",
    "price_nonnegative": "Цена не может быть отрицательной.",
    "product_format": "Формат: Название | Цена в рублях | Описание",
    "text_saved": "✅ Текст сохранён.",
    "text_reset": "↩️ Стандартный текст восстановлен.",
    "photo_deleted": "🗑️ Фото удалено.",
    "text_empty": "Текст не может быть пустым. Отправьте новый текст или фото.",
})
T["en"].update({
    "bal_topup_title": "➕ <b>Top up balance</b>",
    "bal_topup_desc": "Choose a top-up method. Your balance is credited in RUB. The maximum per top-up is 10,000 RUB.",
    "bal_rub_button": "💳 Top up with RUB",
    "bal_star_button": "⭐ Top up with Stars",
    "bal_stars_pay_button": "Pay {amount} ⭐",
    "bal_amount_invalid": "Send a whole number from 10 to {max} {unit}.",
    "bal_amount_range": "Amount must be from 10 to {max} {unit}.",
    "bal_minmax": "Enter an amount from 10 to {max} {unit}",
    "bal_amount_prompt": "✍️ Send a top-up amount from 10 to {max} {unit}. The limit per top-up is 10,000 RUB.",
    "support_contact_text": "🆘 <b>Shop support</b>\n\nFor purchase or payment questions, contact {contact}.\nTap “Contact support” to open the support chat in Telegram. Describe your issue there and include your order number if available.",
    "b_contact_support": "✍️ Contact support",
    "pay_limit": "⚠️ The maximum amount per payment is 10,000 RUB.",
    "bal_platega_missing": "Top-up via Platega is not configured.",
    "bal_choose_method": "Top-up: <b>{amount} ₽</b>\nChoose a payment method:",
    "bal_pay_button": "💳 Pay {amount} ₽",
    "bal_check_button": "🔎 Check payment",
    "bal_pay_instructions": "💳 <b>Balance top-up</b>\n\nAmount: <b>{amount} ₽</b>\nAfter paying, tap “Check payment”.",
    "ref_screen_title": "👥 <b>Referral program</b>",
    "ref_invited": "Users invited: <b>{refs}</b>",
    "ref_bonus_line": "Bonus from invited users' purchases: <b>{percent}%</b>",
    "ref_link_label": "Your referral link:",
    "ref_screen_text": "{title}\n\n{invited}\n{bonus}\n\n{link_label}\n<code>{link}</code>",
    "pay_stars_disabled": "⭐ Stars payments are temporarily disabled. Choose another payment method.",
    "admin_only_owner": "⛔ Only the owner can add administrators.",
    "admin_id_number": "A numeric Telegram ID is required. Try again.",
    "admin_id_positive": "ID must be positive.",
    "price_integer": "Price must be a whole number. Try again.",
    "price_nonnegative": "Price cannot be negative.",
    "product_format": "Format: Name | Price in RUB | Description",
    "text_saved": "✅ Text saved.",
    "text_reset": "↩️ Default text restored.",
    "photo_deleted": "🗑️ Photo deleted.",
    "text_empty": "Text cannot be empty. Send new text or a photo.",
})

LANG = {}


def lang_of(uid):
    if uid not in LANG:
        r = one("SELECT lang FROM users WHERE id=?", (uid,))
        LANG[uid] = (r["lang"] if r and r["lang"] else "ru")
    return LANG[uid]

def template_vars(uid):
    user = one("SELECT id, username, name, joined, balance FROM users WHERE id=?", (uid,))
    tg_user = None
    first_name = (user["name"] if user else None) or "друг"
    username = ("@" + user["username"]) if user and user["username"] else "не указан"
    joined = user["joined"] if user else None
    today_count = one("SELECT COUNT(*) AS n FROM orders WHERE user_id=? AND refunded=0", (uid,))["n"]
    refs = one("SELECT COUNT(*) AS n FROM users WHERE ref_by=?", (uid,))["n"]
    join_date = datetime.fromtimestamp(joined).strftime("%d.%m.%Y") if joined else "не указана"
    bal = (user["balance"] or 0) if user else 0
    return {
        "FIRST_NAME": esc(first_name), "first_name": esc(first_name), "name": esc(first_name),
        "USERNAME": esc(username), "username": esc(username),
        "USER_ID": str(uid), "user_id": str(uid), "id": str(uid),
        "BALANCE": str(bal), "balance": str(bal), "bal": str(bal),
        "STATS_TODAY_PAYMENTS_COUNT": str(today_count),
        "stats_today_payments_count": str(today_count), "my_ref_count": str(refs), "refs": str(refs),
        "JOIN_DATE": esc(join_date), "join_date": esc(join_date),
    }

def t(uid, key, **kw):
    lg = lang_of(uid)
    saved = cfg(f"text_{lg}_{key}")
    s = saved if saved else (T.get(lg, {}).get(key) or T["ru"].get(key, ""))
    base = template_vars(uid)
    values = dict(base); values.update(kw)


    br = "|".join(re.escape(n) for n in sorted(values, key=len, reverse=True))
    bare = "|".join(re.escape(n) for n in sorted(base, key=len, reverse=True))
    pat = re.compile(r"\{(" + br + r")(?::([^{}]*))?\}|(?<![A-Za-z0-9_{])(" + bare + r")(?![A-Za-z0-9_}])")
    def rep_(m):
        v = values[m.group(1) or m.group(3)]
        if m.group(2):
            try: return format(v, m.group(2))
            except (ValueError, TypeError): pass
        return str(v)
    return pat.sub(rep_, s)


def is_owner(uid): return uid in ADMIN_IDS
def admin_ids(): return set(ADMIN_IDS) | {r["id"] for r in q("SELECT id FROM admins")}
def is_admin(uid): return uid in admin_ids()
def esc(s): return html.escape(str(s if s is not None else ""))
def fmt_date(ts): return datetime.fromtimestamp(ts).strftime("%d.%m.%Y")

UNL = 10**6
def stock(pid):
    p=one("SELECT delivery_type FROM products WHERE id=?",(pid,))
    if not p or p["delivery_type"] not in ("key","file"): return 0
    if p["delivery_type"]=="file":
        return one("SELECT COUNT(*) c FROM keys WHERE product_id=? AND kind LIKE 'file:%' AND sold_to IS NULL AND bad=0",(pid,))["c"]
    return one("SELECT COUNT(*) c FROM keys WHERE product_id=? AND COALESCE(kind,'text') NOT LIKE 'file:%' AND sold_to IS NULL AND bad=0",(pid,))["c"]

def stock_txt(n): return str(n)

def take_key(pid):
    p=one("SELECT delivery_type FROM products WHERE id=?",(pid,))
    if not p or p["delivery_type"] not in ("key","file"): return None
    if p["delivery_type"]=="file":
        return one("SELECT * FROM keys WHERE product_id=? AND kind LIKE 'file:%' AND sold_to IS NULL AND bad=0 ORDER BY id LIMIT 1",(pid,))
    return one("SELECT * FROM keys WHERE product_id=? AND COALESCE(kind,'text') NOT LIKE 'file:%' AND sold_to IS NULL AND bad=0 ORDER BY id LIMIT 1",(pid,))

def levels():
    out = []
    for part in (cfg("levels") or "").split(","):
        a, _, b = part.partition(":")
        if a.strip().isdigit() and b.strip().isdigit(): out.append((int(a), int(b)))
    return sorted(out) or [(0, 5)]

def spent(uid):
    return one("SELECT COALESCE(SUM(CASE WHEN value>0 THEN value ELSE stars END),0) s FROM orders "
               "WHERE COALESCE(NULLIF(payer,0),user_id)=? AND refunded=0", (uid,))["s"]

def level_info(uid):
    lv = levels(); s_ = spent(uid); idx = 0
    for i, (th, _) in enumerate(lv):
        if s_ >= th: idx = i
    return idx, lv[idx][1], s_

def balance(uid):
    r = one("SELECT balance FROM users WHERE id=?", (uid,))
    return (r["balance"] or 0) if r else 0

def uname(uid):
    r = one("SELECT username, name FROM users WHERE id=?", (uid,))
    if r and r["username"]: return "@" + r["username"]
    return (r["name"] if r and r["name"] else str(uid))

def eff_price(p): return p["price"]

def rating(pid):
    r = one("SELECT AVG(stars) a, COUNT(*) n FROM reviews WHERE product_id=?", (pid,))
    return (round(r["a"], 1), r["n"]) if r["n"] else (0, 0)

CAP = 1024

def pic(uid, key):
    language = lang_of(uid)
    aliases = {"faq_text": "b_faq"}
    candidates = [f"photo_{language}_{key}", f"photo_ru_{key}"]
    old_key = aliases.get(key)
    if old_key:
        candidates.extend((f"photo_{language}_{old_key}", f"photo_ru_{old_key}"))
    return next((value for name in candidates if (value := cfg(name))), None)

class _PlainTelegramHTML(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts = []
    def handle_data(self, data): self.parts.append(data)
    def handle_starttag(self, tag, attrs):
        if tag == "br": self.parts.append("\n")

def message_chunks(text, limit=4096):
    raw = text.encode("utf-16-le")
    while raw:
        end = min(len(raw), limit * 2)
        if end < len(raw) and 0xD800 <= int.from_bytes(raw[end-2:end], "little") <= 0xDBFF:
            end -= 2
        yield raw[:end].decode("utf-16-le")
        raw = raw[end:]

async def _send_text(ctx, chat_id, text, markup=None):
    if len(text.encode("utf-16-le")) > 8192:
        parser = _PlainTelegramHTML(); parser.feed(text); parser.close()
        chunks = list(message_chunks("".join(parser.parts) or text))
        result = None
        for i, chunk in enumerate(chunks):
            result = await ctx.bot.send_message(chat_id, chunk, reply_markup=markup if i == len(chunks)-1 else None)
        return result
    for mode in ("HTML", None):
        try: return await ctx.bot.send_message(chat_id, text, reply_markup=markup, parse_mode=mode)
        except BadRequest: pass
    raise TelegramError("send failed")

async def send(ctx, chat_id, text, markup=None, photo=None):
    text = text or "—"
    if photo:
        if len(text) > CAP:

            try:
                await ctx.bot.send_photo(chat_id, photo)
                return await _send_text(ctx, chat_id, text, markup)
            except BadRequest: pass
        else:
            for mode in ("HTML", None):
                try: return await ctx.bot.send_photo(chat_id, photo, caption=text, reply_markup=markup, parse_mode=mode)
                except BadRequest: pass

    return await _send_text(ctx, chat_id, text, markup)

async def _strip_markup(m):
    try: await m.edit_reply_markup(reply_markup=None)
    except TelegramError: pass

async def show(update, ctx, text, rows=None, photo=None):
    markup = Markup(rows) if rows else None
    text = text or "—"
    c = update.callback_query
    if c:
        try: await c.answer()
        except TelegramError: pass
    if len(text.encode("utf-16-le")) > 8192:
        if c and c.message: await _strip_markup(c.message)
        return await send(ctx, update.effective_chat.id, text, markup, photo)
    if c and c.message:
        m = c.message
        if m.photo and photo and len(text) <= CAP:

            for mode in ("HTML", None):
                try:
                    await m.edit_media(InputMediaPhoto(photo, caption=text, parse_mode=mode), reply_markup=markup)
                    return m
                except BadRequest as e:
                    if "not modified" in str(e).lower(): return m
                except TelegramError: break
        if m.photo or photo:

            await _strip_markup(m)
            return await send(ctx, m.chat_id, text, markup, photo)
        try:
            await m.edit_text(text, reply_markup=markup, parse_mode="HTML")
        except BadRequest as e:
            if "not modified" in str(e).lower(): return m
            try: await m.edit_text(text, reply_markup=markup)
            except TelegramError:
                await _strip_markup(m)
                return await send(ctx, m.chat_id, text, markup, photo)
        except TelegramError:
            await _strip_markup(m)
            return await send(ctx, m.chat_id, text, markup, photo)
    else:
        await send(ctx, update.effective_chat.id, text, markup, photo)

async def alert(update, text):
    try: await update.callback_query.answer(text, show_alert=True)
    except TelegramError: pass

async def notify(ctx, ids, text, markup=None):
    for i in ids:
        try: await ctx.bot.send_message(i, text, parse_mode="HTML", reply_markup=markup)
        except TelegramError: pass


RATE = {}
def too_fast(uid):
    t0 = time.time(); ts = [x for x in RATE.get(uid, []) if t0 - x < 5]; ts.append(t0); RATE[uid] = ts
    return len(ts) > 10

async def guard(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    u = update.effective_user
    if not u: return
    paying = bool(update.pre_checkout_query or (update.message and update.message.successful_payment))
    if not paying and not is_admin(u.id) and too_fast(u.id):
        if update.callback_query: await alert(update, t(u.id, "slow"))
        raise ApplicationHandlerStop
    r = one("SELECT banned FROM users WHERE id=?", (u.id,))
    if r is None:
        ref = None; m = update.message
        if m and m.text and m.text.startswith("/start ref_"):
            tail = m.text.split("ref_", 1)[1].strip()
            if tail.isdigit() and int(tail) != u.id and one("SELECT 1 FROM users WHERE id=?", (int(tail),)):
                ref = int(tail)
        code = (u.language_code or "ru")[:2]
        lg = "ru" if code in ("ru", "uk", "be", "kk") else "en"
        db.execute("INSERT INTO users(id,username,name,joined,lang,ref_by) VALUES(?,?,?,?,?,?)",
                   (u.id, u.username, u.full_name, now(), lg, ref))
        LANG[u.id] = lg
    else:
        db.execute("UPDATE users SET username=?, name=? WHERE id=?", (u.username, u.full_name, u.id))
        if r["banned"] and not is_admin(u.id):
            if update.pre_checkout_query:
                await update.pre_checkout_query.answer(ok=False, error_message="Banned"); raise ApplicationHandlerStop
            if paying: return
            if update.callback_query: await alert(update, t(u.id, "banned"))
            elif update.effective_message: await update.effective_message.reply_text(t(u.id, "banned"))
            raise ApplicationHandlerStop

def home_rows(uid):
    rows = [
        [Btn(t(uid, "b_catalog"), callback_data="cat"),
         Btn(t(uid, "b_search"), callback_data="search")],
        [Btn(t(uid, "b_profile"), callback_data="prof"),
         Btn(t(uid, "b_support"), callback_data="sup")],
        [Btn(t(uid, "b_faq"), callback_data="faq"),
         Btn(t(uid, "b_lang"), callback_data="lang")],
    ]
    if is_admin(uid): rows.append([Btn(t(uid, "b_admin"), callback_data="adm")])
    return rows


def back_row(uid, cb="home"): return [Btn(t(uid, "b_back"), callback_data=cb, style="primary")]

async def send_home(update, ctx):
    user = update.effective_user
    uid = user.id
    welcome_text = t(
        uid, "welcome",
        name=esc(user.first_name or user.full_name or "друг"),
        username=esc("@" + user.username if user.username else "не указан"),
        user_id=uid,
        id=uid,
    )
    await show(update, ctx, welcome_text, home_rows(uid), photo=pic(uid, "welcome"))

async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    ctx.user_data.clear(); uid = update.effective_user.id
    await send_home(update, ctx)

async def cancel(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    ctx.user_data.clear()
    await update.message.reply_text(t(update.effective_user.id, "cancelled"))

async def fixtexts(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    if not is_owner(uid):
        return await update.message.reply_text("Только для владельца.")
    changed = migrate_price_texts()
    if changed:
        await update.message.reply_text("✅ Исправлено текстов: %d\n%s" % (len(changed), "\n".join(changed)))
    else:
        await update.message.reply_text("✅ Все тексты цен уже в порядке, менять нечего.")

async def catalog(update, ctx):
    uid = update.effective_user.id
    secs = q("SELECT * FROM sections ORDER BY id")
    if not secs:
        return await show(update, ctx, t(uid, "cat_empty"), [back_row(uid)],
                          photo=pic(uid, "cat_empty") or pic(uid, "catalog_text"))
    rows = [[Btn(s["name"], callback_data=f"sec:{s['id']}")] for s in secs] + [back_row(uid)]
    await show(update, ctx, t(uid, "catalog_text"), rows,
               photo=pic(uid, "catalog_text"))

async def section(update, ctx, sid):
    uid = update.effective_user.id
    s = one("SELECT * FROM sections WHERE id=?", (sid,))
    if not s: return await catalog(update, ctx)
    prods = q("SELECT * FROM products WHERE section_id=? AND delivery_type IN ('key','file') ORDER BY pinned DESC, sort_order ASC, id DESC", (sid,))
    rows = [[Btn(f"{p['name']} — {rub_amount(p, p['price'])} ₽ ({stock_txt(stock(p['id']))})"[:60], callback_data=f"prod:{p['id']}")]
            for p in prods] + [back_row(uid, "cat")]
    await show(update, ctx, f"<b>{esc(s['name'])}</b>\n\n{esc(s['description'] or '')}\n\n{t(uid, 'sec_pick')}", rows, photo=s["photo"])

async def product(update, ctx, pid):
    uid = update.effective_user.id
    p = one("SELECT * FROM products WHERE id=?", (pid,))
    if not p or p["delivery_type"] not in DELIVERY_TYPES: return await catalog(update, ctx)
    n = stock(pid)
    text = f"<b>{esc(p['name'])}</b>\n\n{esc(p['description'])}\n\n{t(uid, 'p_price', price=rub_amount(p, p['price']))}\n"
    text += t(uid, "p_stock_unl") if n >= UNL else t(uid, "p_stock", n=n)
    avg, rn = rating(pid)
    if rn: text += f"\n⭐ {avg} ({rn})"
    if p["duration"]: text += f"\n⏳ {p['duration']} дн."
    rows = []
    if n > 0:
        rows.append([Btn(t(uid, "b_buy", price=rub_amount(p, p["price"])), callback_data=f"co:{pid}")])
    else:
        text += "\n\n" + t(uid, "p_none")
        sub = one("SELECT 1 FROM restock_subs WHERE user_id=? AND product_id=?", (uid, pid))
        rows.append([Btn(t(uid, "b_notify_off" if sub else "b_notify"), callback_data=f"nf:{pid}")])
    rows.append([Btn("❤️ Избранное", callback_data=f"ext:favorite:{pid}")])
    rows.append([Btn(t(uid, "b_back"), callback_data=f"sec:{p['section_id']}"),
                  Btn(t(uid, "b_home"), callback_data="home")])
    await show(update, ctx, text, rows, photo=p["photo"])

async def toggle_notify(update, pid):
    uid = update.effective_user.id
    p = one("SELECT id FROM products WHERE id=?", (pid,))
    if not p:
        return await alert(update, "Товар не найден")
    sub = one("SELECT 1 FROM restock_subs WHERE user_id=? AND product_id=?", (uid, pid))
    if sub:
        db.execute("DELETE FROM restock_subs WHERE user_id=? AND product_id=?", (uid, pid))
        return await alert(update, t(uid, "nf_off"))
    db.execute("INSERT OR IGNORE INTO restock_subs(user_id,product_id) VALUES(?,?)", (uid, pid))
    return await alert(update, t(uid, "nf_on"))


def promo_get(code, uid):
    p = one("SELECT * FROM promos WHERE code=? AND active=1", (code.strip().upper(),))
    if not p or (p["owner"] and p["owner"] != uid): return None, "promo_bad"
    if p["expires"] and p["expires"] < now(): return None, "promo_exp"
    if one("SELECT 1 FROM promo_uses WHERE promo_id=? AND user_id=?", (p["id"], uid)): return None, "promo_used"
    if p["max_uses"] and p["used"] >= p["max_uses"]: return None, "promo_lim"
    return p, None

def promo_disc(base, promo):
    if not promo or promo["kind"] not in ("p", "s"): return 0
    d = base * promo["value"] // 100 if promo["kind"] == "p" else promo["value"]
    return max(0, min(d, base))

def order_total_rub(p, promo):
    base = p["price"]
    if promo and promo["kind"] == "r":
        base_rub = rub_amount(p, base) if base > 0 else 0
        return max(base_rub - promo["value"], 0)
    price = max(base - promo_disc(base, promo), 0)
    return rub_amount(p, price) if price > 0 else 0

def promo_label(p):
    k, v = p["kind"], p["value"]
    if k == "p": return f"−{v}%"
    if k == "r": return f"−{v} ₽"
    if k == "b": return f"+{v} ₽ на баланс"
    return f"−{v}⭐ (экв.)"

def promo_valid(p):
    return bool(p["active"]) and not (p["expires"] and p["expires"] < now()) \
        and not (p["max_uses"] and p["used"] >= p["max_uses"])

def redeem_balance_promo(uid, p):
    begin()
    try:
        cur = db.execute("UPDATE promos SET used=used+1 WHERE id=? AND active=1 AND (max_uses=0 OR used<max_uses) "
                         "AND (expires=0 OR expires>?)", (p["id"], now()))
        if cur.rowcount != 1:
            db.execute("ROLLBACK"); return "promo_lim"
        cur = db.execute("INSERT OR IGNORE INTO promo_uses(promo_id,user_id) VALUES(?,?)", (p["id"], uid))
        if cur.rowcount != 1:
            db.execute("ROLLBACK"); return "promo_used"
        balance_change("Бонус по промокоду","UPDATE users SET balance=balance+? WHERE id=?", (p["value"], uid))
        db.execute("COMMIT")
        return None
    except Exception:
        if db.in_transaction: db.execute("ROLLBACK")
        raise

def activate_promo(uid, code):
    ru = lang_of(uid) == "ru"
    p, err = promo_get(code, uid)
    if err: return t(uid, err), False
    if p["kind"] == "b":
        err = redeem_balance_promo(uid, p)
        if err: return t(uid, err), False
        return ((f"✅ Промокод активирован! На баланс зачислено <b>{p['value']} ₽</b>.\nТекущий баланс: <b>{balance(uid)} ₽</b>") if ru else
                (f"✅ Promo code activated! <b>{p['value']} ₽</b> added to your balance.\nCurrent balance: <b>{balance(uid)} ₽</b>")), True
    db.execute("UPDATE users SET promo_pending=? WHERE id=?", (p["id"], uid))
    return ((f"✅ Промокод <b>{esc(p['code'])}</b> активирован: <b>{promo_label(p)}</b>.\nСкидка применится автоматически при следующей покупке.") if ru else
            (f"✅ Promo code <b>{esc(p['code'])}</b> activated: <b>{promo_label(p)}</b>.\nThe discount will apply automatically to your next purchase.")), True

def calc(uid, p, promo, use_bal):

    base = p["price"]
    disc = promo_disc(base, promo)
    price = max(base - disc, 0)
    total_rub = order_total_rub(p, promo)
    used = min(balance(uid), total_rub) if use_bal else 0
    remaining_rub = max(total_rub - used, 0)
    final = math.ceil(remaining_rub / star_rate() - 1e-9) if remaining_rub else 0
    return base, disc, price, used, final

def calc_rub(uid, p, promo, use_bal):
    total = order_total_rub(p, promo)
    used = min(balance(uid), total) if use_bal else 0
    return total, used, max(total - used, 0)


async def checkout_start(update, ctx, pid):
    uid = update.effective_user.id
    p = one("SELECT * FROM products WHERE id=?", (pid,))
    if not p or stock(pid) == 0: return await alert(update, t(uid, "out_stock"))
    promo_id = None
    pend = one("SELECT promo_pending FROM users WHERE id=?", (uid,))
    if pend and pend["promo_pending"]:
        pr = one("SELECT * FROM promos WHERE id=?", (pend["promo_pending"],))
        ok_p, err = promo_get(pr["code"], uid) if pr else (None, "promo_bad")
        if ok_p and ok_p["kind"] != "b": promo_id = ok_p["id"]
        else: db.execute("UPDATE users SET promo_pending=0 WHERE id=?", (uid,))
    ctx.user_data["co"] = {"pid": pid, "promo": promo_id, "bal": True}
    await render_checkout(update, ctx)

def get_co(ctx):
    co = ctx.user_data.get("co")
    p = co and one("SELECT * FROM products WHERE id=?", (co["pid"],))
    return (co, p) if p else (None, None)

def checkout_promo(co, uid):
    promo_id = co.get("promo")
    if not promo_id: return None, None
    candidate = one("SELECT * FROM promos WHERE id=?", (promo_id,))
    promo, err = promo_get(candidate["code"], uid) if candidate else (None, "promo_bad")
    if err:
        co["promo"] = None
        db.execute("UPDATE users SET promo_pending=0 WHERE id=? AND promo_pending=?", (uid, promo_id))
    return promo, err

async def render_checkout(update, ctx):
    uid = update.effective_user.id
    co, p = get_co(ctx)
    if not p: return await catalog(update, ctx)
    promo, _ = checkout_promo(co, uid)

    base, disc, price, used, final = calc(uid, p, promo, True)
    total = order_total_rub(p, promo)
    base_rub = rub_amount(p, base) if base > 0 else 0
    bal = balance(uid)
    need = max(total - bal, 0)
    text = t(uid, "co_title", name=esc(p["name"])) + t(uid, "co_base", v=base_rub)
    if promo and base_rub - total > 0:
        text += "\n" + t(uid, "co_disc", code=esc(promo["code"]), v=base_rub - total)
    text += t(uid, "co_total", v=total)
    text += t(uid, "co_balance", bal=bal)
    rows = [[Btn(t(uid, "b_promo_rm", code=promo["code"]), callback_data="cop_rm") if promo
             else Btn(t(uid, "b_promo"), callback_data="cop")]]
    if total > MAX_PAYMENT_RUB:
        text += "\n\n" + t(uid, "pay_limit")
    elif need > 0:
        text += t(uid, "co_need", need=need, bal=bal)
        rows.append([Btn(t(uid, "b_topup"), callback_data="bal_topup")])
    else:
        rows.append([Btn(t(uid, "b_pay_bal", v=total) if total else t(uid, "b_free"), callback_data="pay")])

    if 0 < total <= MAX_PAYMENT_RUB and platega_ready():
        rows.append([Btn(t(uid, "b_pay_rub", v=total), callback_data="payrub")])
    rows.append([Btn(t(uid, "b_back"), callback_data=f"prod:{p['id']}"),
                  Btn(t(uid, "b_home"), callback_data="home")])
    await show(update, ctx, text, rows, photo=pic(uid, "co_title"))

async def pay(update, ctx):
    uid = update.effective_user.id
    co, p = get_co(ctx)
    if not p: return await catalog(update, ctx)
    promo, err = checkout_promo(co, uid)
    if err:
        await alert(update, t(uid, err))
        return await render_checkout(update, ctx)
    if order_total_rub(p, promo) > MAX_PAYMENT_RUB:
        return await alert(update, t(uid, "pay_limit"))
    base, disc, price, used, final = calc(uid, p, promo, True)
    if stock(p["id"]) == 0: return await alert(update, t(uid, "out_stock"))
    if final > 0:

        return await render_checkout(update, ctx)
    promo_id = promo["id"] if promo else 0
    total = order_total_rub(p, promo)
    unit = rub_unit(p) or star_rate()
    value = max(1, round(total / unit)) if total > 0 else 0
    ok = await process_order(ctx, uid, uid, p["id"], promo_id, used, value, 0, total, "balance", "")
    if ok:
        await _strip_markup(update.callback_query.message)
        ctx.user_data.pop("co", None)
    else: await alert(update, t(uid, "out_stock"))


PLATEGA_URL = "https://app.platega.io"
PM_IDS = (2, 3, 11, 12, 14)
PL_BAD = ("CANCELED", "CANCELLED", "EXPIRED", "FAILED", "CHARGEBACKED")
PENDING_TTL = 24 * 3600
STUCK_AFTER = 300

def pl_cred():
    return (cfg("platega_merchant") or os.getenv("PLATEGA_MERCHANT", ""),
            cfg("platega_secret") or os.getenv("PLATEGA_SECRET", ""))
def platega_ready():
    m, s = pl_cred(); return bool(m and s)
def pl_methods():
    ids = [int(x) for x in (cfg("platega_methods") or "").split(",") if x.strip().isdigit() and int(x) in PM_IDS]
    return ids or [2, 11]
def rub_unit(p):
    if p["price_rub"] and p["price"]: return p["price_rub"] / p["price"]
    return star_rate()
def rub_amount(p, final): return 0 if final <= 0 else max(math.ceil(final * rub_unit(p) - 1e-9), 1)

async def platega_post(body):
    m, s = pl_cred()
    async with httpx.AsyncClient(timeout=20) as c:
        r = await c.post(PLATEGA_URL + "/transaction/process", json=body,
                         headers={"X-MerchantId": m, "X-Secret": s, "Content-Type": "application/json"})
        r.raise_for_status(); return r.json()

async def platega_get(tid):
    m, s = pl_cred()
    async with httpx.AsyncClient(timeout=20) as c:
        r = await c.get(f"{PLATEGA_URL}/transaction/{tid}", headers={"X-MerchantId": m, "X-Secret": s})
        r.raise_for_status(); return r.json()

async def create_platega_order(update, ctx, method=None):
    uid = update.effective_user.id
    co, p = get_co(ctx)
    if not p: return await catalog(update, ctx)
    promo, err = checkout_promo(co, uid)
    if err:
        await alert(update, t(uid, err))
        return await render_checkout(update, ctx)
    total = order_total_rub(p, promo)
    if total <= 0:
        return await pay(update, ctx)
    if total > MAX_PAYMENT_RUB:
        return await alert(update, t(uid, "pay_limit"))
    if stock(p["id"]) == 0:
        return await alert(update, t(uid, "out_stock"))
    if not platega_ready():
        return await alert(update, t(uid, "pay_err"))
    methods = pl_methods()
    if not methods or (method is not None and method not in methods):
        return await alert(update, t(uid, "pay_err"))
    if method is None and len(methods) > 1:
        rows = [[Btn(t(uid, f"pm_{m}"), callback_data=f"pay_pm:{m}")] for m in methods]
        rows.append(back_row(uid, "co_back"))
        return await show(update, ctx, t(uid, "pm_title", v=total), rows, photo=pic(uid, "co_title"))
    method = method if method is not None else methods[0]
    if method not in PM_IDS:
        return await alert(update, t(uid, "pay_err"))

    bal_used = min(balance(uid), total)
    remaining = total - bal_used
    if remaining <= 0:
        return await pay(update, ctx)
    tid = None
    balance_reserved = False
    try:
        begin()
        cur = balance_change("Резерв на оплату","UPDATE users SET balance=balance-? WHERE id=? AND balance>=?", (bal_used, uid, bal_used))
        if cur.rowcount != 1:
            db.execute("ROLLBACK")
            return await render_checkout(update, ctx)
        db.execute("COMMIT")
        balance_reserved = True
        back_url = f"https://t.me/{ctx.bot.username}"
        body = {
            "paymentMethod": method,
            "paymentDetails": {"amount": remaining, "currency": "RUB"},
            "description": f"Оплата заказа {p['name']}"[:100],
            "return": back_url,
            "failedUrl": back_url,
            "payload": f"order:{uid}:{p['id']}",
            "metadata": {"userId": str(uid), "userName": f"@{update.effective_user.username}" if update.effective_user.username else str(uid)},
        }
        data = await platega_post(body)
        tid = data.get("transactionId")
        url = data.get("redirect") or data.get("url")
        if not tid or not url:
            raise ValueError(data)
        db.execute("INSERT INTO payments(id,payer,owner,pid,promo_id,bal_used,final,rub,method,ts,reserved) VALUES(?,?,?,?,?,?,?,?,?,?,1)",
                   (tid, uid, uid, p["id"], promo["id"] if promo else 0, bal_used, remaining, remaining, method, now()))
    except Exception as e:

        if db.in_transaction: db.execute("ROLLBACK")
        if balance_reserved:
            balance_change("Возврат резерва","UPDATE users SET balance=balance+? WHERE id=?", (bal_used, uid))
        log.error("platega order create: %s", e)
        return await alert(update, t(uid, "pay_err"))
    rows = [[Btn(t(uid, "b_open_pay", v=remaining), url=url)],
            [Btn(t(uid, "b_chk"), callback_data=f"chk:{tid}")],
            [back_row(uid, "co_back")[0]]]
    await show(update, ctx, t(uid, "pay_link", v=remaining), rows, photo=pic(uid, "co_title"))

async def pay_rub(update, ctx):
    return await create_platega_order(update, ctx)

def release_pending(tid, new_status):
    begin()
    try:
        cur = db.execute("UPDATE payments SET status=?, upd=? WHERE id=? AND status='pending'", (new_status, now(), tid))
        row = None
        if cur.rowcount == 1:
            row = one("SELECT * FROM payments WHERE id=?", (tid,))
            if row["reserved"] and row["bal_used"]:
                balance_change("Возврат резерва","UPDATE users SET balance=balance+? WHERE id=?", (row["bal_used"], row["payer"]))
            db.execute("UPDATE payments SET reserved=0 WHERE id=?", (tid,))
        db.execute("COMMIT")
        return row
    except Exception:
        if db.in_transaction: db.execute("ROLLBACK")
        raise

async def settle_payment(ctx, tid, late=False):
    pay_ = one("SELECT * FROM payments WHERE id=?", (tid,))
    payer = pay_["payer"]
    try:
        if pay_["pid"] == 0 or late:
            credit = pay_["rub"] + (pay_["bal_used"] if pay_["reserved"] else 0)
            begin()
            try:
                balance_change("Пополнение / поздний платёж","UPDATE users SET balance=balance+? WHERE id=?", (credit, payer))
                db.execute("UPDATE payments SET status=?, upd=? WHERE id=?",
                           ("done" if pay_["pid"] == 0 else "late", now(), tid))
                db.execute("COMMIT")
            except Exception:
                if db.in_transaction: db.execute("ROLLBACK")
                raise
            if pay_["pid"] == 0:
                await notify(ctx, [payer],
                             f"✅ Баланс пополнен на <b>{credit} ₽</b>. Текущий баланс: <b>{balance(payer)} ₽</b>")
                return "done"
            await notify(ctx, [payer], f"⚠️ Оплата пришла после истечения времени заказа. "
                                       f"<b>{credit} ₽</b> зачислено на баланс — оформите покупку заново.")
            return "late"
        prepaid = bool(pay_["reserved"])
        ok = await process_order(ctx, payer, pay_["owner"], pay_["pid"], pay_["promo_id"], pay_["bal_used"],
                                 pay_["final"], 0, pay_["rub"], "platega", tid, prepaid=prepaid)
        if ok:
            db.execute("UPDATE payments SET status='done', upd=? WHERE id=?", (now(), tid))
            return "done"

        refund = pay_["rub"] + (pay_["bal_used"] if prepaid else 0)
        begin()
        try:
            balance_change("Возврат за недоступный товар","UPDATE users SET balance=balance+? WHERE id=?", (refund, payer))
            db.execute("UPDATE payments SET status='nostock', upd=? WHERE id=?", (now(), tid))
            db.execute("COMMIT")
        except Exception:
            if db.in_transaction: db.execute("ROLLBACK")
            raise
        await notify(ctx, [payer], t(payer, "pay_nostock", v=refund))
        return "nostock"
    except Exception:
        log.exception("settle_payment %s", tid)
        if one("SELECT 1 FROM orders WHERE charge_id=?", (tid,)):
            db.execute("UPDATE payments SET status='done', upd=? WHERE id=?", (now(), tid)); return "done"
        db.execute("UPDATE payments SET status='pending', upd=? WHERE id=? AND status='processing'", (now(), tid))
        return "pending"

async def check_payment(ctx, tid):
    pay_ = one("SELECT * FROM payments WHERE id=?", (tid,))
    if not pay_: return "none"
    cur_st = pay_["status"]
    if cur_st not in ("pending", "expired"): return cur_st
    try: data = await platega_get(tid)
    except Exception as e:
        log.warning("platega status: %s", e); return cur_st
    st = str(data.get("status", "")).upper()
    if st == "CONFIRMED":
        cur = db.execute("UPDATE payments SET status='processing', upd=? WHERE id=? AND status=?", (now(), tid, cur_st))
        if cur.rowcount != 1: return "processing"
        return await settle_payment(ctx, tid, late=(cur_st == "expired"))
    if st in PL_BAD:
        if cur_st == "pending":
            row = release_pending(tid, "canceled")
            if row: await notify(ctx, [row["payer"]], t(row["payer"], "pay_cancel"))
        return "canceled"
    if cur_st == "pending" and now() - pay_["ts"] > PENDING_TTL:
        row = release_pending(tid, "expired")
        if row: await notify(ctx, [row["payer"]], t(row["payer"], "pay_cancel"))
        return "expired"
    return cur_st

async def chk_payment(update, ctx, tid):
    uid = update.effective_user.id
    row = one("SELECT payer FROM payments WHERE id=?", (tid,))
    if row and row["payer"] != uid and not is_admin(uid): return await alert(update, "⛔")
    st = await check_payment(ctx, tid)
    if st in ("pending", "processing"): return await alert(update, t(uid, "pay_pending"))
    if st in ("canceled", "expired"): return await alert(update, t(uid, "pay_cancel"))
    if st in ("done", "nostock", "late"):
        await _strip_markup(update.callback_query.message)
    try: await update.callback_query.answer()
    except TelegramError: pass


def recover_stuck():
    for r in q("SELECT id FROM payments WHERE status='processing' AND upd<?", (now() - STUCK_AFTER,)):
        if one("SELECT 1 FROM orders WHERE charge_id=?", (r["id"],)):
            db.execute("UPDATE payments SET status='done', upd=? WHERE id=?", (now(), r["id"]))
        else:
            log.warning("payment %s was stuck in processing, retrying", r["id"])
            db.execute("UPDATE payments SET status='pending', upd=? WHERE id=?", (now(), r["id"]))

async def poll_payments(app, cycle):
    recover_stuck()
    if not platega_ready(): return
    rows = list(q("SELECT id FROM payments WHERE status='pending' ORDER BY ts LIMIT 100"))
    if cycle % 20 == 0:
        rows += list(q("SELECT id FROM payments WHERE status='expired' AND ts>? LIMIT 50", (now() - 3 * 86400,)))
    for r in rows:
        try: await check_payment(app, r["id"])
        except Exception: log.exception("poll payment %s", r["id"])
        await asyncio.sleep(0.3)

async def send_reminders(app):
    ts = now()
    for o in q("SELECT * FROM orders WHERE expires>? AND expires<=? AND reminded=0 AND refunded=0",
               (ts, ts + 3 * 86400)):
        uid = o["user_id"]
        db.execute("UPDATE orders SET reminded=1 WHERE id=?", (o["id"],))
        try:
            await notify(app, [uid], t(uid, "remind", name=esc(o["product_name"]), d=fmt_date(o["expires"])),
                         Markup([[Btn(t(uid, "b_renew"), callback_data=f"prod:{o['product_id']}")]]))
        except Exception: log.exception("reminder %s", o["id"])
        await asyncio.sleep(0.05)

async def bg_loop(app):
    await asyncio.sleep(10)
    cycle = 0
    while True:
        cycle += 1
        try:
            await poll_payments(app, cycle)
            if cycle % 20 == 1: await send_reminders(app)
        except asyncio.CancelledError: raise
        except Exception: log.exception("background loop")
        await asyncio.sleep(30)


def fulfill(payer, owner, pid, promo_id, bal_used, value, stars, rub, method, charge_id, prepaid=False):
    begin()
    try:
        p = one("SELECT * FROM products WHERE id=?", (pid,))
        u = one("SELECT * FROM users WHERE id=?", (payer,))
        if not p or not u or (not prepaid and (u["balance"] or 0) < bal_used):
            db.execute("ROLLBACK"); return None
        if method == "balance" and promo_id:
            promo = one("SELECT code FROM promos WHERE id=?", (promo_id,))
            if not promo or promo_get(promo["code"], payer)[1]:
                db.execute("ROLLBACK"); return None
        ts = now(); picked = []
        k = take_key(pid)
        if not k: db.execute("ROLLBACK"); return None
        db.execute("UPDATE keys SET sold_to=?, sold_at=? WHERE id=?", (owner, ts, k["id"]))
        picked.append(k)
        if bal_used and not prepaid: balance_change("Оплата заказа","UPDATE users SET balance=balance-? WHERE id=?", (bal_used, payer))
        if promo_id:
            db.execute("INSERT OR IGNORE INTO promo_uses(promo_id,user_id) VALUES(?,?)", (promo_id, payer))
            db.execute("UPDATE promos SET used=used+1 WHERE id=?", (promo_id,))
            db.execute("UPDATE users SET promo_pending=0 WHERE id=? AND promo_pending=?", (payer, promo_id))

        paid_rub = rub if rub else int(stars * star_rate())
        cashback = 0
        ref_to = u["ref_by"] or 0
        ref_bonus = paid_rub * ref_percent() // 100 if ref_to else 0
        if ref_bonus: balance_change("Реферальный бонус","UPDATE users SET balance=balance+? WHERE id=?", (ref_bonus, ref_to))
        expires = ts + p["duration"] * 86400 if p["duration"] else 0
        cur = db.execute(
            "INSERT INTO orders(user_id,payer,product_id,product_name,key_value,stars,rub,value,bal_used,"
            "promo_id,charge_id,ts,expires,cashback,ref_bonus,ref_to,method) "
            "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
            (owner, payer, pid, p["name"], k["value"], stars, rub, value, bal_used, promo_id, charge_id,
             ts, expires, cashback, ref_bonus, ref_to, method))
        oid = cur.lastrowid
        if k["id"] is not None:
            db.execute("INSERT INTO order_keys(order_id,key_id) VALUES(?,?)", (oid, k["id"]))
        db.execute("COMMIT")
        return one("SELECT * FROM orders WHERE id=?", (oid,))
    except Exception:
        if db.in_transaction: db.execute("ROLLBACK")
        raise

async def deliver_order(ctx, chat_id, o, head=None):
    items = q("SELECT k.*, p.name pname FROM order_keys ok JOIN keys k ON k.id=ok.key_id "
              "JOIN products p ON p.id=k.product_id WHERE ok.order_id=?", (o["id"],))
    text = head or t(chat_id, "paid_head")
    if items:
        for k in items: text += t(chat_id, "paid_item", name=esc(k["pname"]), val=esc(k["value"]))
    else: text += t(chat_id, "paid_item", name=esc(o["product_name"]), val=esc(o["key_value"]))
    if o["expires"]: text += t(chat_id, "paid_until", d=fmt_date(o["expires"]))
    p = one("SELECT instruction FROM products WHERE id=?", (o["product_id"],))
    if p and p["instruction"]: text += t(chat_id, "paid_ins", ins=esc(p["instruction"]))
    text += t(chat_id, "paid_saved")
    if len(text.encode("utf-16-le")) > 8192:
        values = [k["value"] for k in items] if items else [o["key_value"]]
        data = io.BytesIO("\n\n".join(values).encode("utf-8"))
        filename = f"order_{o['id']}.txt"
        data.name = filename
        await ctx.bot.send_document(chat_id=chat_id, document=data, filename=filename,
                                    caption=f"📦 #{o['id']} — {o['product_name']}"[:1024])
        return await send(ctx, chat_id, t(chat_id, "paid_saved"))
    await send(ctx, chat_id, text, photo=pic(chat_id, "paid_head"))

async def process_order(ctx, payer, owner, pid, promo_id, bal_used, value, stars, rub, method, charge_id, prepaid=False):
    o = fulfill(payer, owner, pid, promo_id, bal_used, value, stars, rub, method, charge_id, prepaid)
    if not o: return False


    try:
        await deliver_order(ctx, owner, o)
    except Exception:
        log.exception("deliver_order failed for order %s", o["id"])
    try:
        stars_row = [Btn(f"{i}⭐", callback_data=f"rate:{o['id']}:{i}") for i in range(1, 6)]
        await send(ctx, owner, t(owner, "rate_ask", name=esc(o["product_name"])), Markup([stars_row]))
        if o["ref_bonus"] and o["ref_to"]:
            await notify(ctx, [o["ref_to"]], t(o["ref_to"], "ref_bonus", v=o["ref_bonus"]))
        await notify(ctx, list(admin_ids()),
                     f"🧾 #{o['id']} {esc(o['product_name'])} от {esc(uname(payer))} — оплата {value}⭐/{rub}₽ ({method})")
    except Exception:
        log.exception("post-order notifications failed for order %s", o["id"])
    return True

async def precheckout(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    pq = update.pre_checkout_query
    uid = pq.from_user.id
    parts = pq.invoice_payload.split(":")
    if cfg("stars_enabled") == "0":
        return await pq.answer(ok=False, error_message="Оплата звёздами временно отключена")
    if parts[0] == "bt":
        try:
            valid = (len(parts) == 3 and int(parts[1]) == uid and int(parts[2]) == pq.total_amount
                     and pq.currency == "XTR" and valid_topup_amount(pq.total_amount, stars=True))
        except (ValueError, TypeError):
            valid = False
        if not valid:
            return await pq.answer(ok=False, error_message="Платёж не соответствует пользователю или сумме")
        return await pq.answer(ok=True)
    try:
        valid_payload = len(parts) == 5 and int(parts[4]) == uid
        pid, promo_id, bal_used = int(parts[1]), int(parts[2]), int(parts[3])
    except (ValueError, IndexError):
        return await pq.answer(ok=False, error_message="Некорректный заказ")
    if not valid_payload or bal_used < 0:
        return await pq.answer(ok=False, error_message="Этот счёт создан для другого пользователя")
    p = one("SELECT * FROM products WHERE id=?", (pid,))
    if not p or stock(pid) == 0:
        return await pq.answer(ok=False, error_message=t(uid, "out_stock"))
    if bal_used and balance(uid) < bal_used:
        return await pq.answer(ok=False, error_message="Баланс изменился. Создайте заказ заново.")
    promo = one("SELECT * FROM promos WHERE id=? AND active=1", (promo_id,)) if promo_id else None
    if promo_id and not promo:
        return await pq.answer(ok=False, error_message="Промокод больше недоступен. Создайте заказ заново.")
    total_rub = order_total_rub(p, promo)
    if total_rub > MAX_PAYMENT_RUB:
        return await pq.answer(ok=False, error_message=t(uid, "pay_limit"))
    expected_stars = math.ceil(max(total_rub - bal_used, 0) / star_rate() - 1e-9)
    if pq.total_amount != expected_stars:
        return await pq.answer(ok=False, error_message="Сумма заказа изменилась. Создайте заказ заново.")
    return await pq.answer(ok=True)

async def paid(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg = update.message; pay_ = msg.successful_payment; uid = msg.from_user.id
    parts = pay_.invoice_payload.split(":")
    charge = pay_.telegram_payment_charge_id
    if parts[0] == "bt":
        try:
            if len(parts) != 3 or int(parts[1]) != uid or int(parts[2]) != pay_.total_amount:
                await ctx.bot.refund_star_payment(uid, charge)
                await msg.reply_text("⚠️ Платёж не совпал с данными пополнения и был возвращён.")
                return
        except (ValueError, TypeError):
            await ctx.bot.refund_star_payment(uid, charge)
            await msg.reply_text("⚠️ Некорректные данные платежа. Платёж возвращён.")
            return
        stars_amount = pay_.total_amount
        credited = math.floor(stars_amount * star_rate())
        begin()
        try:
            cur = db.execute("INSERT OR IGNORE INTO topups(user_id,method,paid,credited,charge_id,ts) VALUES(?,?,?,?,?,?)",
                             (uid, "stars", stars_amount, credited, charge, now()))
            fresh = cur.rowcount == 1
            if fresh: balance_change("Пополнение Stars","UPDATE users SET balance=balance+? WHERE id=?", (credited, uid))
            db.execute("COMMIT")
        except Exception:
            if db.in_transaction: db.execute("ROLLBACK")
            raise
        if not fresh: return
        await msg.reply_text(
            f"✅ Зачислено на баланс: <b>{credited} ₽</b>\n"
            f"Оплачено: {stars_amount} ⭐ по курсу {star_rate()} ₽/⭐\n"
            f"Текущий баланс: <b>{balance(uid)} ₽</b>", parse_mode="HTML")
        return
    if one("SELECT 1 FROM orders WHERE charge_id=?", (charge,)): return
    try:
        if len(parts) != 5 or int(parts[4]) != uid:
            await ctx.bot.refund_star_payment(uid, charge)
            await msg.reply_text("⚠️ Этот счёт создан для другого пользователя. Платёж возвращён.")
            return
        pid, promo_id, bal_used = int(parts[1]), int(parts[2]), int(parts[3])
    except (ValueError, IndexError):
        await ctx.bot.refund_star_payment(uid, charge)
        await msg.reply_text("⚠️ Некорректные данные платежа. Платёж возвращён.")
        return
    ctx.user_data.pop("co", None)
    ok = await process_order(ctx, uid, uid, pid, promo_id, bal_used, pay_.total_amount,
                             pay_.total_amount, 0, "stars", charge)
    if not ok:
        try:
            await ctx.bot.refund_star_payment(uid, charge)
            await msg.reply_text(t(uid, "refunded_stock"))
        except TelegramError as e:
            log.error("refund: %s", e); await msg.reply_text("Out of stock. Contact support.")


async def my_orders(update,ctx,page=0):
    uid=update.effective_user.id
    orders=q("SELECT * FROM orders WHERE user_id=? AND refunded=0 ORDER BY id DESC LIMIT 9 OFFSET ?",(uid,page*8))
    lines=[]; rows=[]
    for o in orders[:8]:
        status="выдан" if o['delivery_type'] in DELIVERY_TYPES else "архив"
        lines.append(f"#{o['id']} · {esc(o['product_name'])} · {esc(status)}")
        buttons=[Btn(f"📥 #{o['id']}",callback_data=f"dl:{o['id']}")] if o['delivery_type'] in DELIVERY_TYPES else []
        if o['delivery_type']=='key': buttons.append(Btn("Замена",callback_data=f"bad:{o['id']}"))
        if buttons: rows.append(buttons)
    nav=[]
    if page: nav.append(Btn("⬅️",callback_data=f"ext:purchases:{page-1}"))
    if len(orders)>8: nav.append(Btn("➡️",callback_data=f"ext:purchases:{page+1}"))
    if nav: rows.append(nav)
    return await show(update,ctx,"📦 Мои покупки\n\n"+"\n".join(lines or ["Покупок пока нет"]),rows+[back_row(uid,"prof")])

async def orders_screen(update,ctx):
    return await my_orders(update,ctx)

async def re_deliver(update, ctx, oid):
    uid = update.effective_user.id
    o = one("SELECT * FROM orders WHERE id=? AND user_id=? AND refunded=0", (oid, uid))
    if not o: return await alert(update, t(uid, "out_stock"))
    await deliver_order(ctx, uid, o)
    await alert(update, "✅")


async def bad_key_request(update, ctx, oid):
    uid = update.effective_user.id
    o = one("SELECT * FROM orders WHERE id=? AND user_id=? AND refunded=0", (oid, uid))
    if not o or o["delivery_type"] != "key": return await alert(update, t(uid, "bad_limit"))
    pr_ = one("SELECT replace_days FROM products WHERE id=?", (o["product_id"],))
    days = pr_["replace_days"] if pr_ and pr_["replace_days"] is not None else REPLACE_DAYS
    if days <= 0 or now() - o["ts"] > days * 86400: return await alert(update, t(uid, "bad_limit"))
    if o["replace_status"] in ("pending", "approved", "rejected"):
        return await alert(update, t(uid, "bad_limit"))
    db.execute("UPDATE orders SET replace_status='pending' WHERE id=?", (oid,))
    db.execute("INSERT INTO tickets(user_id,text,status,ts) VALUES(?,?,?,?)",
               (uid, f"Замена ключа по заказу #{oid} ({o['product_name']})", "open", now()))
    text = (f"⚠️ <b>Запрос замены ключа</b>\n\n👤 {esc(uname(uid))} (<code>{uid}</code>)\n"
            f"🧾 Заказ #{oid}: {esc(o['product_name'])}\n🔑 <code>{esc(o['key_value'])}</code>\n"
            f"📦 Остаток: {stock_txt(stock(o['product_id']))}")
    rows = [[Btn("✅ Заменить", callback_data=f"apbad:{oid}:ok"),
             Btn("❌ Отклонить", callback_data=f"apbad:{oid}:no")]]
    await notify(ctx, list(admin_ids()), text, Markup(rows))
    await alert(update, t(uid, "bad_sent"))

async def approve_bad(update, ctx, oid, action):
    admin = update.effective_user.id
    if not is_admin(admin): return await alert(update, "⛔")
    if action not in ("ok", "no"): return await alert(update, "Неизвестное действие")
    o = one("SELECT * FROM orders WHERE id=?", (oid,))
    if not o or o["replace_status"] != "pending": return await alert(update, "Уже обработано")
    buyer = o["user_id"]
    if action == "no":
        db.execute("UPDATE orders SET replace_status='rejected' WHERE id=?", (oid,))
        await notify(ctx, [buyer], t(buyer, "bad_rejected"))
        return await alert(update, "❌ Отклонено")

    if db.in_transaction: db.execute("ROLLBACK")
    db.execute("BEGIN IMMEDIATE")
    try:
        pr = one("SELECT unlimited,delivery_type,delivery_config FROM products WHERE id=?", (o["product_id"],))
        if not pr or pr["delivery_type"] != "key":
            db.execute("ROLLBACK"); return await alert(update, "Замена для этого товара недоступна")
        old_k = one("SELECT key_id FROM order_keys WHERE order_id=?", (oid,))
        excl = old_k["key_id"] if old_k else 0
        new_k = one("SELECT * FROM keys WHERE product_id=? AND COALESCE(kind,'text') NOT LIKE 'file:%' AND sold_to IS NULL AND bad=0 AND id!=? ORDER BY id LIMIT 1",
                    (o["product_id"], excl))
        if not new_k:
            db.execute("ROLLBACK"); return await alert(update, "Нет ключей на складе")
        if old_k: db.execute("UPDATE keys SET bad=1 WHERE id=?", (old_k["key_id"],))
        p = one("SELECT unlimited,delivery_type,delivery_config FROM products WHERE id=?", (o["product_id"],))
        db.execute("UPDATE keys SET sold_to=?, sold_at=? WHERE id=?", (buyer, now(), new_k["id"]))
        if old_k:
            db.execute("UPDATE order_keys SET key_id=? WHERE order_id=?", (new_k["id"], oid))
        else:
            db.execute("INSERT INTO order_keys(order_id,key_id) VALUES(?,?)", (oid, new_k["id"]))
        db.execute("UPDATE orders SET key_value=?, replace_status='approved' WHERE id=?", (new_k["value"], oid))
        db.execute("COMMIT")
    except Exception:
        if db.in_transaction: db.execute("ROLLBACK")
        raise
    await send(ctx, buyer, t(buyer, "bad_approved") + f"<b>{esc(o['product_name'])}</b>\n<code>{esc(new_k['value'])}</code>")
    await alert(update, "✅ Заменено")


async def profile(update, ctx):
    uid = update.effective_user.id
    refs = one("SELECT COUNT(*) c FROM users WHERE ref_by=?", (uid,))["c"]
    link = f"https://t.me/{ctx.bot.username}?start=ref_{uid}"
    ru=lang_of(uid)=="ru"
    rows = [
        [Btn(t(uid, "b_orders"), callback_data="my")],
        [Btn("❤️ Избранное" if ru else "❤️ Favorites", callback_data="ext:favorites")],
        [Btn("💳 История баланса" if ru else "💳 Balance history", callback_data="ext:ledger:0")],
        [Btn("💰 Баланс" if ru else "💰 Balance", callback_data="balance"),
         Btn("🎁 Промокод" if ru else "🎁 Promo code", callback_data="profpromo")],
        [Btn("👥 Реферальная программа" if ru else "👥 Referral program", callback_data="refprog")],
        back_row(uid),
    ]
    user = update.effective_user
    ptxt = t(uid, "prof", id=uid, user_id=uid,
             name=esc(user.first_name or user.full_name or ""),
             username=esc("@" + user.username if user.username else "не указан"),
             bal=balance(uid), refs=refs, rp=cfg("ref_percent"), link=link)
    pend = one("SELECT pr.* FROM users u JOIN promos pr ON pr.id=u.promo_pending WHERE u.id=?", (uid,))
    if pend and promo_valid(pend) and pend["kind"] != "b":
        ptxt += ("\n\n🎁 Активный промокод: <b>%s</b> (%s) — применится при следующей покупке." if lang_of(uid) == "ru"
                 else "\n\n🎁 Active promo code: <b>%s</b> (%s) — applies to your next purchase.") % (esc(pend["code"]), promo_label(pend))
    await show(update, ctx, ptxt, rows, photo=pic(uid, "prof"))

async def support(update, ctx):
    uid = update.effective_user.id
    ctx.user_data["state"] = None
    support_username = (cfg("support_username") or "zenit_support_bot").strip()
    if support_username.startswith("https://t.me/"):
        support_url = support_username
    else:
        support_url = "https://t.me/" + support_username.lstrip("@").strip()
    rows = [
        [Btn(t(uid, "b_contact_support"), url=support_url)],
        [Btn(t(uid, "b_back"), callback_data="home")],
    ]
    contact = "@" + support_url.removeprefix("https://t.me/").split("?", 1)[0].rstrip("/")
    await show(update, ctx, t(uid, "support_contact_text", contact=esc(contact)), rows, photo=pic(uid, "sup_text"))

async def faq(update, ctx):
    uid = update.effective_user.id
    rows = [
        [Btn(t(uid, "b_agreement"), callback_data="agreement")],
        [Btn(t(uid, "b_privacy"), callback_data="privacy")],
        [back_row(uid)[0]],
    ]
    await show(update, ctx, t(uid, "faq_text"), rows,
               photo=pic(uid, "faq_text") or pic(uid, "b_faq"))

async def document_screen(update, ctx, key):
    uid = update.effective_user.id
    await show(update, ctx, t(uid, key), [back_row(uid, "faq")],
               photo=pic(uid, key))


async def balance_screen(update, ctx):
    uid = update.effective_user.id
    text = ("💰 <b>Твой баланс</b>\n\n"
            f"Доступно: <b>{balance(uid)} ₽</b>\n\n"
            "Пополните баланс, чтобы оплачивать покупки быстрее.")
    rows = [[Btn("➕ Пополнить баланс", callback_data="bal_topup")],
            [back_row(uid, "prof")[0]]]
    await show(update, ctx, text, rows, photo=pic(uid, "prof"))

async def balance_topup_start(update, ctx):
    uid = update.effective_user.id
    rows = [
        [Btn(t(uid, "bal_rub_button"), callback_data="bal_rub_custom")],
        [Btn(t(uid, "bal_star_button"), callback_data="bal_star_custom")],
        [back_row(uid, "balance")[0]],
    ]
    await show(update, ctx, t(uid, "bal_topup_title") + "\n\n" + t(uid, "bal_topup_desc"), rows, photo=pic(uid, "prof"))

def topup_max(stars=False):
    return math.floor(MAX_PAYMENT_RUB / star_rate()) if stars else MAX_PAYMENT_RUB

def valid_topup_amount(amount, stars=False):
    return 10 <= amount <= topup_max(stars)

async def balance_topup_pay(update, ctx, amount, method=None):

    uid = update.effective_user.id
    if not valid_topup_amount(amount):
        return await alert(update, t(uid, "bal_minmax", unit="₽", max=topup_max()))
    if not platega_ready():
        return await alert(update, t(uid, "bal_platega_missing"))
    methods = pl_methods()
    if not methods or (method is not None and method not in methods):
        return await alert(update, t(uid, "pay_err"))
    if method is None and len(methods) > 1:
        rows = [[Btn(t(uid, f"pm_{m}"), callback_data=f"bal_pm:{amount}:{m}")] for m in methods]
        rows.append(back_row(uid, "bal_topup"))
        return await show(update, ctx, t(uid, "bal_choose_method", amount=amount), rows, photo=pic(uid, "prof"))
    method = method if method is not None else methods[0]
    if method not in PM_IDS: return await alert(update, t(uid, "pay_err"))
    back_url = f"https://t.me/{ctx.bot.username}"
    body = {"paymentMethod": method, "paymentDetails": {"amount": amount, "currency": "RUB"},
            "description": f"Пополнение баланса {amount} RUB"[:100],
            "return": back_url, "failedUrl": back_url, "payload": f"balance:{uid}:{amount}"}
    try:
        data = await platega_post(body)
        tid = data.get("transactionId"); url = data.get("redirect") or data.get("url")
        if not tid or not url: raise ValueError(data)
    except Exception as e:
        log.error("platega balance topup create: %s", e)
        return await alert(update, t(uid, "pay_err"))
    db.execute("INSERT INTO payments(id,payer,owner,pid,promo_id,bal_used,final,rub,method,ts) VALUES(?,?,?,?,?,?,?,?,?,?)",
               (tid, uid, uid, 0, 0, 0, amount, amount, method, now()))
    rows = [[Btn(t(uid, "bal_pay_button", amount=amount), url=url)],
            [Btn(t(uid, "bal_check_button"), callback_data=f"chk:{tid}")],
            [back_row(uid, "balance")[0]]]
    await show(update, ctx, t(uid, "bal_pay_instructions", amount=amount), rows, photo=pic(uid, "prof"))

async def balance_topup_stars(update, ctx, amount):
    uid = update.effective_user.id
    if not valid_topup_amount(amount, stars=True):
        return await alert(update, t(uid, "bal_minmax", unit="⭐", max=topup_max(stars=True)))
    if cfg("stars_enabled") == "0":
        return await alert(update, "⭐ Оплата звёздами временно отключена. Выберите другой способ.")
    await ctx.bot.send_invoice(
        chat_id=update.effective_chat.id, title="Пополнение баланса",
        description=f"Пополнение баланса: {amount} ⭐, зачисление {math.floor(amount * star_rate())} RUB по курсу {star_rate()} RUB/⭐",
        payload=f"bt:{uid}:{amount}", provider_token="", currency="XTR",
        prices=[LabeledPrice("Пополнение баланса", amount)],
        reply_markup=Markup([[Btn(t(uid, "bal_stars_pay_button", amount=amount), pay=True)]]))

async def referral_screen(update, ctx):
    uid = update.effective_user.id
    refs = one("SELECT COUNT(*) c FROM users WHERE ref_by=?", (uid,))["c"]
    link = f"https://t.me/{ctx.bot.username}?start=ref_{uid}"
    text = t(uid, "ref_screen_text",
              title=t(uid, "ref_screen_title"),
              invited=t(uid, "ref_invited", refs=refs),
              bonus=t(uid, "ref_bonus_line", percent=cfg("ref_percent")),
              link_label=t(uid, "ref_link_label"),
              link=esc(link))
    await show(update, ctx, text, [back_row(uid, "prof")], photo=pic(uid, "prof"))

async def rate_stars(update, ctx, oid, stars):
    uid = update.effective_user.id
    if not 1 <= stars <= 5: return await alert(update, "Оценка должна быть от 1 до 5.")
    o = one("SELECT * FROM orders WHERE id=? AND user_id=?", (oid, uid))
    if not o:
        return await alert(update, "Покупка не найдена.")
    db.execute("INSERT OR IGNORE INTO reviews(order_id,product_id,user_id,stars,ts) VALUES(?,?,?,?,?)",
               (oid, o["product_id"], uid, stars, now()))
    db.execute("UPDATE reviews SET stars=? WHERE order_id=?", (stars, oid))
    ctx.user_data["state"] = "review_comment"
    ctx.user_data["review_order_id"] = oid
    await alert(update, "Спасибо за оценку!")
    try:
        await update.callback_query.message.reply_text(
            f"⭐ Спасибо за отзыв: {stars}/5\n\nНапишите комментарий или отправьте «-», чтобы оставить только оценку."
        )
    except TelegramError:
        pass

async def admin_reviews(update, ctx):
    uid = update.effective_user.id
    if not is_admin(uid):
        return await alert(update, "⛔")
    rows_data = q("""SELECT r.*, p.name product_name, u.name user_name, u.username
                     FROM reviews r LEFT JOIN products p ON p.id=r.product_id
                     LEFT JOIN users u ON u.id=r.user_id ORDER BY r.ts DESC LIMIT 30""")
    rows = []
    text = ["⭐ <b>Последние отзывы</b>"]
    if not rows_data:
        text.append("\nПока отзывов нет.")
    for r in rows_data:
        who = ("@" + r["username"]) if r["username"] else (r["user_name"] or str(r["user_id"]))
        comment = (r["comment"] or "Без комментария").strip()
        text.append(f"\n\n<b>{esc(r['product_name'] or 'Товар удалён')}</b> · {'⭐' * max(0, min(5, int(r['stars'] or 0)))}\n"
                    f"👤 {esc(who)}\n💬 {esc(comment[:500])}")
    await show(update, ctx, "".join(text), [back_row(uid, "adm")])


def adm_rows(uid):
    return [
        [Btn("📊 Статистика", callback_data="adm_stats"), Btn("🗂 Разделы и товары", callback_data="adm_cat")],
        [Btn("🔑 Ключи", callback_data="adm_keys"), Btn("🎟 Промокоды", callback_data="adm_promo")],
        [Btn("⭐ Отзывы", callback_data="adm_reviews")],
        [Btn("⚙️ Настройки", callback_data="adm_cfg"), Btn("👥 Админы", callback_data="adm_admins")],
        [Btn("📢 Рассылка", callback_data="adm_bc")],
        [Btn("✏️ Тексты", callback_data="adm_texts:ru:0")],
        *([[Btn("💾 Экспорт базы данных", callback_data="adm_export")]] if is_owner(uid) else []),
        back_row(uid),
    ]

async def admin_panel(update, ctx):
    uid = update.effective_user.id
    if not is_admin(uid): return await alert(update, "⛔")
    await show(update, ctx, "⚙️ <b>Админ-панель</b>", adm_rows(uid))

async def adm_export(update, ctx):
    uid = update.effective_user.id
    if not is_owner(uid):
        return await alert(update, "⛔ Только владелец")
    try:
        backup = sqlite3.connect(":memory:")
        try:
            db.backup(backup)
            data = backup.serialize()
        finally:
            backup.close()
        file_obj = io.BytesIO(data)
        file_obj.name = "shop.db"
        await ctx.bot.send_document(
            chat_id=uid,
            document=file_obj,
            filename="shop.db",
            caption="💾 SellBot · Экспорт базы данных"
        )
        return await alert(update, "✅ Экспорт отправлен в личные сообщения")
    except Exception:
        log.exception("Database export failed")
        return await alert(update, "❌ Не удалось экспортировать базу данных")

async def adm_stats(update, ctx):
    if not is_admin(update.effective_user.id): return await alert(update, "⛔")
    users = one("SELECT COUNT(*) c FROM users")["c"]
    orders = one("SELECT COUNT(*) c, COALESCE(SUM(stars),0) s, COALESCE(SUM(rub),0) r FROM orders WHERE refunded=0")
    keys = one("SELECT COUNT(*) c FROM keys WHERE sold_to IS NULL AND bad=0")["c"]
    await show(update, ctx, f"📊 Пользователи: {users}\n🧾 Заказов: {orders['c']}\n"
                            f"💰 Оплачено: {orders['s']}⭐ + {orders['r']}₽\n🔑 Ключей на складе: {keys}", [back_row(update.effective_user.id, "adm")])

async def adm_cat(update, ctx):
    uid = update.effective_user.id
    if not is_admin(uid): return await alert(update, "⛔")
    secs = q("SELECT * FROM sections ORDER BY id")
    rows = [[Btn(f"📁 {s['name']}", callback_data=f"adm_sec:{s['id']}")] for s in secs]
    rows.append([Btn("➕ Добавить раздел", callback_data="adm_addsec")])
    rows.append(back_row(uid, "adm"))
    await show(update, ctx, "📝 <b>Разделы</b>", rows)

async def adm_sec(update, ctx, sid):
    uid = update.effective_user.id
    if not is_admin(uid): return await alert(update, "⛔")
    s = one("SELECT * FROM sections WHERE id=?", (sid,))
    if not s: return await adm_cat(update, ctx)
    prods = q("SELECT * FROM products WHERE section_id=? ORDER BY pinned DESC, sort_order ASC, id DESC", (sid,))
    rows = [[Btn(f"{'📌 ' if p['pinned'] else '📦 '}{p['name']} — {rub_amount(p, p['price'])} ₽", callback_data=f"adm_prod:{p['id']}")] for p in prods]
    rows.append([Btn("➕ Добавить товар", callback_data=f"adm_addprod:{sid}")])
    rows.append([Btn("✏️ Название раздела", callback_data=f"adm_editsec:{sid}")])
    rows.append([Btn("📝 Описание раздела", callback_data=f"adm_secdesc:{sid}")])
    rows.append([Btn("🖼 Фото раздела", callback_data=f"adm_secphoto:{sid}")])
    rows.append([Btn("🗑 Удалить раздел", callback_data=f"adm_delsec:{sid}")])
    rows.append(back_row(uid, "adm_cat"))
    await show(update, ctx, f"📁 <b>{esc(s['name'])}</b>", rows)

async def adm_prod(update, ctx, pid):
    uid = update.effective_user.id
    if not is_admin(uid): return await alert(update, "⛔")
    p = one("SELECT * FROM products WHERE id=?", (pid,))
    if not p: return await adm_cat(update, ctx)
    keys = stock(pid)
    text = (f"📦 <b>{esc(p['name'])}</b>\nЦена: {rub_amount(p, p['price'])} ₽\nОстаток: {stock_txt(stock(pid))}\n"
            f"Описание: {esc(p['description'])}\nСрок: {p['duration']} дн.\n"
            f"Тип выдачи: {DELIVERY_TYPES.get(p['delivery_type'], 'Не настроен')}")
    rows = [
        [Btn("➕ Ключи", callback_data=f"adm_addkeys:{pid}"), Btn("🗑 Удалить", callback_data=f"adm_delprod:{pid}")],
        [Btn("✏️ Цена в ₽", callback_data=f"adm_editprice:{pid}"), Btn("✏️ Название", callback_data=f"adm_editname:{pid}")],
        [Btn("✏️ Описание", callback_data=f"adm_editdesc:{pid}"), Btn("⏳ Срок", callback_data=f"adm_editduration:{pid}")],
        [Btn("🖼 Фото товара", callback_data=f"adm_editphoto:{pid}"), Btn("📌 Закрепить" if not p["pinned"] else "📍 Открепить", callback_data=f"adm_pin:{pid}")],
        [Btn("🔢 Порядок товара", callback_data=f"adm_editorder:{pid}"), Btn("🔄 Время замены", callback_data=f"adm_editreplace:{pid}")],
        [Btn("🔑 Управление ключами", callback_data=f"adm_keys:{pid}")],
        [Btn("📦 Тип выдачи / настройки", callback_data=f"ext:config:{pid}")],
        back_row(uid, f"adm_sec:{p['section_id']}"),
    ]
    if p["delivery_type"] != "key":
        hidden=("adm_addkeys:","adm_keys:","adm_editreplace:")
        rows=[[button for button in row if not (button.callback_data or "").startswith(hidden)] for row in rows]
        rows=[row for row in rows if row]
    else:
        text+=f"\n🔄 Замена ключа: {p['replace_days']} дн.\nКлючей: {keys}"
    await show(update, ctx, text, rows)

async def adm_keys_list(update, ctx, pid):
    uid = update.effective_user.id
    if not is_admin(uid): return await alert(update, "⛔")
    ks = q("SELECT * FROM keys WHERE product_id=? AND COALESCE(kind,'text') NOT LIKE 'file:%' ORDER BY id DESC LIMIT 50", (pid,))
    text = f"🔑 <b>Ключи товара #{pid}</b>\n\n" + "\n".join(
        f"{k['id']}. {'✅ Продан' if k['sold_to'] else '⬜ На складе'}{' ❌' if k['bad'] else ''} <code>{esc(k['value'][:45])}</code>"
        for k in ks) if ks else "Пусто."
    rows = [[Btn(f"🗑 Удалить ключ #{k['id']}", callback_data=f"adm_delkey:{k['id']}:{pid}")]
            for k in ks if k['sold_to'] is None]
    rows.append(back_row(uid, f"adm_prod:{pid}"))
    await show(update, ctx, text, rows)

def decode_keys_file(raw):
    if not raw: raise ValueError("Файл пустой.")
    if len(raw) > MAX_KEYS_FILE_BYTES: raise ValueError("Файл должен быть не больше 2 МБ.")
    encodings = ("utf-16",) if raw.startswith((b"\xff\xfe", b"\xfe\xff")) else ("utf-8-sig", "cp1251")
    for encoding in encodings:
        try: return raw.decode(encoding)
        except UnicodeError: pass
    raise ValueError("Не удалось прочитать текст. Сохраните .txt в кодировке UTF-8.")

def parse_keys_text(text):
    text = text.lstrip("\ufeff")
    if any((ord(c) < 32 and c not in "\n\r\t") or 127 <= ord(c) < 160 for c in text):
        raise ValueError("Файл содержит служебные символы. Нужен обычный текстовый .txt.")
    values = [line.strip() for line in text.splitlines() if line.strip()]
    if not values: raise ValueError("Нет данных: добавьте хотя бы одну непустую строку.")
    if len(values) > MAX_IMPORT_KEYS: raise ValueError("За один раз можно загрузить не больше 10 000 строк.")
    return values

async def import_keys_text(update, ctx, text):
    uid = update.effective_user.id
    if not is_admin(uid): return await update.message.reply_text("⛔ Нет доступа.")
    pid = (ctx.user_data.get("sd") or {}).get("pid")
    prod = one("SELECT name,delivery_type FROM products WHERE id=?", (pid,))
    if not prod or prod["delivery_type"] != "key":
        ctx.user_data.pop("state", None); ctx.user_data.pop("sd", None)
        return await update.message.reply_text("Товар не найден. Выберите товар в админке заново.")
    try:
        values = parse_keys_text(text)
    except ValueError as e:
        ctx.user_data["state"] = "adm_keys"
        return await update.message.reply_text(f"❌ {e} Отправьте исправленный текст или файл.")
    try:
        begin()
        existing = {r["value"] for r in q("SELECT value FROM keys WHERE product_id=?", (pid,))}
        unique = list(dict.fromkeys(values))
        new_values = [value for value in unique if value not in existing]
        db.executemany("INSERT INTO keys(product_id,value) VALUES(?,?)", ((pid, value) for value in new_values))
        db.execute("COMMIT")
    except sqlite3.Error:
        if db.in_transaction: db.execute("ROLLBACK")
        log.exception("Key import failed for product %s", pid)
        ctx.user_data["state"] = "adm_keys"
        return await update.message.reply_text("❌ Не удалось сохранить товар. Данные не добавлены; попробуйте ещё раз.")
    ctx.user_data.pop("state", None); ctx.user_data.pop("sd", None)
    duplicates = len(values) - len(new_values)
    await update.message.reply_text(f"✅ Добавлено единиц товара: {len(new_values)}.\nПропущено повторов: {duplicates}.")
    if new_values and stock(pid) > 0:
        for sub in q("SELECT user_id FROM restock_subs WHERE product_id=?", (pid,)):
            try:
                await ctx.bot.send_message(sub["user_id"], t(sub["user_id"], "restock", name=esc(prod["name"])), parse_mode="HTML")
                db.execute("DELETE FROM restock_subs WHERE user_id=? AND product_id=?", (sub["user_id"], pid))
            except TelegramError: pass
    return await adm_prod(update, ctx, pid)


async def adm_cfg(update, ctx):
    uid = update.effective_user.id
    if not is_admin(uid): return await alert(update, "⛔")
    rows = [
        [Btn(f"🆘 Поддержка: @{(cfg('support_username') or 'zenit_support_bot').replace('https://t.me/', '').lstrip('@')}", callback_data="cfg_support")],
        [Btn(f"🎁 Реф. %: {cfg('ref_percent') or os.getenv('REF_PERCENT', '0')}", callback_data="cfg_ref")],
        [Btn(f"⭐ Оплата звёздами: {'✅ Включена' if cfg('stars_enabled') != '0' else '❌ Выключена'}", callback_data="cfg_stars")],
        [Btn(f"💱 ₽ за ⭐: {cfg('rub_per_star') or os.getenv('RUB_PER_STAR', '1.7')}", callback_data="cfg_rub")],
        [Btn(f"🏦 Platega: {'✅' if platega_ready() else '❌'}", callback_data="cfg_platega")],
        [Btn(f"🏦 Методы: {','.join(map(str, pl_methods()))}", callback_data="cfg_methods")],
        back_row(uid, "adm"),
    ]
    await show(update, ctx, "⚙️ <b>Настройки</b>", rows)


HIDDEN_TEXT_KEYS = {

    "b_rules", "b_agreement", "b_privacy", "b_faq", "b_catalog",
    "tk_sent", "tk_reply", "sup_text", "support_contact_text", "paid_cb", "faq_text_unused",
}
TEXT_LABELS = {
    "welcome": "Приветствие",
    "catalog_text": "Текст экрана каталога",
    "cat_empty": "Текст пустого каталога",
    "p_price": "Цена товара", "p_stock": "Наличие товара", "p_stock_unl": "Безлимитный остаток",
    "p_none": "Нет в наличии", "prof": "Текст профиля",
    "faq_text": "Текст раздела «Документы»",
    "agreement_text": "Текст соглашения и правил",
    "privacy_text": "Текст политики конфиденциальности",
    "rules_text": "Текст правил",
}


TEXT_GROUPS = {
    "menu": ("🏠 Приветствие и разделы", ("welcome", "faq_text")),
    "catalog": ("🛍 Каталог и товары", ("catalog_text",)),
    "support": ("👤 Профиль и документы", ("prof", "agreement_text", "privacy_text")),
}

def editable_text_keys(group=None):
    keys = {k for _, (_, items) in TEXT_GROUPS.items() for k in items} - HIDDEN_TEXT_KEYS
    ordered = []
    group_keys = dict((k, g) for g, (_, items) in TEXT_GROUPS.items() for k in items)
    if group in TEXT_GROUPS:
        ordered.extend(k for k in TEXT_GROUPS[group][1] if k in keys)
        ordered.extend(sorted(k for k in keys if group_keys.get(k) == group and k not in ordered))
        return ordered
    for _, items in TEXT_GROUPS.values():
        ordered.extend(k for k in items if k in keys and k not in ordered)
    ordered.extend(sorted(keys - set(ordered)))
    return ordered

async def adm_texts(update, ctx, language="ru", page=0, group=None):
    uid = update.effective_user.id
    if not is_admin(uid):
        return await alert(update, "⛔")
    language = "en" if language == "en" else "ru"
    if group not in TEXT_GROUPS:
        group = None
    keys = editable_text_keys(group)
    page_size = 10
    pages = max(1, (len(keys) + page_size - 1) // page_size)
    page = max(0, min(int(page), pages - 1))
    rows = []

    for key in keys[page * page_size:(page + 1) * page_size]:
        value = cfg(f"text_{language}_{key}") or T.get(language, {}).get(key) or T["ru"].get(key, "")
        preview = " ".join(value.replace("\n", " ").split())
        if len(preview) > 30:
            preview = preview[:27] + "..."
        has_photo = bool(cfg(f"photo_{language}_{key}"))
        label = TEXT_LABELS.get(key, key.replace("_", " ").capitalize())
        rows.append([Btn(f"✏️ {'🖼️ ' if has_photo else ''}{label}: {preview}"[:60],
                         callback_data=f"adm_textedit:{language}:{group or 'all'}:{key}")])
    nav = []
    if page > 0:
        nav.append(Btn("⬅️ Назад", callback_data=f"adm_texts:{language}:{page-1}:{group or 'all'}"))
    nav.append(Btn(f"Стр. {page+1}/{pages}", callback_data="adm_texts_help"))
    if page + 1 < pages:
        nav.append(Btn("Вперёд ➡️", callback_data=f"adm_texts:{language}:{page+1}:{group or 'all'}"))
    rows.append(nav)
    rows.append([Btn("🇷🇺 Русский" if language == "en" else "🇬🇧 English",
                     callback_data=f"adm_texts:{'ru' if language == 'en' else 'en'}:0:{group or 'all'}")])
    rows.append(back_row(uid, "adm"))
    group_title = TEXT_GROUPS[group][0] if group else "Все категории"
    await show(update, ctx,
               f"✏️ <b>Тексты</b> · {language.upper()}\nРаздел: {group_title}",
               rows)

async def adm_promo(update, ctx):
    uid = update.effective_user.id
    if not is_admin(uid): return await alert(update, "⛔")
    ps = q("SELECT * FROM promos ORDER BY id DESC LIMIT 30")
    text = ("🎁 <b>Промокоды</b>\n\nНажмите на промокод, чтобы отключить или удалить его." if ps else
            "🎁 <b>Промокоды</b>\n\nПромокодов пока нет.")
    rows = [[Btn(f"{'✅' if promo_valid(p) else '⏸'} {p['code']} · {promo_label(p)} · {p['used']}/{p['max_uses'] or '∞'}",
                 callback_data=f"adm_pr:{p['id']}")] for p in ps]
    rows.append([Btn("➕ Создать", callback_data="adm_addpromo")])
    rows.append(back_row(uid, "adm"))
    await show(update, ctx, text, rows)

async def adm_pr(update, ctx, pid):
    uid = update.effective_user.id
    if not is_admin(uid): return await alert(update, "⛔")
    p = one("SELECT * FROM promos WHERE id=?", (pid,))
    if not p: return await adm_promo(update, ctx)
    if not p["active"]: st_ = "⏸ отключён"
    elif p["expires"] and p["expires"] < now(): st_ = "⌛ срок истёк"
    elif p["max_uses"] and p["used"] >= p["max_uses"]: st_ = "🚫 лимит исчерпан"
    else: st_ = "✅ действует"
    kind_txt = {"p": "скидка в процентах", "r": "скидка в рублях", "b": "бонус на баланс (активируется в профиле)",
                "s": "скидка в эквиваленте ⭐"}.get(p["kind"], p["kind"])
    text = (f"🎁 <b>{esc(p['code'])}</b>\n\n"
            f"Тип: {kind_txt}\nЗначение: <b>{promo_label(p)}</b>\n"
            f"Использовано: {p['used']} из {p['max_uses'] or '∞'}\n"
            f"Срок: {fmt_date(p['expires']) if p['expires'] else 'бессрочно'}\n"
            f"Статус: {st_}")
    rows = [[Btn("▶️ Включить" if not p["active"] else "⏸ Отключить", callback_data=f"adm_prt:{pid}")],
            [Btn("🗑 Удалить", callback_data=f"adm_prd:{pid}")],
            back_row(uid, "adm_promo")]
    await show(update, ctx, text, rows)

async def adm_pr_toggle(update, ctx, pid):
    uid = update.effective_user.id
    if not is_admin(uid): return await alert(update, "⛔")
    db.execute("UPDATE promos SET active=1-active WHERE id=?", (pid,))
    return await adm_pr(update, ctx, pid)

async def adm_pr_delete(update, ctx, pid, confirm=False):
    uid = update.effective_user.id
    if not is_admin(uid): return await alert(update, "⛔")
    p = one("SELECT * FROM promos WHERE id=?", (pid,))
    if not p: return await adm_promo(update, ctx)
    if not confirm:
        return await show(update, ctx, f"🗑 Удалить промокод <b>{esc(p['code'])}</b>?\nЭто действие нельзя отменить.",
                          [[Btn("✅ Да, удалить", callback_data=f"adm_prdy:{pid}")], back_row(uid, f"adm_pr:{pid}")])
    begin()
    try:
        db.execute("DELETE FROM promo_uses WHERE promo_id=?", (pid,))
        db.execute("UPDATE users SET promo_pending=0 WHERE promo_pending=?", (pid,))
        db.execute("DELETE FROM promos WHERE id=?", (pid,))
        db.execute("COMMIT")
    except Exception:
        if db.in_transaction: db.execute("ROLLBACK")
        raise
    try: await update.callback_query.answer("🗑 Промокод удалён")
    except TelegramError: pass
    return await adm_promo(update, ctx)

async def adm_addpromo(update, ctx):
    uid = update.effective_user.id
    if not is_admin(uid): return await alert(update, "⛔")
    ctx.user_data["state"] = "adm_promo_code"
    await show(update, ctx, "Введите код промокода:", [back_row(uid, "adm_promo")])

async def adm_admins(update, ctx):
    uid = update.effective_user.id
    if not is_owner(uid): return await alert(update, "Только владелец")
    adm = q("SELECT * FROM admins")
    text = "👥 <b>Админы</b>\n\n" + "\n".join(f"<code>{a['id']}</code>" for a in adm) if adm else "Только владелец."
    rows = [[Btn("➕ Добавить", callback_data="adm_addadmin")], back_row(uid, "adm")]
    await show(update, ctx, text, rows)

async def adm_bc(update, ctx):
    uid = update.effective_user.id
    if not is_admin(uid): return await alert(update, "⛔")
    ctx.user_data["state"] = "adm_bc_text"
    await show(update, ctx, "📢 Отправьте текст рассылки (HTML):", [back_row(uid, "adm")])

OWNER_CB = {"adm_export", "cfg_platega", "cfg_methods", "cfg_rub", "cfg_stars", "cfg_ref"}
OWNER_TEXT_STATES = {"adm_addadmin", "cfg_ref", "cfg_rub", "cfg_methods", "cfg_platega_merchant", "cfg_platega_secret"}
async def on_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    data = update.callback_query.data
    if not isinstance(data, str):
        return await alert(update, "Кнопка устарела. Откройте меню через /start.")
    try:
        return await _route_callback(update, ctx)
    except (ValueError, IndexError):
        log.warning("Ignored malformed callback: %r", data[:64])
        return await alert(update, "Некорректная или устаревшая кнопка. Откройте меню через /start.")

async def _route_callback(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    c = update.callback_query; d = c.data; uid = c.from_user.id

    if d == "adm" and not is_admin(uid):
        return await alert(update, "⛔ Нет доступа")
    if d.startswith(("adm", "cfg_", "apbad:")) and not is_admin(uid):
        return await alert(update, "⛔ Нет доступа")
    if d in OWNER_CB and not is_owner(uid):
        return await alert(update, "⛔ Только владелец")

    ctx.user_data.pop("state", None)
    ctx.user_data.pop("sd", None)
    ctx.user_data.pop("review_order_id", None)
    ctx.user_data.pop("platega_merchant_pending", None)
    if d == "home": return await send_home(update, ctx)
    if d == "cat": return await catalog(update, ctx)
    if d.startswith("sec:"): return await section(update, ctx, int(d[4:]))
    if d.startswith("prod:"): return await product(update, ctx, int(d[5:]))
    if d.startswith("co:"): return await checkout_start(update, ctx, int(d[3:]))
    if d == "co_back": return await render_checkout(update, ctx)
    if d == "cob": return await render_checkout(update, ctx)
    if d == "cop":
        ctx.user_data["state"] = "promo"; return await show(update, ctx, t(uid, "promo_ask"), [back_row(uid, "co_back")])
    if d == "cop_rm":
        co, p = get_co(ctx)
        if co: co["promo"] = None
        db.execute("UPDATE users SET promo_pending=0 WHERE id=?", (uid,))
        return await render_checkout(update, ctx)
    if d == "profpromo":
        ctx.user_data["state"] = "profile_promo"
        return await show(update, ctx, "🎁 Отправьте промокод:" if lang_of(uid) == "ru" else "🎁 Send the promo code:",
                          [back_row(uid, "prof")])
    if d == "pay": return await pay(update, ctx)
    if d == "payrub": return await pay_rub(update, ctx)
    if d.startswith("pay_pm:"): return await create_platega_order(update, ctx, int(d.split(":", 1)[1]))
    if d.startswith("pm:"): return await render_checkout(update, ctx)
    if d.startswith("chk:"): return await chk_payment(update, ctx, d[4:])
    if d == "my": return await my_orders(update, ctx)
    if d == "orders": return await orders_screen(update, ctx)
    if d == "search":
        ctx.user_data["state"] = "search"
        return await show(update, ctx, "🔎 <b>Поиск товара</b>\nВведите название или часть названия:", [back_row(uid)])
    if d == "balance": return await balance_screen(update, ctx)
    if d == "bal_topup": return await balance_topup_start(update, ctx)
    if d in ("bal_rub_custom", "bal_star_custom"):
        stars = d == "bal_star_custom"
        ctx.user_data["state"] = "balance_topup_stars_amount" if stars else "balance_topup_amount"
        return await show(update, ctx, t(uid, "bal_amount_prompt", max=topup_max(stars), unit="⭐" if stars else "₽"),
                          [back_row(uid, "bal_topup")])
    if d.startswith("bal_amt:"): return await balance_topup_pay(update, ctx, int(d.split(":")[1]))
    if d.startswith("bal_star_amt:"): return await balance_topup_stars(update, ctx, int(d.split(":")[1]))
    if d.startswith("bal_pm:"):
        _, amount, method = d.split(":")
        return await balance_topup_pay(update, ctx, int(amount), int(method))
    if d == "refprog": return await referral_screen(update, ctx)
    if d.startswith("dl:"): return await re_deliver(update, ctx, int(d[3:]))
    if d.startswith("bad:"): return await bad_key_request(update, ctx, int(d[4:]))
    if d.startswith("apbad:"):
        _, oid, act = d.split(":"); return await approve_bad(update, ctx, int(oid), act)
    if d.startswith("rate:"):
        _, oid, st = d.split(":"); return await rate_stars(update, ctx, int(oid), int(st))
    if d == "adm_reviews": return await admin_reviews(update, ctx)
    if d == "prof": return await profile(update, ctx)
    if d == "sup": return await support(update, ctx)
    if d == "faq": return await faq(update, ctx)
    if d == "agreement": return await document_screen(update, ctx, "agreement_text")
    if d == "rules": return await document_screen(update, ctx, "rules_text")
    if d == "privacy": return await document_screen(update, ctx, "privacy_text")
    if d == "lang":
        lg = "en" if lang_of(uid) == "ru" else "ru"
        db.execute("UPDATE users SET lang=? WHERE id=?", (lg, uid)); LANG[uid] = lg
        return await send_home(update, ctx)
    if d.startswith("nf:"): return await toggle_notify(update, int(d[3:]))

    if d == "adm":
        if not is_admin(uid): return await alert(update, "⛔")
        return await admin_panel(update, ctx)
    if d == "adm_export": return await adm_export(update, ctx)
    if d == "adm_stats": return await adm_stats(update, ctx)
    if d == "adm_cat": return await adm_cat(update, ctx)
    if d.startswith("adm_sec:"): return await adm_sec(update, ctx, int(d[8:]))
    if d.startswith("adm_prod:"): return await adm_prod(update, ctx, int(d[9:]))
    if d.startswith("adm_keys:"): return await adm_keys_list(update, ctx, int(d[9:]))
    if d.startswith("adm_pin:"):
        pid = int(d.split(":", 1)[1])
        prod = one("SELECT * FROM products WHERE id=?", (pid,))
        if not prod: return await alert(update, "Товар не найден")
        db.execute("UPDATE products SET pinned=? WHERE id=?", (0 if prod["pinned"] else 1, pid))
        return await adm_prod(update, ctx, pid)
    if d.startswith("adm_delkey:"):
        _, kid, pid = d.split(":")
        kid, pid = int(kid), int(pid)
        key = one("SELECT * FROM keys WHERE id=? AND product_id=?", (kid, pid))
        if not key: return await alert(update, "Ключ не найден")
        if key["sold_to"] is not None: return await alert(update, "Проданный ключ нельзя удалить из истории заказа")
        db.execute("DELETE FROM keys WHERE id=?", (kid,))
        return await adm_keys_list(update, ctx, pid)
    if d.startswith("adm_secdesc:"):
        sid = int(d.split(":", 1)[1])
        sec = one("SELECT * FROM sections WHERE id=?", (sid,))
        if not sec: return await alert(update, "Раздел не найден")
        ctx.user_data["state"] = "adm_secdesc"; ctx.user_data["sd"] = {"sid": sid}
        return await show(update, ctx, f"📝 Текущее описание: {esc(sec['description'] or '—')}\n\nОтправьте новое описание. Чтобы очистить, отправьте СБРОС.", [back_row(uid, f"adm_sec:{sid}")])
    if d.startswith("adm_secphoto:"):
        sid = int(d.split(":", 1)[1])
        if not one("SELECT id FROM sections WHERE id=?", (sid,)): return await alert(update, "Раздел не найден")
        ctx.user_data["state"] = "adm_section_photo"; ctx.user_data["sd"] = {"sid": sid}
        return await show(update, ctx, "🖼 Отправьте фото для раздела. Чтобы удалить текущее фото, отправьте УДАЛИТЬ ФОТО.", [back_row(uid, f"adm_sec:{sid}")])
    if d.startswith("adm_media:"):
        if not is_admin(uid): return await alert(update, "⛔")
        kind = d.split(":", 1)[1]
        if kind not in ("catalog", "documents"):
            return await alert(update, "Неизвестный экран")
        key = "catalog_text" if kind == "catalog" else "faq_text"
        ctx.user_data["state"] = "adm_media_photo"
        ctx.user_data["sd"] = {"key": key}
        label = "каталога" if kind == "catalog" else "документов"
        return await show(update, ctx, f"🖼 Отправьте новое фото {label}.\n\nЧтобы удалить фото, отправьте УДАЛИТЬ ФОТО.", [back_row(uid, "adm_cfg")], photo=pic(uid, key))
    if d == "adm_cfg": return await adm_cfg(update, ctx)
    if d == "cfg_stars":
        if not is_admin(uid): return await alert(update, "⛔")
        set_cfg("stars_enabled", "0" if cfg("stars_enabled") != "0" else "1")
        return await adm_cfg(update, ctx)
    if d == "cfg_adminfile": return await adm_cfg(update, ctx)
    if d.startswith("adm_texts:"):
        parts = d.split(":")
        lg = parts[1]
        pg = int(parts[2])
        group = parts[3] if len(parts) > 3 and parts[3] != "all" else None
        return await adm_texts(update, ctx, lg, pg, group)
    if d.startswith("adm_textedit:"):
        if not is_admin(uid): return await alert(update, "⛔")
        _, lg, group, key = d.split(":", 3)
        if key not in editable_text_keys(): return await alert(update, "Неизвестный текст")
        ctx.user_data["state"] = "adm_textedit"
        ctx.user_data["sd"] = {"lang": lg, "key": key, "group": group}
        old_text = cfg(f"text_{lg}_{key}") or T.get(lg, {}).get(key) or T["ru"].get(key, "")
        photo_now = cfg(f"photo_{lg}_{key}")
        photo_note = "🖼️ Фото уже добавлено." if photo_now else "🖼️ Фото пока нет."
        back_group = group if group != "all" else "all"
        return await show(update, ctx,
            f"✏️ <b>Редактирование: {esc(TEXT_LABELS.get(key, key))}</b> ({lg})\n\nТекущий текст:\n{esc(old_text[:1800])}\n\n{photo_note}\n\nОтправьте новый текст или фотографию. Напишите УДАЛИТЬ ФОТО, чтобы убрать фото, или СБРОС, чтобы вернуть стандартный текст. Сохраняйте шаблоны вроде {{{{name}}}}.",
            [back_row(uid, f"adm_texts:{lg}:0:{back_group}")])
    if d == "adm_texts_help":
        return await alert(update, "Текст с переменными вроде {name} сохраняйте вместе с фигурными скобками.")
    if d == "adm_promo": return await adm_promo(update, ctx)
    if d.startswith("adm_pr:"): return await adm_pr(update, ctx, int(d[7:]))
    if d.startswith("adm_prt:"): return await adm_pr_toggle(update, ctx, int(d[8:]))
    if d.startswith("adm_prd:"): return await adm_pr_delete(update, ctx, int(d[8:]))
    if d.startswith("adm_prdy:"): return await adm_pr_delete(update, ctx, int(d[9:]), confirm=True)
    if d == "adm_addpromo": return await adm_addpromo(update, ctx)
    if d == "adm_admins": return await adm_admins(update, ctx)
    if d == "adm_bc": return await adm_bc(update, ctx)
    if d == "adm_keys":
        if not is_admin(uid): return await alert(update, "⛔")
        prods = q("SELECT id, name FROM products WHERE delivery_type='key' ORDER BY id")
        rows = [[Btn(f"📦 {p['name']}"[:60], callback_data=f"adm_keys:{p['id']}")] for p in prods]
        rows.append(back_row(uid, "adm"))
        return await show(update, ctx, "🔑 <b>Выберите товар для просмотра ключей</b>", rows)
    if d == "adm_addadmin":
        if not is_owner(uid): return await alert(update, "Только владелец")
        ctx.user_data["state"] = "adm_addadmin"
        return await show(update, ctx, "Отправьте числовой Telegram ID пользователя:", [back_row(uid, "adm_admins")])
    if d.startswith("adm_editprice:"):
        if not is_admin(uid): return await alert(update, "⛔")
        pid = int(d.split(":", 1)[1])
        if not one("SELECT id FROM products WHERE id=?", (pid,)): return await alert(update, "Товар не найден")
        ctx.user_data["state"] = "adm_editprice"
        ctx.user_data["sd"] = {"pid": pid}
        return await show(update, ctx, "Введите новую цену в рублях (целое число от 0). Это будет цена для покупателя:", [back_row(uid, f"adm_prod:{pid}")])
    if d.startswith("adm_editorder:"):
        if not is_admin(uid): return await alert(update, "⛔")
        pid = int(d.split(":", 1)[1])
        prod = one("SELECT id, section_id, sort_order FROM products WHERE id=?", (pid,))
        if not prod: return await alert(update, "Товар не найден")
        ctx.user_data["state"] = "adm_editorder"
        ctx.user_data["sd"] = {"pid": pid, "sid": prod["section_id"]}
        return await show(update, ctx,
            f"🔢 <b>Порядок товара</b>\n\nТекущий номер: {prod['sort_order']}\n"
            "Отправьте целое положительное число. Чем меньше номер, тем выше товар в каталоге. "
            "Закреплённые товары всё равно отображаются первыми.",
            [back_row(uid, f"adm_prod:{pid}")])
    if d.startswith("adm_editname:"):
        if not is_admin(uid): return await alert(update, "⛔")
        pid = int(d.split(":", 1)[1])
        if not one("SELECT id FROM products WHERE id=?", (pid,)): return await alert(update, "Товар не найден")
        ctx.user_data["state"] = "adm_editname"
        ctx.user_data["sd"] = {"pid": pid}
        return await show(update, ctx, "Введите новое название товара:", [back_row(uid, f"adm_prod:{pid}")])
    if d.startswith("adm_editsec:"):
        if not is_admin(uid): return await alert(update, "⛔")
        sid = int(d.split(":", 1)[1])
        if not one("SELECT id FROM sections WHERE id=?", (sid,)): return await alert(update, "Раздел не найден")
        ctx.user_data["state"] = "adm_editsec"
        ctx.user_data["sd"] = {"sid": sid}
        return await show(update, ctx, "Введите новое название раздела:", [back_row(uid, f"adm_sec:{sid}")])
    if d.startswith("adm_editphoto:"):
        if not is_admin(uid): return await alert(update, "⛔")
        pid = int(d.split(":", 1)[1])
        prod = one("SELECT id FROM products WHERE id=?", (pid,))
        if not prod: return await alert(update, "Товар не найден")
        ctx.user_data["state"] = "adm_product_photo"
        ctx.user_data["sd"] = {"pid": pid}
        return await show(update, ctx,
            "🖼 Отправьте фотографию товара одним сообщением. Она будет показываться в карточке товара.\n\n"
            "Чтобы убрать фото, отправьте текст: УДАЛИТЬ ФОТО",
            [back_row(uid, f"adm_prod:{pid}")])
    if d.startswith(("adm_editdesc:", "adm_editduration:", "adm_editrubprice:", "adm_editreplace:")):
        if not is_admin(uid): return await alert(update, "⛔")
        action, pid_text = d.split(":", 1)
        pid = int(pid_text)
        prod = one("SELECT * FROM products WHERE id=?", (pid,))
        if not prod: return await alert(update, "Товар не найден")
        state_map = {"adm_editdesc": ("adm_editdesc", "Введите новое описание товара:"),
                     "adm_editduration": ("adm_editduration", "Введите срок действия в днях (0 — без срока):"),
                     "adm_editreplace": ("adm_editreplace", "Сколько дней покупатель может запросить замену ключа для этого товара? (0 — замена недоступна):"),
                     "adm_editrubprice": ("adm_editrubprice", "Введите цену в рублях (0 — не показывать):")}
        state, prompt = state_map[action]
        ctx.user_data["state"] = state
        ctx.user_data["sd"] = {"pid": pid}
        return await show(update, ctx, prompt, [back_row(uid, f"adm_prod:{pid}")])
    if d == "adm_addsec":
        ctx.user_data["state"] = "adm_sec_name"
        return await show(update, ctx, "Название раздела:", [back_row(uid, "adm_cat")])
    if d.startswith("adm_addprod:"):
        ctx.user_data["state"] = "adm_prod"; ctx.user_data["sd"] = {"sid": int(d[12:])}
        return await show(update, ctx, "Товар: `Название | Цена в ₽ | Описание`", [back_row(uid, f"adm_sec:{d[12:]}")])
    if d.startswith("adm_addkeys:"):
        pid = int(d[12:])
        if not one("SELECT id FROM products WHERE id=?", (pid,)): return await alert(update, "Товар не найден")
        ctx.user_data["state"] = "adm_keys"; ctx.user_data["sd"] = {"pid": pid}
        return await show(update, ctx,
            "📥 <b>Загрузка товара</b>\n\nОтправьте ключи/данные текстом или прикрепите файл <b>.txt</b>. "
            "Одна непустая строка — одна единица товара.\n"
            "Кодировка: UTF-8, UTF-16 с BOM или Windows-1251. До 2 МБ и 10 000 строк за раз. "
            "Повторяющиеся строки не добавляются повторно.", [back_row(uid, f"adm_prod:{pid}")])
    if d.startswith("adm_delprod:"):
        if not is_admin(uid): return await alert(update, "⛔")
        pid = int(d[12:]); pr = one("SELECT section_id FROM products WHERE id=?", (pid,))
        if not pr: return await alert(update, "Товар уже удалён")
        sid = pr["section_id"]
        db.execute("DELETE FROM order_keys WHERE key_id IN (SELECT id FROM keys WHERE product_id=?)", (pid,))
        db.execute("DELETE FROM products WHERE id=?", (pid,)); db.execute("DELETE FROM keys WHERE product_id=?", (pid,))
        return await adm_sec(update, ctx, sid)
    if d.startswith("adm_delsec:"):
        sid = int(d[11:])
        if not is_admin(uid): return await alert(update, "⛔")
        db.execute("DELETE FROM order_keys WHERE key_id IN (SELECT id FROM keys WHERE product_id IN "
                   "(SELECT id FROM products WHERE section_id=?))", (sid,))
        db.execute("DELETE FROM keys WHERE product_id IN (SELECT id FROM products WHERE section_id=?)", (sid,))
        db.execute("DELETE FROM products WHERE section_id=?", (sid,))
        db.execute("DELETE FROM sections WHERE id=?", (sid,))
        return await adm_cat(update, ctx)
    if d.startswith("adm_treply:"):
        if not is_admin(uid): return await alert(update, "⛔")
        try: tid = int(d.split(":", 1)[1])
        except ValueError: return await alert(update, "Некорректный номер обращения")
        if not one("SELECT id FROM tickets WHERE id=?", (tid,)): return await alert(update, "Обращение не найдено")
        ctx.user_data["state"] = "adm_treply"
        ctx.user_data["sd"] = {"tid": tid}
        return await show(update, ctx, f"Введите ответ на обращение #{tid}:", [back_row(uid, "adm")])

    if d == "cfg_support":
        ctx.user_data["state"] = "cfg_support"
        current_support = cfg("support_username") or "zenit_support_bot"
        return await show(update, ctx, f"🆘 <b>Настройка поддержки</b>\n\nТекущая поддержка: <code>{esc(current_support)}</code>\n\nОтправьте @username или ссылку https://t.me/username:", [back_row(uid, "adm_cfg")])
    if d == "cfg_ref":
        ctx.user_data["state"] = "cfg_ref"; return await show(update, ctx, "Реф. процент (0-100):", [back_row(uid, "adm_cfg")])
    if d == "cfg_rub":
        ctx.user_data["state"] = "cfg_rub"; return await show(update, ctx, "Рублей за 1 звезду (например 1.7):", [back_row(uid, "adm_cfg")])
    if d == "cfg_platega":
        ctx.user_data["state"] = "cfg_platega_merchant"
        ctx.user_data.pop("platega_merchant_pending", None)
        return await show(update, ctx,
            "🏦 <b>Настройка Platega — шаг 1 из 2</b>\n\nОтправьте Merchant ID отдельным сообщением.",
            [back_row(uid, "adm_cfg")])
    if d == "cfg_methods":
        ctx.user_data["state"] = "cfg_methods"; return await show(update, ctx,
            "Методы через запятую (2=СБП,3=ЕРИП,11=Карта,12=Межд,14=SberPay):", [back_row(uid, "adm_cfg")])
    return await alert(update, "⚠️ Эта кнопка устарела. Откройте меню заново через /start.")


async def on_text(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id; txt = update.message.text or ""; st = ctx.user_data.get("state")
    if not st: return
    ctx.user_data["state"] = None
    if st.startswith(("adm_", "cfg_")) and not is_admin(uid):
        ctx.user_data.pop("sd", None)
        return await update.message.reply_text("⛔ Нет доступа.")
    if st in OWNER_TEXT_STATES and not is_owner(uid):
        return await update.message.reply_text("⛔ Только владелец.")
    if st == "review_comment":
        oid = ctx.user_data.pop("review_order_id", None)
        comment = "" if txt.strip() == "-" else txt.strip()[:1000]
        if oid:
            db.execute("UPDATE reviews SET comment=? WHERE order_id=? AND user_id=?", (comment, oid, uid))
        try:
            await update.message.delete()
        except TelegramError:
            pass
        try:
            await ctx.bot.send_message(uid, "✅ Спасибо! Отзыв добавлен." + ("\n💬 Комментарий сохранён." if comment else ""))
        except TelegramError:
            pass
        return
    if st in ("balance_topup_amount", "balance_topup_stars_amount"):
        stars = st == "balance_topup_stars_amount"
        unit = "⭐" if stars else "₽"
        try:
            amount = int(txt.strip())
        except ValueError:
            ctx.user_data["state"] = st
            return await update.message.reply_text(t(uid, "bal_amount_invalid", max=topup_max(stars), unit=unit))
        if not valid_topup_amount(amount, stars):
            ctx.user_data["state"] = st
            return await update.message.reply_text(t(uid, "bal_amount_range", unit=unit, max=topup_max(stars)))
        if stars:
            return await balance_topup_stars(update, ctx, amount)
        return await balance_topup_pay(update, ctx, amount)
    if st == "support":
        db.execute("INSERT INTO tickets(user_id,text,status,ts) VALUES(?,?,?,?)", (uid, txt, "open", now()))
        await update.message.reply_text(t(uid, "tk_sent"))
        for a in admin_ids():
            try:
                await ctx.bot.send_message(a, f"🎫 Новый тикет от {esc(uname(uid))}:\n{esc(txt)}",
                                           parse_mode="HTML",
                                           reply_markup=Markup([[Btn("💬 Ответить", callback_data=f"adm_treply:{one('SELECT MAX(id) m FROM tickets')['m']}")]]))
            except TelegramError: pass
        return
    if st == "search":
        res = q("SELECT * FROM products WHERE delivery_type IN ('key','file') AND name LIKE ? LIMIT 10", (f"%{txt}%",))
        if not res: return await update.message.reply_text(t(uid, "search_none"))
        rows = [[Btn(f"{p['name']} — {rub_amount(p, p['price'])} ₽", callback_data=f"prod:{p['id']}")] for p in res]
        rows.append(back_row(uid))
        return await update.message.reply_text("🔍 <b>Результаты поиска:</b>", parse_mode="HTML", reply_markup=Markup(rows))
    if st == "promo":
        p, err = promo_get(txt, uid)
        if err: return await update.message.reply_text(t(uid, err))
        if p["kind"] == "b":
            msg_, ok_ = activate_promo(uid, txt)
            await update.message.reply_text(msg_, parse_mode="HTML")
            return await render_checkout(update, ctx)
        co = ctx.user_data.get("co")
        if co: co["promo"] = p["id"]
        await update.message.reply_text(t(uid, "promo_ok"))
        return await render_checkout(update, ctx)
    if st == "profile_promo":
        msg_, ok_ = activate_promo(uid, txt)
        if not ok_: ctx.user_data["state"] = "profile_promo"
        return await update.message.reply_text(
            msg_, parse_mode="HTML",
            reply_markup=Markup([[Btn("⬅️ В профиль" if lang_of(uid) == "ru" else "⬅️ Profile", callback_data="prof")]]))
    if st == "adm_addadmin":
        if not is_owner(uid): return await update.message.reply_text(t(uid, "admin_only_owner"))
        try: new_id = int(txt.strip())
        except ValueError:
            ctx.user_data["state"] = "adm_addadmin"
            return await update.message.reply_text(t(uid, "admin_id_number"))
        if new_id <= 0:
            ctx.user_data["state"] = "adm_addadmin"
            return await update.message.reply_text(t(uid, "admin_id_positive"))
        db.execute("INSERT OR IGNORE INTO admins(id) VALUES(?)", (new_id,))
        await update.message.reply_text(f"✅ Администратор {new_id} добавлен.")
        return await adm_admins(update, ctx)
    if st == "adm_editprice":
        pid = ctx.user_data.get("sd", {}).get("pid")
        try: price = int(txt.strip())
        except ValueError:
            ctx.user_data["state"] = "adm_editprice"
            return await update.message.reply_text(t(uid, "price_integer"))
        if price < 0:
            ctx.user_data["state"] = "adm_editprice"
            return await update.message.reply_text("Цена не может быть отрицательной.")
        if not pid or not one("SELECT id FROM products WHERE id=?", (pid,)):
            return await update.message.reply_text("Товар не найден.")
        stars_price = max(1, math.ceil(price / star_rate())) if price > 0 else 0
        db.execute("UPDATE products SET price=?, price_rub=? WHERE id=?", (stars_price, price, pid))
        return await adm_prod(update, ctx, pid)
    if st == "adm_editorder":
        pid = ctx.user_data.get("sd", {}).get("pid")
        try:
            order_num = int(txt.strip())
            if order_num < 1: raise ValueError
        except ValueError:
            ctx.user_data["state"] = "adm_editorder"
            return await update.message.reply_text("Введите целое число от 1 и выше.")
        prod = one("SELECT id, section_id FROM products WHERE id=?", (pid,))
        if not prod: return await update.message.reply_text("Товар не найден.")
        db.execute("UPDATE products SET sort_order=? WHERE id=?", (order_num, pid))
        ctx.user_data.pop("state", None)
        return await adm_prod(update, ctx, pid)
    if st == "adm_editname":
        pid = ctx.user_data.get("sd", {}).get("pid")
        name = txt.strip()
        if not name:
            ctx.user_data["state"] = "adm_editname"
            return await update.message.reply_text("Название не может быть пустым. Попробуйте ещё раз.")
        if not pid or not one("SELECT id FROM products WHERE id=?", (pid,)):
            return await update.message.reply_text("Товар не найден.")
        db.execute("UPDATE products SET name=? WHERE id=?", (name[:200], pid))
        return await adm_prod(update, ctx, pid)
    if st == "adm_sec_name":
        name = txt.strip()
        if not name:
            ctx.user_data["state"] = "adm_sec_name"
            return await update.message.reply_text("Название не может быть пустым.")
        db.execute("INSERT INTO sections(name) VALUES(?)", (name[:200],))
        return await adm_cat(update, ctx)
    if st == "adm_editsec":
        sid = ctx.user_data.get("sd", {}).get("sid")
        name = txt.strip()
        if not name:
            ctx.user_data["state"] = "adm_editsec"
            return await update.message.reply_text("Название не может быть пустым.")
        db.execute("UPDATE sections SET name=? WHERE id=?", (name[:200], sid))
        return await adm_sec(update, ctx, sid)
    if st in ("adm_editdesc", "adm_editduration", "adm_editrubprice", "adm_editreplace"):
        pid = ctx.user_data.get("sd", {}).get("pid")
        prod = one("SELECT section_id FROM products WHERE id=?", (pid,))
        if not prod: return await update.message.reply_text("Товар не найден.")
        if st == "adm_editdesc":
            db.execute("UPDATE products SET description=? WHERE id=?", (txt[:3000], pid))
        else:
            try: value = int(txt.strip())
            except ValueError:
                ctx.user_data["state"] = st
                return await update.message.reply_text("Введите целое неотрицательное число.")
            if value < 0:
                ctx.user_data["state"] = st
                return await update.message.reply_text("Число не может быть отрицательным.")
            if st == "adm_editduration":
                db.execute("UPDATE products SET duration=? WHERE id=?", (value, pid))
            elif st == "adm_editreplace":
                db.execute("UPDATE products SET replace_days=? WHERE id=?", (min(value, 3650), pid))
            else:
                stars_price = max(1, math.ceil(value / star_rate())) if value > 0 else 0
                db.execute("UPDATE products SET price=?, price_rub=? WHERE id=?", (stars_price, value, pid))
        return await adm_prod(update, ctx, pid)
    if st == "adm_prod":
        if not is_admin(uid):
            return await update.message.reply_text("⛔ Нет доступа.")
        sid = (ctx.user_data.get("sd") or {}).get("sid")
        if not sid or not one("SELECT id FROM sections WHERE id=?", (sid,)):
            ctx.user_data["state"] = None
            ctx.user_data.pop("sd", None)
            return await update.message.reply_text("Раздел не найден. Откройте каталог в админ-панели и выберите раздел заново.")
        parts = [x.strip() for x in txt.split("|", 2)]
        if len(parts) != 3 or not parts[0] or not parts[1]:
            ctx.user_data["state"] = "adm_prod"
            return await update.message.reply_text(t(uid, "product_format"))
        name, price, desc = parts
        try:
            rub_price = int(price)
            if rub_price < 0 or len(name) > 200 or len(desc) > 3000:
                raise ValueError
        except ValueError:
            ctx.user_data["state"] = "adm_prod"
            return await update.message.reply_text("Проверьте формат: название до 200 символов, цена — целое число от 0, описание — до 3000 символов. Формат: Название | Цена в ₽ | Описание")
        try:
            stars_price = max(1, math.ceil(rub_price / star_rate())) if rub_price > 0 else 0
            next_order = one("SELECT COALESCE(MAX(sort_order),0)+1 AS n FROM products WHERE section_id=?", (sid,))["n"]
            db.execute("INSERT INTO products(section_id,name,description,price,price_rub,sort_order) VALUES(?,?,?,?,?,?)",
                       (sid, name, desc, stars_price, rub_price, next_order))
        except Exception:
            log.exception("Failed to add product to section %s", sid)
            ctx.user_data["state"] = "adm_prod"
            return await update.message.reply_text("❌ Не удалось сохранить товар из-за ошибки базы данных. Попробуйте ещё раз.")
        ctx.user_data["state"] = None
        ctx.user_data.pop("sd", None)
        return await adm_sec(update, ctx, sid)
    if st == "adm_keys":
        return await import_keys_text(update, ctx, txt)
    if st == "adm_promo_code":
        code = txt.strip().upper()
        if not code or " " in code or len(code) > 32:
            ctx.user_data["state"] = "adm_promo_code"
            return await update.message.reply_text("Код — одно слово до 32 символов. Введите код промокода:")
        if one("SELECT 1 FROM promos WHERE code=?", (code,)):
            ctx.user_data["state"] = "adm_promo_code"
            return await update.message.reply_text("Такой промокод уже есть. Введите другой код:")
        ctx.user_data["sd"] = {"code": code}
        ctx.user_data["state"] = "adm_promo_value"
        return await update.message.reply_text(
            f"Код: {code}\n\nТеперь тип и размер:\n"
            "10p — скидка 10%\n100r — скидка 100 ₽\n500b — бонус 500 ₽ на баланс (активируется в профиле)")
    if st == "adm_promo_value":
        sd = ctx.user_data.get("sd") or {}
        if not sd.get("code"): return await adm_promo(update, ctx)
        raw = txt.strip().lower()
        try:
            if raw[-1:] not in ("p", "r", "b", "s"): raise ValueError
            kind, val = raw[-1], int(raw[:-1])
            if val <= 0 or val > 1000000 or (kind == "p" and val > 100): raise ValueError
        except (ValueError, IndexError):
            ctx.user_data["state"] = "adm_promo_value"
            return await update.message.reply_text(
                f"Формат: 10p (процент от 1 до 100), 100r (₽ скидка) или 500b (₽ на баланс). "
                f"Код {sd['code']} сохранён — отправьте ещё раз:")
        sd["kind"], sd["val"] = kind, val
        ctx.user_data["sd"] = sd
        ctx.user_data["state"] = "adm_promo_limit"
        return await update.message.reply_text("Сколько раз можно использовать всего? Число или 0 — без лимита:")
    if st == "adm_promo_limit":
        sd = ctx.user_data.get("sd") or {}
        if not sd.get("code"): return await adm_promo(update, ctx)
        try:
            lim = int(txt.strip())
            if lim < 0 or lim > 10000000: raise ValueError
        except ValueError:
            ctx.user_data["state"] = "adm_promo_limit"
            return await update.message.reply_text("Нужно целое число от 0. Сколько раз можно использовать (0 — без лимита)?")
        sd["limit"] = lim
        ctx.user_data["sd"] = sd
        ctx.user_data["state"] = "adm_promo_days"
        return await update.message.reply_text("Сколько дней действует? Число дней или 0 — бессрочно:")
    if st == "adm_promo_days":
        sd = ctx.user_data.get("sd") or {}
        if not sd.get("code"): return await adm_promo(update, ctx)
        try:
            days = int(txt.strip())
            if days < 0 or days > 3650: raise ValueError
        except ValueError:
            ctx.user_data["state"] = "adm_promo_days"
            return await update.message.reply_text("Нужно целое число дней от 0 до 3650 (0 — бессрочно):")
        expires = now() + days * 86400 if days else 0
        try:
            db.execute("INSERT INTO promos(code,kind,value,max_uses,expires) VALUES(?,?,?,?,?)",
                       (sd["code"], sd["kind"], sd["val"], sd["limit"], expires))
        except sqlite3.IntegrityError:
            ctx.user_data["state"] = "adm_promo_code"
            return await update.message.reply_text("Такой промокод уже есть. Введите другой код:")
        ctx.user_data.pop("sd", None)
        await update.message.reply_text(
            f"✅ Промокод {sd['code']} создан: {promo_label({'kind': sd['kind'], 'value': sd['val']})}, "
            f"лимит {sd['limit'] or '∞'}, срок {str(days) + ' дн.' if days else 'бессрочно'}")
        return await adm_promo(update, ctx)
    if st == "adm_bc_text":
        sent = fail = 0
        for r in q("SELECT id FROM users WHERE banned=0"):
            try:
                await ctx.bot.send_message(r["id"], txt, parse_mode="HTML"); sent += 1
                await asyncio.sleep(0.05)
            except TelegramError: fail += 1
        return await update.message.reply_text(f"📢 Рассылка: {sent} ✅ / {fail} ❌")
    if st == "adm_treply":
        tid = ctx.user_data.get("sd", {}).get("tid")
        tk = one("SELECT * FROM tickets WHERE id=?", (tid,))
        if tk:
            await notify(ctx, [tk["user_id"]], t(tk["user_id"], "tk_reply", text=esc(txt)))
            db.execute("UPDATE tickets SET status='closed' WHERE id=?", (tid,))
        return await update.message.reply_text("✅ Отправлено")
    if st == "adm_secdesc":
        sid = ctx.user_data.get("sd", {}).get("sid")
        if not sid or not one("SELECT id FROM sections WHERE id=?", (sid,)):
            return await update.message.reply_text("Раздел не найден.")
        value = "" if txt.strip().upper() in ("СБРОС", "RESET") else txt.strip()[:1500]
        db.execute("UPDATE sections SET description=? WHERE id=?", (value, sid))
        await update.message.reply_text("✅ Описание раздела сохранено.")
        return await adm_sec(update, ctx, sid)
    if st == "adm_section_photo":
        sid = ctx.user_data.get("sd", {}).get("sid")
        if txt.strip().upper() == "УДАЛИТЬ ФОТО":
            if sid: db.execute("UPDATE sections SET photo=NULL WHERE id=?", (sid,))
            await update.message.reply_text("✅ Фото раздела удалено.")
            return await adm_sec(update, ctx, sid) if sid else await adm_cat(update, ctx)
        ctx.user_data["state"] = st
        return await update.message.reply_text("Отправьте фотографию или текст УДАЛИТЬ ФОТО.")
    if st == "adm_product_photo":
        pid = ctx.user_data.get("sd", {}).get("pid")
        if txt.strip().upper() == "УДАЛИТЬ ФОТО":
            if pid and one("SELECT id FROM products WHERE id=?", (pid,)):
                db.execute("UPDATE products SET photo=NULL WHERE id=?", (pid,))
            ctx.user_data["state"] = None
            await update.message.reply_text("✅ Фото товара удалено.")
            return await adm_prod(update, ctx, pid) if pid else await adm_cat(update, ctx)
        return await update.message.reply_text("Отправьте именно фотографию или текст «УДАЛИТЬ ФОТО».")
    if st == "adm_media_photo":
        key = (ctx.user_data.get("sd") or {}).get("key")
        if key not in ("catalog_text", "faq_text", "b_catalog", "b_faq"):
            return await update.message.reply_text("Экран не найден.")
        if txt.strip().upper() == "УДАЛИТЬ ФОТО":
            set_cfg(f"photo_{lang_of(uid)}_{key}", "")
            legacy_key = {"catalog_text": "b_catalog", "faq_text": "b_faq"}.get(key)
            if legacy_key:
                set_cfg(f"photo_{lang_of(uid)}_{legacy_key}", "")
            ctx.user_data["state"] = None
            await update.message.reply_text("✅ Фото удалено.")
            return await adm_cfg(update, ctx)
        ctx.user_data["state"] = st
        return await update.message.reply_text("Отправьте именно фотографию или текст «УДАЛИТЬ ФОТО».")
    if st == "adm_textedit":
        data = ctx.user_data.get("sd", {})
        lg, key = data.get("lang", "ru"), data.get("key", "")
        if key not in editable_text_keys():
            return await update.message.reply_text("Неизвестный текст.")
        if txt.strip().upper() == "УДАЛИТЬ ФОТО":
            set_cfg(f"photo_{lg}_{key}", "")
            await update.message.reply_text(t(uid, "photo_deleted"))
            return await adm_texts(update, ctx, lg, 0, data.get("group") if data.get("group") != "all" else None)
        if txt.strip().upper() in ("СБРОС", "RESET", "DEFAULT"):
            set_cfg(f"text_{lg}_{key}", "")
            await update.message.reply_text(t(uid, "text_reset"))
            return await adm_texts(update, ctx, lg, 0, data.get("group") if data.get("group") != "all" else None)
        if not txt.strip():
            ctx.user_data["state"] = "adm_textedit"
            return await update.message.reply_text(t(uid, "text_empty"))
        set_cfg(f"text_{lg}_{key}", txt[:4000])
        await update.message.reply_text(t(uid, "text_saved"))
        return await adm_texts(update, ctx, lg, 0, data.get("group") if data.get("group") != "all" else None)
    if st == "cfg_support":
        value = txt.strip()
        if value.startswith("https://t.me/"):
            username = value[len("https://t.me/"):].split("/", 1)[0].split("?", 1)[0]
        else:
            username = value.lstrip("@")
        if not re.fullmatch(r"[A-Za-z0-9_]{5,32}", username):
            ctx.user_data["state"] = "cfg_support"
            return await update.message.reply_text("❌ Отправьте корректный @username Telegram или ссылку https://t.me/username.")
        set_cfg("support_username", username)
        await update.message.reply_text(f"✅ Поддержка изменена: @{username}")
        return await adm_cfg(update, ctx)
    if st in ("cfg_ref", "cfg_rub", "cfg_methods"):
        if not is_owner(uid):
            return await update.message.reply_text("⛔ Только владелец.")
        raw = txt.strip().replace(",", ".")
        if st == "cfg_ref":
            if not raw.isdigit() or not 0 <= int(raw) <= 100:
                ctx.user_data["state"] = st
                return await update.message.reply_text("Нужно целое число от 0 до 100.")
            set_cfg("ref_percent", int(raw) if int(raw) else "0")
        elif st == "cfg_rub":
            try: v = float(raw)
            except ValueError: v = 0
            if not 0 < v <= 10000:
                ctx.user_data["state"] = st
                return await update.message.reply_text("Нужно число больше 0, например 1.7")
            set_cfg("rub_per_star", v)
        elif st == "cfg_methods":
            ids = [int(x) for x in re.split(r"[,\s]+", txt.strip()) if x.isdigit() and int(x) in PM_IDS]
            if not ids:
                ctx.user_data["state"] = st
                return await update.message.reply_text("Допустимые методы: " + ", ".join(map(str, PM_IDS)) + ". Пример: 2,11")
            set_cfg("platega_methods", ",".join(dict.fromkeys(map(str, ids))))
        return await adm_cfg(update, ctx)
    if st in ("cfg_platega_merchant", "cfg_platega_secret") and not is_owner(uid):
        return await update.message.reply_text("⛔ Только владелец.")
    if st == "cfg_platega_merchant":
        merchant = txt.strip()
        if not merchant or len(merchant.split()) != 1:
            ctx.user_data["state"] = "cfg_platega_merchant"
            return await update.message.reply_text(
                "❌ Merchant ID должен быть одним значением. Отправьте его ещё раз или нажмите «Назад»."
            )
        ctx.user_data["platega_merchant_pending"] = merchant
        ctx.user_data["state"] = "cfg_platega_secret"
        return await update.message.reply_text(
            "✅ Merchant ID принят.\n\nТеперь отправьте Secret отдельным сообщением. "
            "Он сохранится вместе с Merchant ID после ввода."
        )
    if st == "cfg_platega_secret":
        secret = txt.strip()
        merchant = ctx.user_data.get("platega_merchant_pending", "").strip()
        if not merchant:
            ctx.user_data["state"] = "cfg_platega_merchant"
            return await update.message.reply_text("Сначала введите Merchant ID.")
        if not secret or len(secret.split()) != 1:
            ctx.user_data["state"] = "cfg_platega_secret"
            return await update.message.reply_text("❌ Secret должен быть одним значением. Отправьте Secret ещё раз.")
        set_cfg("platega_merchant", merchant)
        set_cfg("platega_secret", secret)
        ctx.user_data.pop("platega_merchant_pending", None)
        await update.message.reply_text(
            "✅ Данные Platega сохранены. Это подтверждает сохранение настроек, но не проверяет их действительность."
        )
        return await adm_cfg(update, ctx)


async def on_database_document(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    if not is_admin(uid):
        return
    doc = update.message.document
    if not doc:
        return
    state = ctx.user_data.get("state")
    filename = (doc.file_name or "").lower()
    if state == "adm_keys":
        if not filename.endswith(".txt"):
            return await update.message.reply_text("❌ Для загрузки товара прикрепите файл .txt: одна строка — одна единица товара.")
        if doc.file_size and doc.file_size > MAX_KEYS_FILE_BYTES:
            return await update.message.reply_text("❌ Файл должен быть не больше 2 МБ. Разделите его на несколько .txt.")
        try:
            tg_file = await ctx.bot.get_file(doc.file_id)
            raw = bytes(await tg_file.download_as_bytearray())
            text = decode_keys_file(raw)
        except ValueError as e:
            return await update.message.reply_text(f"❌ {e}")
        except (TelegramError, OSError):
            log.exception("TXT download failed")
            return await update.message.reply_text("❌ Не удалось скачать файл. Прикрепите .txt ещё раз.")
        return await import_keys_text(update, ctx, text)
    if filename.endswith(".txt"):
        return await update.message.reply_text("Сначала откройте: Админ-панель → Разделы и товары → нужный товар → ➕ Ключи. Затем прикрепите .txt.")


    if (is_admin(uid) and state == "adm_textedit" and
            (doc.mime_type or "").lower().startswith("image/") and
            (doc.file_name or "").lower().endswith((".jpg", ".jpeg", ".png", ".webp"))):
        data = ctx.user_data.get("sd", {})
        lg, key = data.get("lang", "ru"), data.get("key", "")
        if key not in editable_text_keys():
            return await update.message.reply_text("Сначала выберите текст в редакторе.")
        try:
            tg_file = await ctx.bot.get_file(doc.file_id)
            raw = bytes(await tg_file.download_as_bytearray())
            if not raw:
                return await update.message.reply_text("❌ Не удалось прочитать изображение. Отправьте его как обычную фотографию.")
            sent = await ctx.bot.send_photo(chat_id=uid, photo=raw)
            photo_id = sent.photo[-1].file_id
            set_cfg(f"photo_{lg}_{key}", photo_id)
            try:
                await sent.delete()
            except TelegramError:
                pass
            ctx.user_data["state"] = None
            await update.message.reply_text("✅ Фото сохранено. Изображение, отправленное как файл, преобразовано в фотографию для совместимости с Telegram.")
            return await adm_texts(update, ctx, lg, 0, data.get("group") if data.get("group") != "all" else None)
        except (TelegramError, OSError) as e:
            log.warning("Не удалось обработать изображение из документа: %s", e)
            return await update.message.reply_text("❌ Не удалось сохранить это изображение. Попробуйте отправить его как обычную фотографию (не как файл).")
    if not (doc.file_name or "").lower().endswith((".db", ".sqlite", ".sqlite3")):
        return
    if not is_owner(uid):
        return await update.message.reply_text("⛔ Импорт базы доступен только владельцу.")
    try:
        tg_file = await ctx.bot.get_file(doc.file_id)
        raw = bytes(await tg_file.download_as_bytearray())
        if not raw:
            return await update.message.reply_text("❌ Файл пустой.")
        incoming = sqlite3.connect(":memory:")
        try:
            incoming.deserialize(raw)
            integrity = incoming.execute("PRAGMA integrity_check").fetchone()
            if not integrity or integrity[0] != "ok":
                return await update.message.reply_text("❌ База повреждена. Текущие данные не изменены.")
            tables = {r[0] for r in incoming.execute(
                "SELECT name FROM sqlite_master WHERE type='table'"
            ).fetchall()}
            required = {"settings", "users", "sections", "products", "keys", "orders"}
            if not required.issubset(tables):
                missing = ", ".join(sorted(required - tables))
                return await update.message.reply_text(
                    f"❌ Это не база этого бота: отсутствуют таблицы {missing}. Текущие данные не изменены."
                )

            incoming.row_factory = sqlite3.Row
            init_db(incoming)
            reference = sqlite3.connect(":memory:")
            try:
                reference.executescript(SCHEMA)
                expected_tables = [r[0] for r in reference.execute(
                    "SELECT name FROM sqlite_master WHERE type='table' AND name!='sqlite_sequence'")]
                for table in expected_tables:
                    expected = {r[1] for r in reference.execute(f"PRAGMA table_info({table})")}
                    actual = {r[1] for r in incoming.execute(f"PRAGMA table_info({table})")}
                    if not expected.issubset(actual):
                        return await update.message.reply_text(
                            f"❌ Несовместимая структура таблицы {table}. Текущие данные не изменены.")
            finally:
                reference.close()
            incoming.commit()

            incoming.backup(db)
            LANG.clear()
        finally:
            incoming.close()
        ctx.user_data["state"] = None
        ctx.user_data.pop("sd", None)
        await update.message.reply_text(
            "✅ База данных импортирована. Настройки, приветствие, товары, ключи и записи заменены данными из файла. "
            "Перезапуск не требуется — бот продолжит работать с новой базой."
        )
    except Exception:
        log.exception("Database import failed")
        await update.message.reply_text(
            "❌ Не удалось импортировать базу. Проверь, что это экспорт shop.db от этого бота. "
            "Текущая база не должна измениться при ошибке проверки."
        )

async def on_photo(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    if not is_admin(uid):
        return
    if ctx.user_data.get("state") == "adm_section_photo":
        sid = ctx.user_data.get("sd", {}).get("sid")
        if not sid or not one("SELECT id FROM sections WHERE id=?", (sid,)):
            ctx.user_data["state"] = None
            return await update.message.reply_text("Раздел не найден. Откройте его в админке заново.")
        db.execute("UPDATE sections SET photo=? WHERE id=?", (update.message.photo[-1].file_id, sid))
        ctx.user_data["state"] = None
        await update.message.reply_text("✅ Фото раздела сохранено.")
        return await adm_sec(update, ctx, sid)
    if ctx.user_data.get("state") == "adm_product_photo":
        data = ctx.user_data.get("sd", {})
        pid = data.get("pid")
        if not pid or not one("SELECT id FROM products WHERE id=?", (pid,)):
            ctx.user_data["state"] = None
            return await update.message.reply_text("Товар не найден. Откройте его в админке заново.")
        db.execute("UPDATE products SET photo=? WHERE id=?", (update.message.photo[-1].file_id, pid))
        ctx.user_data["state"] = None
        await update.message.reply_text("✅ Фото товара сохранено.")
        return await adm_prod(update, ctx, pid)
    if ctx.user_data.get("state") == "adm_media_photo":
        key = (ctx.user_data.get("sd") or {}).get("key")
        if key not in ("catalog_text", "faq_text", "b_catalog", "b_faq"):
            return await update.message.reply_text("Экран не найден.")
        photo_id = update.message.photo[-1].file_id
        set_cfg(f"photo_{lang_of(uid)}_{key}", photo_id)
        ctx.user_data["state"] = None
        await update.message.reply_text("✅ Фото сохранено.")
        return await adm_cfg(update, ctx)
    if ctx.user_data.get("state") != "adm_textedit":
        return
    data = ctx.user_data.get("sd", {})
    lg, key = data.get("lang", "ru"), data.get("key", "")
    if key not in editable_text_keys():
        return await update.message.reply_text("Сначала выберите текст в админке.")
    photo_id = update.message.photo[-1].file_id
    set_cfg(f"photo_{lg}_{key}", photo_id)
    ctx.user_data["state"] = None
    await update.message.reply_text("✅ Фото сохранено для этого текста. Чтобы заменить или удалить его, снова открой редактирование этого текста в админке.")
    return await adm_texts(update, ctx, lg, 0, data.get("group") if data.get("group") != "all" else None)


async def on_ticket_reply_help(update, ctx):
    d = update.callback_query.data
    _, tid = d.split(":")
    ctx.user_data["state"] = "adm_treply"; ctx.user_data["sd"] = {"tid": int(tid)}
    await update.callback_query.answer()
    await update.callback_query.message.reply_text("Введите ответ:")

async def on_error(update, ctx):
    err = ctx.error
    log.exception("Unhandled bot error", exc_info=err)
    if isinstance(update, Update) and update.callback_query:
        try:
            await update.callback_query.answer("⚠️ Ошибка. Попробуйте ещё раз.", show_alert=True)
        except TelegramError:
            pass


async def post_init(app):

    await app.bot.set_my_commands([
        BotCommand("start", "Главное меню"),
        BotCommand("cancel", "Отменить действие"),
    ])

    app.bot_data["bg_task"] = asyncio.create_task(bg_loop(app))

async def post_shutdown(app):
    task = app.bot_data.get("bg_task")
    if task: task.cancel()

def main():
    if not BOT_TOKEN or not ADMIN_IDS:
        print("Заполните BOT_TOKEN и ADMIN_IDS в config.env. Инструкция — README.md.")
        return
    app = Application.builder().token(BOT_TOKEN).post_init(post_init).post_shutdown(post_shutdown).build()
    app.add_handler(TypeHandler(Update, guard), group=-1)
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("cancel", cancel))
    app.add_handler(CommandHandler("fixtexts", fixtexts))
    app.add_handler(PreCheckoutQueryHandler(precheckout))
    app.add_handler(MessageHandler(filters.SUCCESSFUL_PAYMENT, paid))
    app.add_handler(CallbackQueryHandler(on_cb))
    app.add_handler(MessageHandler(filters.Document.ALL, on_database_document))
    app.add_handler(MessageHandler(filters.PHOTO, on_photo))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.add_error_handler(on_error)
    log.info("Bot started")
    app.run_polling(allowed_updates=Update.ALL_TYPES)


DELIVERY_TYPES = {"key": "🔑 Ключи", "file": "📁 Файл"}

def delivery_data(p):
    try: data=json.loads(p["delivery_config"] or "{}")
    except (ValueError, TypeError): return {}
    return data if isinstance(data,dict) else {}

def delivery_ready(p):
    if p["delivery_type"] == "key": return True
    if p["delivery_type"] == "file":
        file_id=delivery_data(p).get("file_id")
        return isinstance(file_id,str) and bool(file_id)
    return False

def role_of(uid):
    if is_owner(uid): return "owner"
    row = one("SELECT role FROM admins WHERE id=?", (uid,))
    return row["role"] if row else "user"

def allowed_admin(uid, action):
    role = role_of(uid)
    if role == "owner": return True
    if action.startswith("apbad:"): return False
    if role == "support":
        return action=="adm" or action.startswith("adm_treply")
    if role == "manager":
        return action in ("adm", "adm_cat", "adm_keys", "adm_reviews") or action.startswith((
            "adm_sec", "adm_prod", "adm_keys:", "adm_addsec", "adm_addprod:", "adm_addkeys:",
            "adm_delkey:", "adm_delprod:", "adm_delsec:", "adm_edit", "adm_pin:",
            "ext:config", "ext:type", "ext:setup", "ext:threshold"))
    return False

_old_guard = guard
async def guard(update, ctx):
    ACTOR.set(update.effective_user.id if update.effective_user else 0)
    await _old_guard(update, ctx)

_old_adm_rows = adm_rows
def adm_rows(uid):
    rows = _old_adm_rows(uid)
    if is_owner(uid):
        rows.insert(-1, [Btn("🧾 Журнал действий", callback_data="ext:audit:0"),
                          Btn("👥 Роли", callback_data="ext:roles")])
        rows.insert(-1, [Btn("📈 Отчёты", callback_data="ext:stats"),
                          Btn("💾 Бэкап сейчас", callback_data="ext:backup")])
    return [[b for b in row if not b.callback_data or b.callback_data == "home" or
             allowed_admin(uid, b.callback_data)] for row in rows
            if any(not b.callback_data or b.callback_data == "home" or allowed_admin(uid,b.callback_data) for b in row)]


_old_on_cb = on_cb
async def on_cb(update, ctx):
    d = update.callback_query.data or ""
    uid = update.effective_user.id
    admin_action = d.startswith(("adm", "cfg_", "apbad:", "ext:config", "ext:type", "ext:setup",
                                "ext:threshold", "ext:roles", "ext:role:",
                                "ext:audit", "ext:stats", "ext:backup"))
    if admin_action and not allowed_admin(uid, d): return await alert(update, "⛔ Недостаточно прав")
    if d.startswith(("adm_addkeys:","adm_keys:","adm_editreplace:","adm_delkey:")):
        try: pid=int(d.split(":")[-1])
        except (ValueError,IndexError): return await alert(update,"Некорректная кнопка")
        if not one("SELECT 1 FROM products WHERE id=? AND delivery_type='key'",(pid,)):
            return await alert(update,"Для этого товара доступны только настройки файла")
    if d.startswith("ext:"):
        ctx.user_data.pop("state", None); ctx.user_data.pop("sd", None)
        try: return await extension_callback(update, ctx, d, uid)
        except (ValueError, KeyError, IndexError): return await alert(update, "Некорректные данные")
    return await _old_on_cb(update, ctx)

async def extension_callback(update, ctx, d, uid):
    parts = d.split(":")
    action = parts[1]
    if action == "purchases": return await my_orders(update,ctx,max(0,int(parts[2])))
    if action == "favorite":
        pid = int(parts[2])
        if not one("SELECT id FROM products WHERE id=?", (pid,)): return await alert(update, "Товар удалён")
        if one("SELECT 1 FROM favorites WHERE user_id=? AND product_id=?", (uid,pid)):
            db.execute("DELETE FROM favorites WHERE user_id=? AND product_id=?", (uid,pid))
            return await alert(update, "Убрано из избранного")
        db.execute("INSERT INTO favorites VALUES(?,?)", (uid,pid))
        return await alert(update, "Добавлено в избранное ❤️")
    if action == "favorites":
        rows = [[Btn(p["name"][:60], callback_data=f"prod:{p['id']}")] for p in q(
            "SELECT p.* FROM products p JOIN favorites f ON f.product_id=p.id WHERE f.user_id=? AND p.delivery_type IN ('key','file') LIMIT 50", (uid,))]
        return await show(update, ctx, "❤️ Избранное" if rows else "Пока ничего нет — добавьте товар из его карточки.", rows+[back_row(uid,"prof")])
    if action in ("ledger", "audit"):
        page = max(0,int(parts[2])); size = 10
        if action == "ledger":
            rows = q("SELECT * FROM balance_history WHERE user_id=? ORDER BY id DESC LIMIT 11 OFFSET ?", (uid,page*size))
            lines = [f"{fmt_date(r['ts'])} · {esc(r['reason'])}: {r['delta']:+} ₽ → {r['balance_after']} ₽" for r in rows[:size]]
            title = "💳 История баланса"
        else:
            rows = q("SELECT * FROM audit_log ORDER BY id DESC LIMIT 11 OFFSET ?", (page*size,))
            lines = [f"{fmt_date(r['ts'])} · {r['actor'] or 'система'} · {r['entity']} #{r['entity_id']} · {r['action']}" for r in rows[:size]]
            title = "🧾 Журнал действий"
        nav=[]
        if page: nav.append(Btn("⬅️",callback_data=f"ext:{action}:{page-1}"))
        if len(rows)>size: nav.append(Btn("➡️",callback_data=f"ext:{action}:{page+1}"))
        return await show(update,ctx, title+"\n\n"+"\n".join(lines or ["Записей пока нет."]), ([nav] if nav else [])+[back_row(uid,"prof" if action=="ledger" else "adm")])
    if action == "config":
        pid=int(parts[2]); p=one("SELECT * FROM products WHERE id=?", (pid,))
        if not p: return await alert(update,"Товар удалён")
        rows=[[Btn(label,callback_data=f"ext:type:{pid}:{kind}")] for kind,label in DELIVERY_TYPES.items()]
        if p["delivery_type"]=="file": rows.append([Btn("📁 Загрузить файлы",callback_data=f"ext:setup:{pid}")])
        if p["delivery_type"] in DELIVERY_TYPES: rows.append([Btn("🔔 Порог остатка",callback_data=f"ext:threshold:{pid}")])
        rows.append(back_row(uid,f"adm_prod:{pid}"))
        text=f"📦 {esc(p['name'])}\nТип: {DELIVERY_TYPES.get(p['delivery_type'], 'Не настроен')}\nГотов к продаже: {'да' if stock(pid)>0 else 'нет'}"
        if p["delivery_type"] in DELIVERY_TYPES: text+=f"\nПорог остатка: {p['low_threshold']}"
        return await show(update,ctx,text,rows)
    if action == "type":
        pid=int(parts[2]); kind=parts[3]
        if kind not in DELIVERY_TYPES: raise ValueError()
        current=one("SELECT delivery_type FROM products WHERE id=?",(pid,))
        if not current: raise ValueError()
        if current["delivery_type"] != kind:
            db.execute("UPDATE products SET delivery_type=?,delivery_config='{}',replace_days=0 WHERE id=?",(kind,pid))
        return await extension_callback(update,ctx,f"ext:config:{pid}",uid)
    if action in ("setup","threshold"):
        pid=int(parts[2]); p=one("SELECT * FROM products WHERE id=?",(pid,))
        if not p or p["delivery_type"] not in DELIVERY_TYPES: raise ValueError()
        upload=action=="setup" and p["delivery_type"]=="file"
        ctx.user_data.update(state="ext_config",sd={"pid":pid,"kind":"file" if upload else "threshold"})
        prompt="Прикрепите документы по одному. /cancel — завершить загрузку." if upload else "Порог остатка: от 0 до 10000. 0 — выключить."
        return await show(update,ctx,prompt,[back_row(uid,f"ext:config:{pid}")])
    if action == "roles":
        rows=[[Btn(f"{r['id']}: {r['role']}",callback_data=f"ext:role:{r['id']}")] for r in q("SELECT * FROM admins")]
        return await show(update,ctx,"👥 Роли. Владелец задаётся только через ADMIN_IDS. Нового сотрудника добавьте в прежнем разделе «Админы».",rows+[back_row(uid,"adm")])
    if action == "role":
        aid=int(parts[2])
        if len(parts)==4:
            if parts[3] not in ("manager","support"): raise ValueError()
            db.execute("UPDATE admins SET role=? WHERE id=?",(parts[3],aid))
            return await extension_callback(update,ctx,"ext:roles",uid)
        return await show(update,ctx,f"Роль сотрудника {aid}",[[Btn("Менеджер",callback_data=f"ext:role:{aid}:manager"),Btn("Поддержка",callback_data=f"ext:role:{aid}:support")],[back_row(uid,"ext:roles")]])
    if action == "backup":
        path=create_backup(force=True)
        return await show(update,ctx,f"💾 Резервная копия готова\n<code>backups/{esc(path.name)}</code>",[back_row(uid,"adm")])
    if action == "stats":
        lines=["📈 Продажи (без возвращённых заказов)"]
        for label,days in (("24 часа",1),("7 дней",7),("30 дней",30)):
            r=one("SELECT COUNT(*) n,COALESCE(SUM(CASE WHEN method='balance' THEN rub ELSE rub+stars*?+bal_used END),0) revenue FROM orders WHERE refunded=0 AND ts>=?",(star_rate(),now()-days*86400))
            lines.append(f"{label}: {r['n']} заказов · {r['revenue']:.2f} ₽")
        repeat=one("SELECT COUNT(*) n FROM (SELECT payer FROM orders WHERE refunded=0 GROUP BY payer HAVING COUNT(*)>1)")["n"]
        lines.append(f"Повторных покупателей: {repeat}\n\nПопулярные товары:")
        for r in q("SELECT product_name,COUNT(*) n FROM orders WHERE refunded=0 GROUP BY product_id ORDER BY n DESC LIMIT 5"):
            lines.append(f"{esc(r['product_name'])} — {r['n']}")
        lines.append("\nРубли + Stars по текущему курсу + списанный баланс; это оборот, не прибыль.")
        return await show(update,ctx,"\n".join(lines),[back_row(uid,"adm")])
    raise ValueError()


_old_text = on_text
async def on_text(update,ctx):
    uid=update.effective_user.id; st=ctx.user_data.get("state","") or ""
    if st.startswith(("adm", "cfg_")) and not allowed_admin(uid,st):
        ctx.user_data.clear(); return await update.message.reply_text("⛔ Недостаточно прав")
    if not st.startswith("ext_"): return await _old_text(update,ctx)
    sd=ctx.user_data.get("sd",{})
    if st != "ext_config" or sd.get("kind") not in ("file","key","threshold"):
        ctx.user_data.pop("state",None); ctx.user_data.pop("sd",None)
        return await update.message.reply_text("Действие больше недоступно. Откройте /start.")
    if not allowed_admin(uid,"ext:config"): return
    if sd["kind"]=="file": return await update.message.reply_text("Прикрепите файл документом.")
    try:
        threshold=int((update.message.text or "").strip())
        if not 0<=threshold<=10000: raise ValueError()
    except ValueError: return await update.message.reply_text("Порог: целое число от 0 до 10000.")
    db.execute("UPDATE products SET low_threshold=?,low_notified=0 WHERE id=? AND delivery_type IN ('key','file')",(threshold,sd.get('pid')))
    ctx.user_data.pop("state",None); ctx.user_data.pop("sd",None)
    return await adm_prod(update,ctx,sd['pid'])

_old_document=on_database_document
async def on_database_document(update,ctx):
    uid=update.effective_user.id; st=ctx.user_data.get("state","") or ""
    doc=update.message.document
    if st.startswith("ext_") and st!="ext_config":
        ctx.user_data.pop("state",None); ctx.user_data.pop("sd",None)
        return await update.message.reply_text("Действие больше недоступно. Откройте /start.")
    if st=="ext_config":
        sd=ctx.user_data.get("sd",{})
        if sd.get("kind")!="file" or not allowed_admin(uid,"ext:config"): return
        if not one("SELECT 1 FROM products WHERE id=? AND delivery_type='file'",(sd['pid'],)):
            return await update.message.reply_text("Товар недоступен.")
        unique=doc.file_unique_id
        if one("SELECT 1 FROM keys WHERE product_id=? AND kind=?",(sd['pid'],'file:'+unique)):
            return await update.message.reply_text("Этот файл уже загружен.")
        db.execute("INSERT INTO keys(product_id,value,kind) VALUES(?,?,?)",(sd['pid'],doc.file_id,'file:'+unique))
        return await update.message.reply_text("✅ Файл добавлен на склад. Можно отправить следующий или /cancel.")
    if not is_owner(uid) and not (st=="adm_keys" and allowed_admin(uid,"adm_addkeys:")): return
    return await _old_document(update,ctx)

_old_photo=on_photo
async def on_photo(update,ctx):
    st=ctx.user_data.get("state","") or ""
    if not allowed_admin(update.effective_user.id,st): return
    return await _old_photo(update,ctx)

_old_deliver=deliver_order
async def deliver_order(ctx,chat_id,o,head=None):
    if o['refunded']: return await send(ctx,chat_id,"Этот заказ возвращён.")
    if o['delivery_type']=="key":
        await _old_deliver(ctx,chat_id,o,head)
    elif o['delivery_type']=="file":
        file_id=o['key_value']
        if file_id=="Файл": file_id=delivery_data(o).get('file_id')
        if not file_id: return await send(ctx,chat_id,"Файл недоступен. Обратитесь в поддержку.")
        await ctx.bot.send_document(chat_id=chat_id,document=file_id,caption=f"📦 #{o['id']} · {o['product_name']}"[:1024])
    else:
        return await send(ctx,chat_id,"Архивный заказ. Обратитесь в поддержку с его номером.")
    await send(ctx,chat_id,"🛍 Нужен ещё один?",Markup([[Btn("Купить повторно",callback_data=f"prod:{o['product_id']}")]]))

def create_backup(force=False):
    folder=pathlib.Path(BASE_DIR)/'backups'; folder.mkdir(mode=0o700,exist_ok=True)
    stamp=datetime.now(timezone.utc).strftime('%Y-%m-%d')
    path=folder/f'shop-{stamp}.db'
    if path.exists() and not force: return path
    tmp=folder/f'.{stamp}.tmp'
    with closing(sqlite3.connect(tmp)) as dest: db.backup(dest)
    os.chmod(tmp,0o600); os.replace(tmp,path)
    for old in sorted(folder.glob('shop-*.db'),reverse=True)[7:]: old.unlink()
    return path

async def extension_tick(app):
    ACTOR.set(0)
    await asyncio.to_thread(create_backup_threadsafe)
    for p in q("SELECT * FROM products WHERE delivery_type IN ('key','file') AND low_threshold>0"):
        n=stock(p['id'])
        if n>p['low_threshold']:
            if p['low_notified']: db.execute("UPDATE products SET low_notified=0 WHERE id=?",(p['id'],))
        elif not p['low_notified']:
            await notify(app,list(ADMIN_IDS),f"📦 Мало товара: {esc(p['name'])} — осталось {n}.")
            db.execute("UPDATE products SET low_notified=1 WHERE id=?",(p['id'],))


def create_backup_threadsafe():

    folder=pathlib.Path(BASE_DIR)/'backups'; folder.mkdir(mode=0o700,exist_ok=True)
    path=folder/f"shop-{datetime.now(timezone.utc).strftime('%Y-%m-%d')}.db"
    if path.exists(): return
    tmp=folder/'.daily.tmp'
    with closing(sqlite3.connect(DB_FILE)) as source, closing(sqlite3.connect(tmp)) as dest: source.backup(dest)
    os.chmod(tmp,0o600); os.replace(tmp,path)
    for old in sorted(folder.glob('shop-*.db'),reverse=True)[7:]: old.unlink()

async def extension_loop(app):
    while True:
        try: await extension_tick(app)
        except asyncio.CancelledError: raise
        except Exception: log.exception("Shop maintenance failed")
        await asyncio.sleep(60)

_old_post_init=post_init
async def post_init(app):
    await _old_post_init(app)
    app.bot_data['shop_task']=asyncio.create_task(extension_loop(app))

_old_post_shutdown=post_shutdown
async def post_shutdown(app):
    task=app.bot_data.get('shop_task')
    if task:
        task.cancel()
        try: await task
        except asyncio.CancelledError: pass
    await _old_post_shutdown(app)
    bg=app.bot_data.get('bg_task')
    if bg:
        try: await bg
        except asyncio.CancelledError: pass
    create_backup(force=True)
    db.close()

if __name__ == '__main__':
    main()
