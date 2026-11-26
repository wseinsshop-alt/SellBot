import asyncio
import importlib.util
import os
from pathlib import Path
import shutil
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import AsyncMock, patch


SOURCE = Path(__file__).resolve().parents[1] / "main" / "main.py"


class SimulatedPowerLoss(BaseException):
    pass


class ShopTests(unittest.IsolatedAsyncioTestCase):
    def load_shop(self):
        spec = importlib.util.spec_from_file_location("shop_under_test", self.source)
        shop = importlib.util.module_from_spec(spec)
        with patch.dict(os.environ, {}, clear=True):
            spec.loader.exec_module(shop)
        shop.platega_post = AsyncMock(side_effect=AssertionError("Unexpected gateway request"))
        shop.platega_get = AsyncMock(side_effect=AssertionError("Unexpected gateway request"))
        return shop

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        (root / "main").mkdir()
        self.source = root / "main" / "main.py"
        shutil.copyfile(SOURCE, self.source)
        (root / "config.env").write_text("BOT_TOKEN=123456:dummy-test-value\nADMIN_IDS=999\n", encoding="utf-8")
        self.shop = self.load_shop()
        self.addCleanup(lambda: self.shop.db.close())
        self.shop.db.executemany("INSERT INTO users(id,name,balance) VALUES(?,?,?)",
                                 [(1, "buyer", 40), (2, "other", 0)])
        self.shop.db.execute("INSERT INTO sections(id,name) VALUES(1,'test')")
        self.shop.db.execute("INSERT INTO products(id,section_id,name,price,price_rub) VALUES(1,1,'test',100,100)")
        self.shop.db.executemany("INSERT INTO keys(product_id,value) VALUES(1,?)",
                                 [("KEY-A",), ("KEY-B",), ("KEY-C",)])
        self.bot = SimpleNamespace(username="test_bot", send_message=AsyncMock(),
                                   send_document=AsyncMock(), send_invoice=AsyncMock(),
                                   set_my_commands=AsyncMock())
        self.ctx = SimpleNamespace(user_data={"co": {"pid": 1, "promo": None}}, bot=self.bot)
        self.message = SimpleNamespace(text="100", reply_text=AsyncMock(), from_user=SimpleNamespace(id=1))
        self.update = SimpleNamespace(effective_user=SimpleNamespace(id=1, username="buyer"),
                                      callback_query=None, message=self.message,
                                      effective_message=self.message, effective_chat=SimpleNamespace(id=1))
        self.shop.set_cfg("platega_merchant", "test-merchant")
        self.shop.set_cfg("platega_secret", "test-secret")
        self.shop.set_cfg("platega_methods", "2")
        self.shop.show = AsyncMock()
        self.shop.send = AsyncMock()
        self.shop.notify = AsyncMock()
        self.shop.deliver_order = AsyncMock()

    def promo(self, max_uses=1):
        self.shop.db.execute("INSERT INTO promos(id,code,kind,value,max_uses) VALUES(1,'ONCE','p',50,?)", (max_uses,))
        self.ctx.user_data["co"]["promo"] = 1

    async def create(self, tid="payment-1"):
        self.shop.platega_post = AsyncMock(return_value={"transactionId": tid, "redirect": "https://example.invalid/pay"})
        await self.shop.create_platega_order(self.update, self.ctx)

    async def confirm(self, tid="payment-1"):
        self.shop.platega_get = AsyncMock(return_value={"status": "CONFIRMED"})
        return await self.shop.check_payment(self.ctx, tid)

    def test_root_config_and_environment_override(self):
        self.assertEqual(self.shop.BOT_TOKEN, "123456:dummy-test-value")
        self.assertEqual(self.shop.ADMIN_IDS, {999})
        with patch.dict(os.environ, {"BOT_TOKEN": "environment-token", "ADMIN_IDS": "123"}, clear=True):
            self.shop._load_env()
            self.assertEqual(os.environ["BOT_TOKEN"], "environment-token")
            self.assertEqual(os.environ["ADMIN_IDS"], "123")

    def test_local_config_stays_compatible(self):
        (self.source.parent / "config.env").write_text("BOT_TOKEN=local-token\nADMIN_IDS=456\n", encoding="utf-8")
        with patch.dict(os.environ, {}, clear=True):
            self.shop._load_env()
            self.assertEqual(os.environ["BOT_TOKEN"], "local-token")
            self.assertEqual(os.environ["ADMIN_IDS"], "456")

    def test_external_data_directory_and_backup(self):
        data = Path(self.temp.name) / "private-data"
        spec = importlib.util.spec_from_file_location("external_shop", self.source)
        external = importlib.util.module_from_spec(spec)
        with patch.dict(os.environ, {"SELLBOT_DATA_DIR": str(data)}, clear=True):
            spec.loader.exec_module(external)
        try:
            self.assertEqual(Path(external.DB_FILE), data / "shop.db")
            self.assertTrue((data / "shop.db").exists())
            self.assertEqual(external.create_backup(force=True).parent, data / "backups")
        finally:
            external.db.close()

    def test_telegram_token_redacted_from_log_messages_and_exceptions(self):
        import logging
        token = self.shop.BOT_TOKEN
        record = logging.LogRecord("httpx", logging.ERROR, __file__, 1,
                                   "POST https://api.telegram.org/bot%s/getMe", (token,), None)
        self.shop.SecretFilter().filter(record)
        self.assertNotIn(token, record.getMessage())
        self.assertIn("[BOT_TOKEN]", record.getMessage())
        try:
            raise RuntimeError("request failed: " + token)
        except RuntimeError:
            import sys
            record = logging.LogRecord("shop", logging.ERROR, __file__, 1, "error", (), sys.exc_info())
        self.shop.SecretFilter().filter(record)
        self.assertNotIn(token, record.exc_text)

    async def test_reserve_and_payment_are_durable_before_gateway_call(self):
        async def gateway(body):
            row = self.shop.one("SELECT * FROM payments WHERE status='creating'")
            self.assertIsNotNone(row)
            self.assertEqual(row["bal_used"], 40)
            self.assertEqual(self.shop.balance(1), 0)
            self.assertFalse(self.shop.db.in_transaction)
            return {"transactionId": "payment-1", "redirect": "https://example.invalid/pay"}
        self.shop.platega_post = AsyncMock(side_effect=gateway)
        await self.shop.create_platega_order(self.update, self.ctx)
        row = self.shop.one("SELECT * FROM payments")
        self.assertEqual((row["id"], row["status"], row["reserved"]), ("payment-1", "pending", 1))

    async def test_cancel_returns_reserve_once(self):
        self.shop.platega_post = AsyncMock(side_effect=asyncio.CancelledError)
        with self.assertRaises(asyncio.CancelledError):
            await self.shop.create_platega_order(self.update, self.ctx)
        self.assertEqual(self.shop.balance(1), 40)
        row = self.shop.one("SELECT * FROM payments")
        self.assertEqual((row["status"], row["reserved"]), ("canceled", 0))
        self.shop.release_pending(row["id"], "canceled")
        self.assertEqual(self.shop.balance(1), 40)

    async def test_restart_recovers_interrupted_creation_once(self):
        self.shop.platega_post = AsyncMock(side_effect=SimulatedPowerLoss)
        with self.assertRaises(SimulatedPowerLoss):
            await self.shop.create_platega_order(self.update, self.ctx)
        self.assertEqual(self.shop.balance(1), 0)
        self.shop.db.close()
        self.shop = self.load_shop()
        self.shop.recover_stuck(startup=True)
        self.shop.recover_stuck(startup=True)
        self.assertEqual(self.shop.balance(1), 40)
        self.assertEqual(self.shop.one("SELECT status FROM payments")["status"], "canceled")

    async def test_gateway_error_returns_reserve(self):
        self.shop.platega_post = AsyncMock(side_effect=RuntimeError("gateway unavailable"))
        await self.shop.create_platega_order(self.update, self.ctx)
        self.assertEqual(self.shop.balance(1), 40)
        self.message.reply_text.assert_awaited_once()
        self.assertEqual(self.shop.one("SELECT status FROM payments")["status"], "canceled")

    async def test_incomplete_gateway_response_returns_reserve(self):
        self.shop.platega_post = AsyncMock(return_value={"transactionId": "incomplete"})
        await self.shop.create_platega_order(self.update, self.ctx)
        self.assertEqual(self.shop.balance(1), 40)
        self.assertEqual(self.shop.one("SELECT status FROM payments")["status"], "canceled")

    async def test_startup_hook_recovers_before_polling(self):
        self.shop.platega_post = AsyncMock(side_effect=SimulatedPowerLoss)
        with self.assertRaises(SimulatedPowerLoss):
            await self.shop.create_platega_order(self.update, self.ctx)
        app = SimpleNamespace(bot=self.bot, bot_data={})
        with patch.object(self.shop, "bg_loop", AsyncMock()), patch.object(self.shop, "extension_loop", AsyncMock()):
            await self.shop.post_init(app)
            await asyncio.gather(*app.bot_data.values())
        self.assertEqual(self.shop.balance(1), 40)

    async def test_database_failure_rolls_back_debit(self):
        self.shop.db.execute("CREATE TRIGGER fail_payment BEFORE INSERT ON payments BEGIN SELECT RAISE(ABORT,'test failure'); END")
        await self.shop.create_platega_order(self.update, self.ctx)
        self.assertEqual(self.shop.balance(1), 40)
        self.assertEqual(self.shop.one("SELECT COUNT(*) n FROM payments")["n"], 0)
        self.shop.platega_post.assert_not_awaited()

    async def test_stale_creation_recovers_without_releasing_active_request(self):
        self.shop.platega_post = AsyncMock(side_effect=SimulatedPowerLoss)
        with self.assertRaises(SimulatedPowerLoss):
            await self.shop.create_platega_order(self.update, self.ctx)
        self.shop.recover_stuck()
        self.assertEqual(self.shop.balance(1), 0)
        self.shop.db.execute("UPDATE payments SET upd=?", (self.shop.now() - self.shop.STUCK_AFTER - 1,))
        self.shop.recover_stuck()
        self.assertEqual(self.shop.balance(1), 40)

    async def test_text_topup_without_gateway_reports_error(self):
        self.shop.set_cfg("platega_merchant", "")
        self.ctx.user_data = {"state": "balance_topup_amount"}
        await self.shop.on_text(self.update, self.ctx)
        self.message.reply_text.assert_awaited_once()
        self.bot.send_invoice.assert_not_awaited()

    async def test_text_topup_when_stars_disabled_reports_error(self):
        self.shop.set_cfg("stars_enabled", "0")
        self.ctx.user_data = {"state": "balance_topup_stars_amount"}
        self.message.text = "10"
        await self.shop.on_text(self.update, self.ctx)
        self.message.reply_text.assert_awaited_once()
        self.bot.send_invoice.assert_not_awaited()

    async def test_callback_alert_keeps_popup(self):
        self.update.callback_query = SimpleNamespace(answer=AsyncMock())
        await self.shop.alert(self.update, "test")
        self.update.callback_query.answer.assert_awaited_once_with("test", show_alert=True)
        self.message.reply_text.assert_not_awaited()

    async def test_single_use_promo_cannot_create_two_invoices(self):
        self.promo()
        await self.create()
        await self.create("payment-2")
        self.shop.platega_post.assert_not_awaited()
        self.assertEqual(self.shop.one("SELECT COUNT(*) n FROM payments")["n"], 1)
        self.assertEqual(await self.confirm(), "done")
        self.assertEqual(self.shop.one("SELECT used FROM promos")["used"], 1)
        self.assertEqual(self.shop.stock(1), 2)

    async def test_single_use_promo_reserves_global_limit(self):
        self.promo()
        await self.create()
        self.update.effective_user.id = 2
        await self.create("payment-2")
        self.shop.platega_post.assert_not_awaited()
        self.assertEqual(self.shop.one("SELECT COUNT(*) n FROM payments")["n"], 1)

    async def test_canceled_invoice_releases_promo_and_balance(self):
        self.promo()
        await self.create()
        self.shop.release_pending("payment-1", "canceled")
        self.assertEqual(self.shop.balance(1), 40)
        await self.create("payment-2")
        self.shop.platega_post.assert_awaited_once()
        self.assertEqual(await self.confirm("payment-2"), "done")

    async def test_inflight_promo_cannot_also_be_used_with_balance(self):
        self.promo(max_uses=5)
        await self.create()
        self.shop.balance_change("test", "UPDATE users SET balance=100 WHERE id=1", ())
        order = self.shop.fulfill(1, 1, 1, 1, 50, 50, 0, 50, "balance", "")
        self.assertIsNone(order)
        self.assertEqual(self.shop.balance(1), 100)

    async def test_legacy_invoice_over_promo_limit_credits_money(self):
        self.promo()
        self.shop.db.execute("UPDATE promos SET used=1")
        self.shop.db.execute("INSERT INTO payments(id,payer,owner,pid,promo_id,bal_used,final,rub,method,ts) "
                             "VALUES('legacy',1,1,1,1,0,50,50,2,?)", (self.shop.now(),))
        self.assertEqual(await self.confirm("legacy"), "nostock")
        self.assertEqual(self.shop.balance(1), 90)
        self.assertEqual(self.shop.stock(1), 3)

    async def test_confirmed_payment_and_fulfillment_are_idempotent(self):
        await self.create()
        self.assertEqual(await self.confirm(), "done")
        self.assertEqual(await self.confirm(), "done")
        existing = self.shop.fulfill(1, 1, 1, 0, 40, 60, 0, 60, "platega", "payment-1", prepaid=True)
        self.assertIsNotNone(existing)
        self.assertEqual(self.shop.one("SELECT COUNT(*) n FROM orders")["n"], 1)
        self.assertEqual(self.shop.stock(1), 2)

    async def test_out_of_stock_returns_gateway_amount_and_reserved_balance_once(self):
        await self.create()
        self.shop.db.execute("DELETE FROM keys")
        self.assertEqual(await self.confirm(), "nostock")
        self.assertEqual(self.shop.balance(1), 100)
        self.assertEqual(await self.confirm(), "nostock")
        self.assertEqual(self.shop.balance(1), 100)

    async def test_late_payment_after_expiry_credits_only_external_amount_once(self):
        self.promo()
        await self.create()
        self.shop.release_pending("payment-1", "expired")
        self.assertEqual(self.shop.balance(1), 40)
        self.assertEqual(await self.confirm(), "late")
        self.assertEqual(self.shop.balance(1), 50)
        self.assertEqual(await self.confirm(), "late")
        self.assertEqual(self.shop.balance(1), 50)
        self.assertEqual(self.shop.one("SELECT COUNT(*) n FROM orders")["n"], 0)

    async def test_stars_topup_redelivery_credits_once(self):
        self.message.successful_payment = SimpleNamespace(invoice_payload="bt:1:10",
            telegram_payment_charge_id="test-stars-charge", total_amount=10)
        await self.shop.paid(self.update, self.ctx)
        await self.shop.paid(self.update, self.ctx)
        self.assertEqual(self.shop.balance(1), 57)
        self.assertEqual(self.shop.one("SELECT COUNT(*) n FROM topups")["n"], 1)


if __name__ == "__main__":
    unittest.main()
