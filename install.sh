#!/usr/bin/env bash
# SellBot installer/updater: Ubuntu 24.04, Python 3.12, systemd.
set -Eeuo pipefail
umask 077
export DEBIAN_FRONTEND=noninteractive NEEDRESTART_MODE=a
APP=/opt/shop-bot
DATA=/var/lib/sellbot
RELEASE_ROOT=/opt/sellbot/releases
UNIT=/etc/systemd/system/shop-bot.service
REF=${SELLBOT_REF:-main}
[[ $EUID -eq 0 ]] || { echo 'Run with sudo bash install.sh'; exit 1; }
exec 9>/var/lock/sellbot-install.lock
flock -n 9 || { echo 'Another SellBot installation is running.'; exit 1; }
[[ $REF =~ ^[A-Za-z0-9._/-]+$ ]] || { echo 'Invalid SELLBOT_REF'; exit 1; }
[[ -d /run/systemd/system ]] || { echo 'A server with systemd is required.'; exit 1; }
. /etc/os-release
[[ ${ID:-} == ubuntu && ${VERSION_ID:-} == 24.04 ]] || {
  echo 'This installer supports Ubuntu 24.04 (Python 3.12).'; exit 1;
}

# Ask only on first installation. Existing secrets are reused during an update.
install -d -m 700 "$DATA" "$RELEASE_ROOT"
if [[ ! -s $DATA/config.env ]]; then
  for candidate in "$APP/main/config.env" "$APP/config.env"; do
    if [[ -f $candidate ]] && grep -Eq '^BOT_TOKEN=.+$' "$candidate" && grep -Eq '^ADMIN_IDS=.+$' "$candidate"; then
      cp -- "$candidate" "$DATA/config.env"
      break
    fi
  done
fi
if [[ ! -s $DATA/config.env ]]; then
  [[ -r /dev/tty ]] || { echo 'Run interactively, or SSH with -t, to enter token and Telegram ID.'; exit 1; }
  read -rsp 'BotFather token: ' bot_token </dev/tty; printf '\n' >/dev/tty
  [[ $bot_token =~ ^[0-9]+:[A-Za-z0-9_-]{20,}$ ]] || { echo 'Invalid token format.'; exit 1; }
  read -rp 'Your numeric Telegram admin ID: ' admin_id </dev/tty
  [[ $admin_id =~ ^[1-9][0-9]{0,18}$ ]] || { echo 'Telegram ID must be a positive number.'; exit 1; }
  printf 'BOT_TOKEN=%s\nADMIN_IDS=%s\n' "$bot_token" "$admin_id" >"$DATA/config.env"
  unset bot_token admin_id
fi
chmod 600 "$DATA/config.env"
apt-get update
apt-get install -y python3.12 python3.12-venv curl ca-certificates
id shopbot >/dev/null 2>&1 || useradd --system --home "$DATA" --shell /usr/sbin/nologin shopbot
stamp=$(date -u +%Y%m%d-%H%M%S)-$$
release="$RELEASE_ROOT/$stamp"
archive=$(mktemp /tmp/sellbot-archive.XXXXXX)
mkdir -m 755 "$release"
trap 'rm -f -- "$archive"' EXIT
curl --fail --silent --show-error --location "https://codeload.github.com/wseinsshop-alt/SellBot/tar.gz/$REF" -o "$archive"
tar -xzf "$archive" --strip-components=1 -C "$release"
[[ -f $release/main.py && -f $release/main/main.py && -f $release/requirements.txt ]] || {
  echo 'Downloaded project is incomplete.'; exit 1;
}
python3.12 -m venv "$release/.venv"
"$release/.venv/bin/python" -m pip install --disable-pip-version-check -r "$release/requirements.txt"
"$release/.venv/bin/python" -m py_compile "$release/main.py" "$release/main/main.py"
"$release/.venv/bin/python" -c 'import telegram, httpx; print("Dependencies: OK")'
chmod 755 /opt/sellbot "$RELEASE_ROOT"
chown -R shopbot:shopbot "$release"

was_active=0
systemctl is-active --quiet shop-bot && was_active=1
snapshot="$DATA/before-update-$stamp"
mkdir -m 700 "$snapshot"
[[ ! -f $UNIT ]] || cp -p -- "$UNIT" "$snapshot/shop-bot.service"
old_target=''
old_directory=''
if [[ -L $APP ]]; then old_target=$(readlink -f "$APP"); fi
switched=0
rollback() {
  code=$?
  trap - ERR
  if [[ $switched == 1 ]]; then
    systemctl stop shop-bot 2>/dev/null || true
    if [[ -L $APP ]]; then rm -f -- "$APP"; fi
    if [[ -n $old_target ]]; then ln -s -- "$old_target" "$APP";
    elif [[ -n $old_directory && -d $old_directory ]]; then mv -- "$old_directory" "$APP"; fi
    if [[ -f $snapshot/shop.db ]]; then
      rm -f -- "$DATA/shop.db-wal" "$DATA/shop.db-shm"
      cp -p -- "$snapshot/shop.db" "$DATA/shop.db"
    fi
    if [[ -f $snapshot/shop-bot.service ]]; then cp -p -- "$snapshot/shop-bot.service" "$UNIT";
    else rm -f -- "$UNIT"; fi
    chown -R shopbot:shopbot "$DATA"
    systemctl daemon-reload
  fi
  if [[ $was_active == 1 ]]; then systemctl start shop-bot 2>/dev/null || true; fi
  echo "Update failed. Previous files restored where available. Snapshot: $snapshot"
  exit "$code"
}
trap rollback ERR
if [[ $was_active == 1 ]]; then systemctl stop shop-bot; fi

# Snapshot live SQLite through the backup API after stopping its writer.
python3.12 - "$APP" "$DATA" "$snapshot" <<'PY'
import os, shutil, sqlite3, sys
from pathlib import Path
app, data, snapshot = map(Path, sys.argv[1:])
destination = data / 'shop.db'
legacy = app / 'main' / 'shop.db'
source = destination if destination.exists() else legacy
if source.exists():
    with sqlite3.connect(source) as src, sqlite3.connect(snapshot / 'shop.db') as dst:
        src.backup(dst)
    if not destination.exists():
        shutil.copy2(snapshot / 'shop.db', destination)
legacy_backups = app / 'main' / 'backups'
if legacy_backups.exists():
    shutil.copytree(legacy_backups, data / 'backups', dirs_exist_ok=True)
for item in data.rglob('*'):
    item.chmod(0o700 if item.is_dir() else 0o600)
PY
chown -R shopbot:shopbot "$DATA"
switched=1
if [[ -L $APP ]]; then rm -f -- "$APP";
elif [[ -e $APP ]]; then old_directory="$APP.before-$stamp"; mv -- "$APP" "$old_directory"; fi
ln -s -- "$release" "$APP"
cat >"$UNIT" <<'UNIT'
[Unit]
Description=SellBot Telegram Shop
After=network-online.target
Wants=network-online.target

[Service]
User=shopbot
Group=shopbot
WorkingDirectory=/opt/shop-bot
EnvironmentFile=/var/lib/sellbot/config.env
Environment=SELLBOT_DATA_DIR=/var/lib/sellbot
Environment=PYTHONDONTWRITEBYTECODE=1
ExecStart=/opt/shop-bot/.venv/bin/python -u /opt/shop-bot/main.py
Restart=on-failure
RestartSec=5
UMask=0077
NoNewPrivileges=true

[Install]
WantedBy=multi-user.target
UNIT
systemctl daemon-reload
systemctl enable shop-bot
systemctl restart shop-bot
sleep 5
systemctl is-active --quiet shop-bot
[[ $(systemctl show shop-bot -p NRestarts --value) == 0 ]] || {
  echo 'The new process restarted during startup.'; false;
}
trap - ERR
echo 'SellBot is running. Open the bot in Telegram and send /start.'
echo "Backup before update: $snapshot. Keep it outside this server as well."
systemctl status shop-bot --no-pager --lines=0
exit 0
