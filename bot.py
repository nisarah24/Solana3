"""
Solana Trading Bot (Telegram)  -  personal, single-owner bot   [v2]
------------------------------------------------------------------
- Market data ........ Dexscreener
- Swaps (buy/sell) ... Jupiter API
- Chain access ....... Solana public RPC (balances, send tx, confirm by signature)
- Wallet ............. imported by you, stored ENCRYPTED on disk (Fernet)
- Auto Buy / Auto Sell rules checked in the background

WARNING: this bot spends REAL money. Use a dedicated wallet with small funds.
Only the Telegram user IDs in ALLOWED_USER_IDS can use it.
"""
import asyncio
import base64
import html
import json
import logging
import os
import re
import time
import uuid
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation
from pathlib import Path

import requests
from requests.adapters import HTTPAdapter
from cryptography.fernet import Fernet
from dotenv import load_dotenv
from solders.keypair import Keypair
from solders.transaction import VersionedTransaction
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ParseMode
from telegram.error import BadRequest
from telegram.ext import (
    Application,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    TypeHandler,
    filters,
)

load_dotenv()

# ============================================================
# START: CONFIG (all values come from the .env file)
# ============================================================
BOT_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
ALLOWED_USER_IDS = {int(x) for x in re.findall(r"\d+", os.getenv("ALLOWED_USER_IDS", ""))}
ENC_KEY = os.getenv("WALLET_ENCRYPTION_KEY", "").strip()
RPC_URL = os.getenv("SOLANA_RPC_URL", "https://api.mainnet-beta.solana.com").strip()
JUP_BASE = os.getenv("JUPITER_BASE_URL", "https://lite-api.jup.ag/swap/v1").rstrip("/")
JUP_KEY = os.getenv("JUPITER_API_KEY", "").strip()
MAX_TRADE_SOL = Decimal(os.getenv("MAX_TRADE_SOL", "1"))   # safety cap per buy
MAX_FEE_SOL = Decimal("0.05")                               # cap for priority fee / tip
RULE_INTERVAL = float(os.getenv("RULE_INTERVAL_SECONDS", "5"))  # auto rules check speed
MAX_RULES_PER_USER = 20
DATA_FILE = Path(os.getenv("DATA_FILE", "bot_data.json"))

DEX_TOKEN_URL = "https://api.dexscreener.com/latest/dex/tokens/{}"
REQUEST_TIMEOUT = 15

WSOL = "So11111111111111111111111111111111111111112"
LAMPORTS = Decimal(10**9)
TOKEN_PROGRAMS = [
    "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA",
    "TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb",
]

DEFAULT_SETTINGS = {
    "priority_fee": "0.0006",                 # SOL
    "tip": "0.0006",                          # SOL
    "buy_slippage": "15",                     # percent
    "sell_slippage": "15",                    # percent
    "buy_presets": "0.015,0.025,0.05,0.1",    # quick-buy buttons (SOL)
    "confirm_trades": "0",                    # "1" = ask before every trade
}
# ============================================================
# END: CONFIG
# ============================================================

logging.basicConfig(
    format="%(asctime)s %(levelname)s %(name)s: %(message)s", level=logging.INFO
)
logging.getLogger("httpx").setLevel(logging.WARNING)
logger = logging.getLogger("trading_bot")

# One shared HTTP session = keep-alive connections = faster requests.
HTTP = requests.Session()
HTTP.mount("https://", HTTPAdapter(pool_connections=20, pool_maxsize=20))


# ============================================================
# START: STORAGE (wallet is encrypted, positions + settings + rules in JSON)
# ============================================================
DATA = {"wallets": {}, "positions": {}, "settings": {}, "rules": {}}
BUSY = set()  # user ids with a trade in progress (blocks double clicks)
fernet = None


def load_data():
    if DATA_FILE.exists():
        DATA.update(json.loads(DATA_FILE.read_text(encoding="utf-8")))


def save_data():
    tmp = DATA_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(DATA, indent=2), encoding="utf-8")
    os.replace(tmp, DATA_FILE)
    try:
        os.chmod(DATA_FILE, 0o600)
    except OSError:
        pass


def get_raw(uid: int, name: str) -> str:
    return str(DATA["settings"].get(str(uid), {}).get(name, DEFAULT_SETTINGS[name]))


def get_setting(uid: int, name: str) -> Decimal:
    return Decimal(get_raw(uid, name))


def set_raw(uid: int, name: str, value: str):
    DATA["settings"].setdefault(str(uid), {})[name] = value
    save_data()


def set_setting(uid: int, name: str, value: Decimal):
    set_raw(uid, name, format(value, "f"))


def confirm_on(uid: int) -> bool:
    return get_raw(uid, "confirm_trades") == "1"


def get_presets(uid: int) -> list:
    """Quick-buy amounts chosen in Settings (1-4 values)."""
    out = []
    for part in get_raw(uid, "buy_presets").split(","):
        value = parse_sol_amount(part, MAX_TRADE_SOL)
        if value is not None:
            out.append(format(value.normalize(), "f"))
    return out[:4] or DEFAULT_SETTINGS["buy_presets"].split(",")


def wallet_address(uid: int):
    w = DATA["wallets"].get(str(uid))
    return w["address"] if w else None


def save_wallet(uid: int, kp: Keypair):
    address = str(kp.pubkey())
    if wallet_address(uid) != address:
        DATA["positions"].pop(str(uid), None)  # cost basis belongs to a wallet
    DATA["wallets"][str(uid)] = {
        "address": address,
        "enc": fernet.encrypt(bytes(kp)).decode(),
    }
    save_data()


def load_keypair(uid: int):
    w = DATA["wallets"].get(str(uid))
    if not w:
        return None
    return Keypair.from_bytes(fernet.decrypt(w["enc"].encode()))


def remove_wallet(uid: int):
    DATA["wallets"].pop(str(uid), None)
    DATA["positions"].pop(str(uid), None)
    save_data()


def parse_private_key(text: str):
    """Accepts a base58 secret key or a JSON byte array. Returns Keypair or None."""
    text = text.strip()
    try:
        if text.startswith("["):
            return Keypair.from_bytes(bytes(json.loads(text)))
        return Keypair.from_base58_string(text)
    except Exception:
        return None
# ============================================================
# END: STORAGE
# ============================================================


# ============================================================
# START: HELPERS (formatting / validation)
# ============================================================
def valid_solana_address(address: str) -> bool:
    return bool(re.fullmatch(r"[1-9A-HJ-NP-Za-km-z]{32,44}", address))


def number(value, default=None):
    if value is None:
        return default
    try:
        result = Decimal(str(value))
        return result if result.is_finite() else default
    except (InvalidOperation, ValueError, TypeError):
        return default


def compact_money(value):
    value = number(value)
    if value is None:
        return "N/A"
    a = abs(value)
    if a >= Decimal("1000000000"):
        return f"${value / Decimal('1000000000'):,.2f}B"
    if a >= Decimal("1000000"):
        return f"${value / Decimal('1000000'):,.2f}M"
    if a >= Decimal("1000"):
        return f"${value / Decimal('1000'):,.2f}K"
    return f"${value:,.2f}"


def token_price(value):
    value = number(value)
    if value is None:
        return "N/A"
    if value == 0:
        return "$0"
    if abs(value) < Decimal("0.01"):
        return f"${value:.10f}".rstrip("0").rstrip(".")
    return f"${value:,.6f}".rstrip("0").rstrip(".")


def safe_text(value, limit=100):
    return html.escape(str(value or "Unknown")[:limit])


def short(addr: str) -> str:
    return f"{addr[:4]}…{addr[-4:]}"


def fmt_sol(lamports) -> str:
    return f"{Decimal(lamports) / LAMPORTS:.4f}"


def fmt_amount(raw: int, decimals: int) -> str:
    ui = Decimal(raw) / Decimal(10**decimals)
    if ui >= 1000:
        return f"{ui:,.2f}"
    if ui >= 1:
        return f"{ui:,.4f}"
    return f"{ui:.6f}"


def now_str() -> str:
    return datetime.now(timezone.utc).strftime("%H:%M:%S UTC")


def parse_sol_amount(text: str, maximum: Decimal):
    try:
        value = Decimal(text.strip())
    except (InvalidOperation, ValueError):
        return None
    if not value.is_finite() or value <= 0 or value > maximum:
        return None
    return value.quantize(Decimal("0.000001"))


def parse_usd_value(text: str):
    """'0.0001', '$50k', '1.5m' -> Decimal (or None)."""
    t = text.strip().lower().replace("$", "").replace(",", "")
    mult = Decimal(1)
    if t and t[-1] in "kmb":
        mult = {"k": Decimal(10**3), "m": Decimal(10**6), "b": Decimal(10**9)}[t[-1]]
        t = t[:-1]
    try:
        value = Decimal(t) * mult
    except (InvalidOperation, ValueError):
        return None
    return value if value.is_finite() and value > 0 else None


def btn(label, data):
    return InlineKeyboardButton(label, callback_data=data)


BACK_HOME = InlineKeyboardMarkup([[btn("⬅️ Main Menu", "m:home")]])


async def edit(bot, ref, text, markup=None):
    """Edit a message IN PLACE. ref = (chat_id, message_id)."""
    try:
        await bot.edit_message_text(
            text,
            chat_id=ref[0],
            message_id=ref[1],
            parse_mode=ParseMode.HTML,
            reply_markup=markup,
            disable_web_page_preview=True,
        )
    except BadRequest as exc:
        if "not modified" not in str(exc).lower():
            raise
# ============================================================
# END: HELPERS
# ============================================================


# ============================================================
# START: DEXSCREENER (market data + prices)
# ============================================================
def fetch_best_pairs(mints):
    """Best-liquidity Solana pair for each mint (up to 30 per request)."""
    out = {}
    for i in range(0, len(mints), 30):
        chunk = mints[i:i + 30]
        r = HTTP.get(
            DEX_TOKEN_URL.format(",".join(chunk)),
            headers={"Accept": "application/json"},
            timeout=REQUEST_TIMEOUT,
        )
        r.raise_for_status()
        for p in r.json().get("pairs") or []:
            if p.get("chainId") != "solana":
                continue
            m = (p.get("baseToken") or {}).get("address")
            if m not in chunk:
                continue
            liq = number((p.get("liquidity") or {}).get("usd"), Decimal(0))
            cur = out.get(m)
            if cur is None or liq > number((cur.get("liquidity") or {}).get("usd"), Decimal(0)):
                out[m] = p
    return out


def fetch_token(mint: str):
    return fetch_best_pairs([mint]).get(mint)


_SOL_CACHE = {"t": 0.0, "v": None}


def get_sol_usd():
    if _SOL_CACHE["v"] and time.time() - _SOL_CACHE["t"] < 30:
        return _SOL_CACHE["v"]
    pair = fetch_best_pairs([WSOL]).get(WSOL)
    value = number(pair.get("priceUsd")) if pair else None
    if value:
        _SOL_CACHE.update(t=time.time(), v=value)
    return value or _SOL_CACHE["v"]
# ============================================================
# END: DEXSCREENER
# ============================================================


# ============================================================
# START: SOLANA RPC (public RPC: balances, send, confirm, parse tx)
# ============================================================
def rpc(method: str, params: list):
    r = HTTP.post(
        RPC_URL,
        json={"jsonrpc": "2.0", "id": 1, "method": method, "params": params},
        timeout=25,
    )
    r.raise_for_status()
    data = r.json()
    if "error" in data:
        err = data["error"]
        raise RuntimeError(err.get("message", str(err)) if isinstance(err, dict) else str(err))
    return data["result"]


def get_sol_balance(address: str) -> int:
    return rpc("getBalance", [address, {"commitment": "confirmed"}])["value"]


def _accounts_for(address: str, program: str):
    return rpc(
        "getTokenAccountsByOwner",
        [address, {"programId": program}, {"encoding": "jsonParsed", "commitment": "confirmed"}],
    )["value"]


def get_token_accounts(address: str) -> dict:
    """{mint: {"raw": int, "decimals": int}} for all non-zero token balances.
    Both token programs are queried in parallel (faster)."""
    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(lambda p: _accounts_for(address, p), TOKEN_PROGRAMS))
    holdings = {}
    for accounts in results:
        for acc in accounts:
            info = acc["account"]["data"]["parsed"]["info"]
            raw = int(info["tokenAmount"]["amount"])
            if raw > 0:
                entry = holdings.setdefault(
                    info["mint"], {"raw": 0, "decimals": info["tokenAmount"]["decimals"]}
                )
                entry["raw"] += raw
    return holdings


def wait_confirm(signature: str, timeout: int = 60) -> str:
    """Poll the signature status. Returns 'confirmed', 'failed: ...' or 'timeout'."""
    deadline = time.time() + timeout
    while time.time() < deadline:
        res = rpc("getSignatureStatuses", [[signature], {"searchTransactionHistory": True}])["value"][0]
        if res:
            if res.get("err"):
                return f"failed: {json.dumps(res['err'])[:120]}"
            if res.get("confirmationStatus") in ("confirmed", "finalized"):
                return "confirmed"
        time.sleep(0.6)
    return "timeout"


def parse_swap_tx(signature: str, owner: str, mint: str) -> dict:
    """Read the confirmed transaction: real SOL and token change of the owner."""
    tx = None
    for _ in range(10):
        tx = rpc(
            "getTransaction",
            [signature, {"encoding": "jsonParsed", "commitment": "confirmed",
                         "maxSupportedTransactionVersion": 0}],
        )
        if tx:
            break
        time.sleep(1)
    if not tx:
        return {"parsed": False, "sol_delta": 0, "token_delta": 0, "decimals": 0}

    meta = tx["meta"]
    keys = [k["pubkey"] if isinstance(k, dict) else k for k in tx["transaction"]["message"]["accountKeys"]]
    idx = keys.index(owner)
    sol_delta = meta["postBalances"][idx] - meta["preBalances"][idx]

    def token_sum(balances):
        total, decimals = 0, 0
        for b in balances or []:
            if b.get("owner") == owner and b.get("mint") == mint:
                total += int(b["uiTokenAmount"]["amount"])
                decimals = b["uiTokenAmount"]["decimals"]
        return total, decimals

    pre, _ = token_sum(meta.get("preTokenBalances"))
    post, decimals = token_sum(meta.get("postTokenBalances"))
    return {"parsed": True, "sol_delta": sol_delta, "token_delta": post - pre, "decimals": decimals}
# ============================================================
# END: SOLANA RPC
# ============================================================


# ============================================================
# START: JUPITER SWAP (quote -> build tx -> sign -> send via RPC)
# NOTE: JUPITER_BASE_URL is configurable in .env. Jupiter now also offers
# "Swap V2" (api.jup.ag/swap/v2, API key required); see their docs to migrate.
# ============================================================
def jup_headers():
    h = {"Accept": "application/json"}
    if JUP_KEY:
        h["x-api-key"] = JUP_KEY
    return h


def jup_request(method: str, path: str, **kwargs):
    r = HTTP.request(method, f"{JUP_BASE}{path}", headers=jup_headers(),
                     timeout=REQUEST_TIMEOUT, **kwargs)
    if r.status_code >= 400:
        raise RuntimeError(f"Jupiter {r.status_code}: {r.text[:200]}")
    return r.json()


def run_swap(kp, input_mint, output_mint, amount_raw, slippage_pct, priority_lamports, token_mint):
    """Blocking: quote, build, sign, send, confirm, parse. Run via asyncio.to_thread."""
    owner = str(kp.pubkey())
    bps = int(slippage_pct * 100)
    quote = jup_request("GET", "/quote", params={
        "inputMint": input_mint,
        "outputMint": output_mint,
        "amount": str(amount_raw),
        "slippageBps": bps,
        "restrictIntermediateTokens": "true",
    })
    body = {
        "quoteResponse": quote,
        "userPublicKey": owner,
        "wrapAndUnwrapSol": True,
        "dynamicComputeUnitLimit": True,
    }
    if priority_lamports > 0:
        body["prioritizationFeeLamports"] = int(priority_lamports)
    swap = jup_request("POST", "/swap", json=body)

    raw_tx = VersionedTransaction.from_bytes(base64.b64decode(swap["swapTransaction"]))
    signed = VersionedTransaction(raw_tx.message, [kp])
    signature = rpc("sendTransaction", [
        base64.b64encode(bytes(signed)).decode(),
        {"encoding": "base64", "skipPreflight": False, "maxRetries": 3,
         "preflightCommitment": "confirmed"},
    ])
    status = wait_confirm(signature)
    result = {"signature": signature, "status": status}
    if status == "confirmed":
        result.update(parse_swap_tx(signature, owner, token_mint))
    return result
# ============================================================
# END: JUPITER SWAP
# ============================================================


# ============================================================
# START: MAIN MENU
# ------------------------------------------------------------
# Row 1 = wallet button (Import Wallet, or Wallet once imported)
# Row 2 = Auto Buy | Auto Sell
# To add/remove a button: edit main_menu_keyboard() and add a
# branch for its callback in on_button() -> "MAIN MENU" section.
# ============================================================
def main_menu_keyboard(uid: int) -> InlineKeyboardMarkup:
    wallet_btn = btn("👛 Wallet", "w:view") if wallet_address(uid) else btn("🔑 Import Wallet", "w:import")
    return InlineKeyboardMarkup([
        [wallet_btn],
        [btn("🤖 Auto Buy", "ru:buy"), btn("🤖 Auto Sell", "ru:sell")],
        [btn("Buy", "m:buy"), btn("Sell", "m:sell")],
        [btn("Positions", "m:pos")],
        [btn("Settings", "m:settings"), btn("↻ Refresh", "m:refresh")],
    ])


async def main_menu_text(uid: int) -> str:
    addr = wallet_address(uid)
    if not addr:
        wallet_block = "<i>No wallet yet. Tap 🔑 Import Wallet to start.</i>"
    else:
        try:
            lamports, sol_usd = await asyncio.gather(
                asyncio.to_thread(get_sol_balance, addr),
                asyncio.to_thread(get_sol_usd),
            )
            usd = f" (${Decimal(lamports) / LAMPORTS * sol_usd:,.2f})" if sol_usd else ""
            balance = f"{fmt_sol(lamports)} SOL{usd}"
        except Exception as exc:
            logger.warning("balance failed: %s", exc)
            balance = "N/A"
        wallet_block = f"<code>{addr}</code>  <i>(Tap to copy)</i>\nBalance: <b>{balance}</b>"
    return (
        "🟣 <b>Solana Trading Bot</b>\n"
        f"{wallet_block}\n"
        "──\n"
        "Tap <b>Buy</b> and send a token address, or open <b>Positions</b>.\n"
        "Click Refresh to update your balance.\n\n"
        f"<i>Updated: {now_str()}</i>"
    )


async def show_main(bot, ref, uid, note=""):
    await edit(bot, ref, note + await main_menu_text(uid), main_menu_keyboard(uid))
# ============================================================
# END: MAIN MENU
# ============================================================


# ============================================================
# START: WALLET SCREENS (import / view / remove)
# ============================================================
IMPORT_PROMPT = (
    "🔑 <b>Import Wallet</b>\n\n"
    "Send your wallet <b>private key</b> (base58 string or JSON array) as a message.\n"
    "I will delete your message right away and store the key encrypted.\n\n"
    "⚠️ Use a <b>dedicated trading wallet</b> with only the funds you can afford to lose. "
    "Never import your main wallet."
)


async def show_wallet(bot, ref, uid, note=""):
    addr = wallet_address(uid)
    if not addr:
        await show_main(bot, ref, uid)
        return
    try:
        lamports = await asyncio.to_thread(get_sol_balance, addr)
        balance = f"{fmt_sol(lamports)} SOL"
    except Exception:
        balance = "N/A"
    await edit(
        bot, ref,
        f"{note}👛 <b>Wallet</b>\n<code>{addr}</code>\nBalance: <b>{balance}</b>",
        InlineKeyboardMarkup([
            [btn("⬅️ Back", "m:home"), btn("↻ Refresh", "w:view")],
            [btn("🔁 Replace Wallet", "w:import"), btn("🗑 Remove", "w:remove")],
        ]),
    )
# ============================================================
# END: WALLET SCREENS
# ============================================================


# ============================================================
# START: SETTINGS SCREEN
# (priority fee, tip, slippage, quick-buy amounts, confirm trades)
# ============================================================
SETTING_PROMPTS = {
    "fee": ("priority_fee", "Priority Fee", "SOL", MAX_FEE_SOL, Decimal("0")),
    "tip": ("tip", "Tip", "SOL", MAX_FEE_SOL, Decimal("0")),
    "bslip": ("buy_slippage", "Buy Slippage", "%", Decimal("50"), Decimal("0.1")),
    "sslip": ("sell_slippage", "Sell Slippage", "%", Decimal("50"), Decimal("0.1")),
}


def settings_text(uid: int) -> str:
    confirm = "🟢 ON" if confirm_on(uid) else "🔴 OFF"
    return (
        "⚙️ <b>Settings</b>\n\n"
        f"⚡ Priority Fee: <b>{get_setting(uid, 'priority_fee')} SOL</b>\n"
        f"💸 Tip: <b>{get_setting(uid, 'tip')} SOL</b>\n"
        f"🛒 Buy Slippage: <b>{get_setting(uid, 'buy_slippage')}%</b>\n"
        f"💰 Sell Slippage: <b>{get_setting(uid, 'sell_slippage')}%</b>\n"
        f"⚡ Quick Buy: <b>{' / '.join(get_presets(uid))} SOL</b>\n"
        f"✅ Confirm Trades: <b>{confirm}</b>\n\n"
        "<i>Priority Fee + Tip are added to every swap as the priority fee.\n"
        "Confirm OFF = buttons trade instantly.</i>"
    )


def settings_keyboard(uid: int) -> InlineKeyboardMarkup:
    dot = "🟢" if confirm_on(uid) else "🔴"
    return InlineKeyboardMarkup([
        [btn("⬅️ Back", "m:home")],
        [btn(f"{get_setting(uid, 'priority_fee')} SOL (Priority Fee)", "st:fee"),
         btn(f"{get_setting(uid, 'tip')} SOL (Tip)", "st:tip")],
        [btn(f"Buy Slippage: {get_setting(uid, 'buy_slippage')}%", "st:bslip"),
         btn(f"Sell Slippage: {get_setting(uid, 'sell_slippage')}%", "st:sslip")],
        [btn("⚡ Quick Buy Amounts", "st:presets")],
        [btn(f"{dot} Confirm Trades", "st:confirm")],
    ])


async def show_settings(bot, ref, uid):
    await edit(bot, ref, settings_text(uid), settings_keyboard(uid))
# ============================================================
# END: SETTINGS SCREEN
# ============================================================


# ============================================================
# START: TOKEN CARD + CONFIRM SCREENS
# ============================================================
def token_message(mint: str, pair: dict) -> str:
    token = pair.get("baseToken") or {}
    liquidity = pair.get("liquidity") or {}
    volume = pair.get("volume") or {}
    change_24h = number((pair.get("priceChange") or {}).get("h24"))
    change_text = "N/A" if change_24h is None else f"{change_24h:+.2f}%"
    return (
        "🟣 <b>SOLANA TOKEN TERMINAL</b>\n"
        "━━━━━━━━━━━━━━━━━━\n"
        f"🪙 <b>{safe_text(token.get('name'))}</b> ({safe_text(token.get('symbol'))})\n\n"
        f"💵 <b>Price:</b> {token_price(pair.get('priceUsd'))}\n"
        f"💧 <b>Liquidity:</b> {compact_money(liquidity.get('usd'))}\n"
        f"📊 <b>Market Cap / FDV:</b> {compact_money(pair.get('marketCap', pair.get('fdv')))}\n"
        f"📈 <b>24h Volume:</b> {compact_money(volume.get('h24'))}\n"
        f"📉 <b>24h Change:</b> {change_text}\n\n"
        f"🔗 <b>Mint:</b>\n<code>{safe_text(mint, 60)}</code>\n\n"
        f"🏦 <b>DEX:</b> {safe_text(pair.get('dexId'), 40)}\n"
        "━━━━━━━━━━━━━━━━━━\n"
        "⚠️ <i>Market data is not a safety audit or buy signal.</i>\n"
        f"<i>Updated: {now_str()}</i>"
    )


def token_keyboard(uid: int, mint: str, pair: dict) -> InlineKeyboardMarkup:
    chart = pair.get("url") or ""
    chart = chart if chart.startswith("https://dexscreener.com/") else "https://dexscreener.com/solana"
    buttons = [btn(f"{a} SOL", f"ta:{a}:{mint}") for a in get_presets(uid)]
    buttons.append(btn("✏️ Custom", f"tc:{mint}"))
    rows = [buttons[i:i + 3] for i in range(0, len(buttons), 3)]
    return InlineKeyboardMarkup([
        [btn("↻ Refresh", f"tr:{mint}"), InlineKeyboardButton("📊 Chart", url=chart)],
        *rows,
        [btn("🤖 Auto Buy", f"rn:buy:{mint}")],
        [btn("⬅️ Main Menu", "m:home")],
    ])


async def show_token(bot, ref, uid, mint, note=""):
    try:
        pair = await asyncio.to_thread(fetch_token, mint)
    except Exception as exc:
        logger.warning("dexscreener failed: %s", exc)
        await edit(bot, ref, "❌ Market data request failed. Please try again.", BACK_HOME)
        return
    if pair is None:
        await edit(
            bot, ref,
            "⚠️ No Solana trading pair was found for this mint.\n"
            "The token may be new, unlisted, or not indexed yet.",
            BACK_HOME,
        )
        return
    await edit(bot, ref, note + token_message(mint, pair), token_keyboard(uid, mint, pair))


async def show_buy_confirm(bot, ref, uid, mint, amount: Decimal):
    """Only shown when 'Confirm Trades' is ON in Settings."""
    fee = get_setting(uid, "priority_fee") + get_setting(uid, "tip")
    await edit(
        bot, ref,
        "🛒 <b>Confirm BUY</b>\n\n"
        f"<code>{mint}</code>\n"
        f"Amount: <b>{amount} SOL</b>\n"
        f"Slippage: <b>{get_setting(uid, 'buy_slippage')}%</b>\n"
        f"Priority fee + tip: <b>{fee} SOL</b>\n\n"
        "⚠️ This will spend real SOL.",
        InlineKeyboardMarkup([[btn("✅ Confirm", f"by:{format(amount, 'f')}:{mint}"),
                               btn("❌ Cancel", f"tr:{mint}")]]),
    )


async def show_sell_confirm(bot, ref, uid, mint, pct: int):
    """Only shown when 'Confirm Trades' is ON in Settings."""
    fee = get_setting(uid, "priority_fee") + get_setting(uid, "tip")
    await edit(
        bot, ref,
        f"💰 <b>Confirm SELL {pct}%</b>\n\n<code>{mint}</code>\n"
        f"Slippage: <b>{get_setting(uid, 'sell_slippage')}%</b>\n"
        f"Priority fee + tip: <b>{fee} SOL</b>",
        InlineKeyboardMarkup([[btn("✅ Confirm", f"sx:{pct}:{mint}"),
                               btn("❌ Cancel", f"pd:{mint}")]]),
    )
# ============================================================
# END: TOKEN CARD + CONFIRM SCREENS
# ============================================================


# ============================================================
# START: POSITIONS (on-chain balances + Dexscreener prices + PnL)
# ------------------------------------------------------------
# Unrealized PnL = current value (SOL) - cost basis (SOL).
# Cost basis is recorded from the REAL transaction (signature) of each
# buy made through this bot. Tokens bought elsewhere show "no cost data".
# Value is an estimate (Dexscreener price), not an exit quote.
# ============================================================
async def load_positions(uid: int, only=None):
    addr = wallet_address(uid)
    if only:  # single token: fetch everything in parallel
        holdings, sol_usd, pairs = await asyncio.gather(
            asyncio.to_thread(get_token_accounts, addr),
            asyncio.to_thread(get_sol_usd),
            asyncio.to_thread(fetch_best_pairs, [only]),
        )
        holdings = {m: h for m, h in holdings.items() if m == only}
    else:
        holdings, sol_usd = await asyncio.gather(
            asyncio.to_thread(get_token_accounts, addr),
            asyncio.to_thread(get_sol_usd),
        )
        pairs = await asyncio.to_thread(fetch_best_pairs, list(holdings)) if holdings else {}
    tracked = DATA["positions"].get(str(uid), {})

    rows = []
    for mint, h in holdings.items():
        pair = pairs.get(mint)
        symbol = ((pair or {}).get("baseToken") or {}).get("symbol") or tracked.get(mint, {}).get("symbol") or short(mint)
        ui = Decimal(h["raw"]) / Decimal(10 ** h["decimals"])
        price = number(pair.get("priceUsd")) if pair else None
        value_sol = ui * price / sol_usd if (price is not None and sol_usd) else None
        cost = tracked.get(mint, {}).get("cost_lamports")
        cost_sol = Decimal(cost) / LAMPORTS if cost else None
        pnl_sol = pnl_pct = None
        if value_sol is not None and cost_sol:
            pnl_sol = value_sol - cost_sol
            pnl_pct = pnl_sol / cost_sol * 100
        if not only and mint not in tracked and value_sol is not None and value_sol < Decimal("0.0005"):
            continue  # hide dust / airdrop spam
        rows.append({
            "mint": mint, "symbol": symbol, "raw": h["raw"], "decimals": h["decimals"],
            "value_sol": value_sol, "cost_sol": cost_sol, "pnl_sol": pnl_sol, "pnl_pct": pnl_pct,
        })
    rows.sort(key=lambda r: r["value_sol"] or Decimal(0), reverse=True)
    return rows[:20]


def pnl_line(r) -> str:
    if r["pnl_sol"] is None:
        return "PnL: N/A (no cost data)" if r["cost_sol"] is None else "PnL: N/A (no price)"
    icon = "🟢" if r["pnl_sol"] >= 0 else "🔴"
    return f"{icon} PnL: <b>{r['pnl_sol']:+.4f} SOL ({r['pnl_pct']:+.1f}%)</b>"


async def show_positions(bot, ref, uid):
    if not wallet_address(uid):
        await edit(bot, ref, "🔑 Import a wallet first.", BACK_HOME)
        return
    try:
        rows = await load_positions(uid)
    except Exception as exc:
        logger.warning("positions failed: %s", exc)
        await edit(bot, ref, "❌ Could not load positions. Try again.",
                   InlineKeyboardMarkup([[btn("⬅️ Back", "m:home"), btn("↻ Retry", "m:pos")]]))
        return

    lines = ["📦 <b>Your Positions</b>\n"]
    if not rows:
        lines.append("<i>No open positions.</i>")
    for i, r in enumerate(rows, 1):
        value = "N/A" if r["value_sol"] is None else f"{r['value_sol']:.4f} SOL"
        lines.append(f"{i}. <b>{safe_text(r['symbol'], 20)}</b> - {value}\n    {pnl_line(r)}")
    lines.append(f"\n<i>Tap a token to view / sell. Updated: {now_str()}</i>")

    buttons = [[btn("⬅️ Back", "m:home"), btn("↻ Refresh", "m:pos")]]
    row = []
    for r in rows:
        pct = "" if r["pnl_pct"] is None else f" {r['pnl_pct']:+.0f}%"
        row.append(btn(f"{r['symbol'][:12]}{pct}", f"pd:{r['mint']}"))
        if len(row) == 2:
            buttons.append(row)
            row = []
    if row:
        buttons.append(row)
    await edit(bot, ref, "\n".join(lines), InlineKeyboardMarkup(buttons))


async def show_position(bot, ref, uid, mint):
    try:
        rows = await load_positions(uid, only=mint)
    except Exception as exc:
        logger.warning("position failed: %s", exc)
        await edit(bot, ref, "❌ Could not load position. Try again.", BACK_HOME)
        return
    r = next((x for x in rows if x["mint"] == mint), None)
    if r is None:
        await show_positions(bot, ref, uid)
        return
    value = "N/A" if r["value_sol"] is None else f"{r['value_sol']:.4f} SOL"
    cost = "N/A" if r["cost_sol"] is None else f"{r['cost_sol']:.4f} SOL"
    await edit(
        bot, ref,
        f"📈 <b>{safe_text(r['symbol'], 20)}</b>\n<code>{mint}</code>\n\n"
        f"Holding: <b>{fmt_amount(r['raw'], r['decimals'])}</b>\n"
        f"Value: <b>{value}</b>\nCost: <b>{cost}</b>\n{pnl_line(r)}\n\n"
        f"<i>Unrealized, estimated from Dexscreener price. Updated: {now_str()}</i>",
        InlineKeyboardMarkup([
            [btn("⬅️ Positions", "m:pos"), btn("↻ Refresh", f"pd:{mint}")],
            [btn("Sell 25%", f"sl:25:{mint}"), btn("Sell 50%", f"sl:50:{mint}"),
             btn("Sell 100%", f"sl:100:{mint}")],
            [btn("🤖 Auto Sell", f"rn:sell:{mint}")],
        ]),
    )
# ============================================================
# END: POSITIONS
# ============================================================


# ============================================================
# START: TRADE EXECUTION (buy / sell)
# ============================================================
def priority_lamports(uid: int) -> int:
    return int((get_setting(uid, "priority_fee") + get_setting(uid, "tip")) * LAMPORTS)


def explorer_link(signature: str) -> str:
    return f'<a href="https://solscan.io/tx/{signature}">View on Solscan</a>'


def status_note(res: dict) -> str:
    if res["status"] == "timeout":
        return ("⏳ <b>Not confirmed yet.</b> The transaction may still land. "
                f"Check it here:\n{explorer_link(res['signature'])}")
    return f"❌ <b>Transaction failed</b>\n{safe_text(res['status'], 200)}\n{explorer_link(res['signature'])}"


def error_text(exc: Exception) -> str:
    msg = str(exc)
    if "insufficient" in msg.lower():
        return "Not enough SOL (keep ~0.003 SOL extra for fees and token account rent)."
    return safe_text(msg, 300)


def update_position_after_buy(uid, mint, symbol, spent, received, decimals, legacy_raw=None):
    positions = DATA["positions"].setdefault(str(uid), {})
    pos = positions.get(mint)
    if pos is None:
        pos = positions[mint] = {"symbol": symbol, "cost_lamports": 0, "raw": 0}
    pos["symbol"] = symbol
    pos["cost_lamports"] += spent
    pos["decimals"] = decimals
    if "raw" in pos:
        pos["raw"] += received
    else:  # older tracked position without token amount
        pos["raw"] = legacy_raw if legacy_raw is not None else received
    save_data()


async def do_buy(bot, ref, uid, mint, amount: Decimal):
    if uid in BUSY:
        return
    BUSY.add(uid)
    try:
        kp = load_keypair(uid)
        if kp is None:
            await edit(bot, ref, "🔑 Import a wallet first.", BACK_HOME)
            return
        lamports = int(amount * LAMPORTS)
        await edit(bot, ref, f"⏳ Buying with {amount} SOL...")
        res, pair = await asyncio.gather(
            asyncio.to_thread(run_swap, kp, WSOL, mint, lamports,
                              get_setting(uid, "buy_slippage"), priority_lamports(uid), mint),
            asyncio.to_thread(fetch_token, mint),
            return_exceptions=True,
        )
        if isinstance(res, Exception):
            raise res
        if isinstance(pair, Exception):
            pair = None
        if res["status"] != "confirmed":
            await edit(bot, ref, status_note(res), BACK_HOME)
            return

        spent = max(-res["sol_delta"], 0)
        received = max(res["token_delta"], 0)
        symbol = ((pair or {}).get("baseToken") or {}).get("symbol") or short(mint)
        legacy_raw = None
        old = DATA["positions"].get(str(uid), {}).get(mint)
        if old and "raw" not in old:
            try:
                held = (await asyncio.to_thread(get_token_accounts, str(kp.pubkey()))).get(mint)
                legacy_raw = held["raw"] if held else None
            except Exception:
                pass
        update_position_after_buy(uid, mint, symbol, spent, received, res["decimals"], legacy_raw)

        await edit(
            bot, ref,
            "✅ <b>Buy confirmed</b>\n\n"
            f"Token: <b>{safe_text(symbol, 20)}</b>\n"
            f"Spent: <b>{fmt_sol(spent)} SOL</b> (incl. fees)\n"
            f"Received: <b>{fmt_amount(received, res['decimals'])}</b>\n"
            f"{explorer_link(res['signature'])}",
            InlineKeyboardMarkup([[btn("📦 Positions", "m:pos"), btn("⬅️ Main Menu", "m:home")]]),
        )
    except Exception as exc:
        logger.exception("buy failed")
        await edit(bot, ref, f"❌ Buy failed:\n<code>{error_text(exc)}</code>", BACK_HOME)
    finally:
        BUSY.discard(uid)


async def do_sell(bot, ref, uid, mint, pct: int):
    if uid in BUSY:
        return
    BUSY.add(uid)
    try:
        kp = load_keypair(uid)
        if kp is None:
            await edit(bot, ref, "🔑 Import a wallet first.", BACK_HOME)
            return
        await edit(bot, ref, f"⏳ Selling {pct}%...")
        holdings = await asyncio.to_thread(get_token_accounts, str(kp.pubkey()))
        held = holdings.get(mint)
        if not held:
            await edit(bot, ref, "No balance found for this token.", BACK_HOME)
            return
        balance_before = held["raw"]
        amount_raw = balance_before * pct // 100
        if amount_raw <= 0:
            await edit(bot, ref, "Amount too small to sell.", BACK_HOME)
            return

        res = await asyncio.to_thread(
            run_swap, kp, mint, WSOL, amount_raw,
            get_setting(uid, "sell_slippage"), priority_lamports(uid), mint,
        )
        if res["status"] != "confirmed":
            await edit(bot, ref, status_note(res), BACK_HOME)
            return

        sold_raw = max(-res["token_delta"], 0)
        proceeds = res["sol_delta"]  # SOL change of wallet (after fees)
        pos = DATA["positions"].get(str(uid), {}).get(mint)
        pnl_text = ""
        if pos:
            if "raw" in pos:
                pos["raw"] = max(pos["raw"] - sold_raw, 0)
            if pos["cost_lamports"] > 0 and balance_before > 0:
                cost_removed = pos["cost_lamports"] * min(sold_raw, balance_before) // balance_before
                realized = proceeds - cost_removed
                pos["cost_lamports"] -= cost_removed
                pnl_text = f"\nRealized PnL: <b>{Decimal(realized) / LAMPORTS:+.4f} SOL</b>"
            if sold_raw >= balance_before:
                DATA["positions"][str(uid)].pop(mint, None)
            save_data()

        await edit(
            bot, ref,
            "✅ <b>Sell confirmed</b>\n\n"
            f"Sold: <b>{fmt_amount(sold_raw, res['decimals'])}</b>\n"
            f"Received: <b>{fmt_sol(proceeds)} SOL</b> (after fees){pnl_text}\n"
            f"{explorer_link(res['signature'])}",
            InlineKeyboardMarkup([[btn("📦 Positions", "m:pos"), btn("⬅️ Main Menu", "m:home")]]),
        )
    except Exception as exc:
        logger.exception("sell failed")
        await edit(bot, ref, f"❌ Sell failed:\n<code>{error_text(exc)}</code>", BACK_HOME)
    finally:
        BUSY.discard(uid)
# ============================================================
# END: TRADE EXECUTION
# ============================================================


# ============================================================
# START: AUTO BUY / AUTO SELL RULES
# ------------------------------------------------------------
# A rule = {id, side, mint, symbol, metric, op, value, amount}
#   side   : "buy" | "sell"
#   metric : "p" = price USD, "m" = market cap USD, "pnl" = PnL % (sell only)
#   op     : "le" (<=) | "ge" (>=)
#   amount : SOL to spend (buy) or % of balance to sell (sell)
# A rule fires ONCE, then it is deleted. A background loop checks all rules
# every RULE_INTERVAL seconds using one Dexscreener request.
# ============================================================
def user_rules(uid: int, side=None) -> list:
    return [r for r in DATA["rules"].get(str(uid), []) if side in (None, r["side"])]


def describe_condition(rule: dict) -> str:
    op = "≤" if rule["op"] == "le" else "≥"
    value = Decimal(rule["value"])
    if rule["metric"] == "p":
        return f"Price {op} {token_price(value)}"
    if rule["metric"] == "m":
        return f"Market Cap {op} {compact_money(value)}"
    return f"PnL {op} {value:+}%"


def describe_rule(rule: dict) -> str:
    sym = safe_text(rule["symbol"], 20)
    if rule["side"] == "buy":
        return f"BUY <b>{sym}</b> when {describe_condition(rule)} → {rule['amount']} SOL"
    return f"SELL {rule['amount']}% of <b>{sym}</b> when {describe_condition(rule)}"


async def show_rules(bot, ref, uid, side, note=""):
    rules = user_rules(uid, side)
    title = "🤖 Auto Buy" if side == "buy" else "🤖 Auto Sell"
    hint = ("Buys a token automatically when your condition is met."
            if side == "buy" else
            "Sells automatically (take profit / stop loss / price target).")
    lines = [f"{note}<b>{title}</b>\n<i>{hint}\nEach rule fires once, then it is removed.</i>\n"]
    if not rules:
        lines.append("<i>No active rules.</i>")
    for i, r in enumerate(rules, 1):
        lines.append(f"{i}. {describe_rule(r)}")
    buttons = [[btn("⬅️ Back", "m:home"), btn("➕ New Rule", f"rn:{side}")]]
    row = [btn(f"🗑 Delete {i}", f"rd:{r['id']}") for i, r in enumerate(rules, 1)]
    buttons += [row[i:i + 3] for i in range(0, len(row), 3)]
    await edit(bot, ref, "\n".join(lines), InlineKeyboardMarkup(buttons))


async def start_rule(bot, ref, context, uid, side, mint):
    """Step 1 done (mint known). Show current data and the condition buttons."""
    try:
        pair = await asyncio.to_thread(fetch_token, mint)
    except Exception:
        pair = None
    if pair is None:
        await edit(bot, ref, "⚠️ No Solana trading pair found for this mint.",
                   InlineKeyboardMarkup([[btn("⬅️ Back", f"ru:{side}")]]))
        return
    token = pair.get("baseToken") or {}
    symbol = token.get("symbol") or short(mint)
    context.user_data["draft"] = {"side": side, "mint": mint, "symbol": symbol}
    if side == "buy":
        options = [
            [btn("📉 Price ≤", "rc:p:le"), btn("📈 Price ≥", "rc:p:ge")],
            [btn("📉 Market Cap ≤", "rc:m:le"), btn("📈 Market Cap ≥", "rc:m:ge")],
        ]
    else:
        options = [
            [btn("🎯 Take Profit (PnL ≥)", "rc:pnl:ge"), btn("🛑 Stop Loss (PnL ≤)", "rc:pnl:le")],
            [btn("📈 Price ≥", "rc:p:ge"), btn("📉 Price ≤", "rc:p:le")],
            [btn("📈 Market Cap ≥", "rc:m:ge"), btn("📉 Market Cap ≤", "rc:m:le")],
        ]
    options.append([btn("❌ Cancel", f"ru:{side}")])
    await edit(
        bot, ref,
        f"🤖 <b>Auto {side.title()} - {safe_text(symbol, 20)}</b>\n"
        f"Price now: <b>{token_price(pair.get('priceUsd'))}</b>\n"
        f"Market cap: <b>{compact_money(pair.get('marketCap', pair.get('fdv')))}</b>\n\n"
        "Choose the condition:",
        InlineKeyboardMarkup(options),
    )


async def show_rule_amount(bot, ref, uid, draft):
    if draft["side"] == "buy":
        buttons = [btn(f"{a} SOL", f"ra:{a}") for a in get_presets(uid)]
        buttons.append(btn("✏️ Custom", "rx"))
        rows = [buttons[i:i + 3] for i in range(0, len(buttons), 3)]
        question = "How much SOL should it spend?"
    else:
        rows = [[btn("25%", "ra:25"), btn("50%", "ra:50"), btn("100%", "ra:100")]]
        question = "How much of your balance should it sell?"
    rows.append([btn("❌ Cancel", f"ru:{draft['side']}")])
    await edit(
        bot, ref,
        f"🤖 <b>Auto {draft['side'].title()} - {safe_text(draft['symbol'], 20)}</b>\n"
        f"Condition: <b>{describe_condition(draft)}</b>\n\n{question}",
        InlineKeyboardMarkup(rows),
    )


async def finalize_rule(bot, ref, context, uid, amount_text):
    draft = context.user_data.get("draft")
    if not draft or "value" not in draft:
        await edit(bot, ref, "Session expired. Please start again.", BACK_HOME)
        return
    if len(user_rules(uid)) >= MAX_RULES_PER_USER:
        await edit(bot, ref, f"❌ Rule limit reached ({MAX_RULES_PER_USER}). Delete one first.", BACK_HOME)
        return
    if draft["side"] == "buy":
        amount = parse_sol_amount(amount_text, MAX_TRADE_SOL)
        if amount is None:
            await show_rule_amount(bot, ref, uid, draft)
            return
        amount_str = format(amount.normalize(), "f")
    else:
        amount_str = str(int(amount_text))
    rule = {**draft, "id": uuid.uuid4().hex[:6], "amount": amount_str}
    DATA["rules"].setdefault(str(uid), []).append(rule)
    save_data()
    context.user_data.pop("draft", None)
    await show_rules(bot, ref, uid, rule["side"], note="✅ <b>Rule saved.</b>\n\n")


async def compute_pnl(uid: int, mint: str, price_usd, sol_usd):
    """PnL % from tracked cost and tracked token amount (no RPC call normally)."""
    pos = DATA["positions"].get(str(uid), {}).get(mint)
    if not pos or not pos.get("cost_lamports") or price_usd is None or not sol_usd:
        return None
    if not pos.get("raw"):  # older position: read balance once and remember it
        held = (await asyncio.to_thread(get_token_accounts, wallet_address(uid))).get(mint)
        if not held:
            return None
        pos["raw"], pos["decimals"] = held["raw"], held["decimals"]
        save_data()
    ui = Decimal(pos["raw"]) / Decimal(10 ** pos["decimals"])
    cost_sol = Decimal(pos["cost_lamports"]) / LAMPORTS
    value_sol = ui * price_usd / sol_usd
    return (value_sol - cost_sol) / cost_sol * 100


async def check_rules(bot):
    pending = [(int(u), r) for u, lst in DATA["rules"].items() for r in lst]
    if not pending:
        return
    mints = sorted({r["mint"] for _, r in pending})
    pairs = await asyncio.to_thread(fetch_best_pairs, mints)
    sol_usd = await asyncio.to_thread(get_sol_usd) if any(r["metric"] == "pnl" for _, r in pending) else None

    for uid, rule in pending:
        pair = pairs.get(rule["mint"])
        if not pair:
            continue
        price = number(pair.get("priceUsd"))
        if rule["metric"] == "p":
            current = price
        elif rule["metric"] == "m":
            current = number(pair.get("marketCap", pair.get("fdv")))
        else:
            current = await compute_pnl(uid, rule["mint"], price, sol_usd)
        if current is None:
            continue
        target = Decimal(rule["value"])
        hit = current <= target if rule["op"] == "le" else current >= target
        if not hit or uid in BUSY:
            continue

        # fire once: remove the rule first so it can never trigger twice
        DATA["rules"][str(uid)] = [r for r in DATA["rules"][str(uid)] if r["id"] != rule["id"]]
        save_data()
        msg = await bot.send_message(
            chat_id=uid,
            text=f"🤖 <b>Auto {rule['side'].title()} triggered</b>\n{describe_rule(rule)}\n"
                 "⏳ Executing...",
            parse_mode=ParseMode.HTML,
        )
        ref = (msg.chat_id, msg.message_id)
        if rule["side"] == "buy":
            await do_buy(bot, ref, uid, rule["mint"], Decimal(rule["amount"]))
        else:
            await do_sell(bot, ref, uid, rule["mint"], int(rule["amount"]))


async def rules_loop(app: Application):
    await asyncio.sleep(5)
    while True:
        try:
            await check_rules(app.bot)
        except Exception:
            logger.exception("rules check failed")
        await asyncio.sleep(RULE_INTERVAL)
# ============================================================
# END: AUTO BUY / AUTO SELL RULES
# ============================================================


# ============================================================
# START: ACCESS GATE (only ALLOWED_USER_IDS may use the bot)
# ============================================================
async def auth_gate(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user = update.effective_user
    if user and user.id in ALLOWED_USER_IDS:
        return
    if update.callback_query:
        await update.callback_query.answer("Not allowed", show_alert=True)
    elif update.effective_message:
        await update.effective_message.reply_text("⛔ This is a private bot.")
    raise ApplicationHandlerStop
# ============================================================
# END: ACCESS GATE
# ============================================================


# ============================================================
# START: /start AND TEXT MESSAGES
# ============================================================
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    context.user_data.pop("await", None)
    msg = await update.effective_message.reply_text("Loading...")
    await show_main(context.bot, (msg.chat_id, msg.message_id), update.effective_user.id)


async def on_text(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message = update.effective_message
    uid = update.effective_user.id
    text = message.text.strip()
    bot = context.bot
    aw = context.user_data.pop("await", None)

    # ----- no pending question: a pasted mint address opens the token card -----
    if not aw:
        if valid_solana_address(text):
            msg = await message.reply_text("🔎 Looking up token...")
            await show_token(bot, (msg.chat_id, msg.message_id), uid, text)
        else:
            await message.reply_text("Use the menu: /start")
        return

    ref = aw["ref"]
    kind = aw["kind"]
    try:  # keep the chat clean (and remove private keys immediately)
        await message.delete()
    except Exception:
        pass

    def retry_prompt(error):
        context.user_data["await"] = aw
        return f"{error}\n\n"

    cancel = lambda cb: InlineKeyboardMarkup([[btn("❌ Cancel", cb)]])

    # ----- wallet import -----
    if kind == "import":
        kp = parse_private_key(text)
        if kp is None:
            await edit(bot, ref, retry_prompt("❌ Invalid private key.") + IMPORT_PROMPT, cancel("m:home"))
            return
        save_wallet(uid, kp)
        await show_wallet(bot, ref, uid, note="✅ <b>Wallet imported.</b>\n\n")
        return

    # ----- token address for Buy -----
    if kind == "mint":
        if not valid_solana_address(text):
            await edit(bot, ref,
                       retry_prompt("❌ That is not a valid Solana address.") +
                       "🛒 <b>Buy</b>\nSend the token mint address.", cancel("m:home"))
            return
        await show_token(bot, ref, uid, text)
        return

    # ----- custom buy amount: buy IMMEDIATELY (or confirm if enabled) -----
    if kind == "buy_custom":
        amount = parse_sol_amount(text, MAX_TRADE_SOL)
        if amount is None:
            await edit(bot, ref,
                       retry_prompt(f"❌ Invalid amount (max {MAX_TRADE_SOL} SOL).") +
                       "Send a SOL amount, e.g. 0.025", cancel(f"tr:{aw['mint']}"))
            return
        if confirm_on(uid):
            await show_buy_confirm(bot, ref, uid, aw["mint"], amount)
        else:
            await do_buy(bot, ref, uid, aw["mint"], amount)
        return

    # ----- settings values -----
    if kind == "presets":
        values = []
        for part in re.split(r"[,\s]+", text):
            if not part:
                continue
            value = parse_sol_amount(part, MAX_TRADE_SOL)
            if value is None:
                values = []
                break
            values.append(format(value.normalize(), "f"))
        if not values or len(values) > 4:
            await edit(bot, ref,
                       retry_prompt(f"❌ Send 1 to 4 amounts (max {MAX_TRADE_SOL} SOL each).") +
                       "Example: 0.015, 0.025, 0.05, 0.1", cancel("m:settings"))
            return
        set_raw(uid, "buy_presets", ",".join(values))
        await show_settings(bot, ref, uid)
        return

    if kind in SETTING_PROMPTS:
        key, label, unit, maximum, minimum = SETTING_PROMPTS[kind]
        value = None
        try:
            value = Decimal(text)
            if not value.is_finite() or value < minimum or value > maximum:
                value = None
        except (InvalidOperation, ValueError):
            pass
        if value is None:
            await edit(bot, ref,
                       retry_prompt(f"❌ Invalid value (allowed {minimum} - {maximum} {unit}).") +
                       f"Send the new <b>{label}</b> ({unit}).", cancel("m:settings"))
            return
        set_setting(uid, key, value)
        await show_settings(bot, ref, uid)
        return

    # ----- auto rules -----
    if kind == "rule_mint":
        if not valid_solana_address(text):
            await edit(bot, ref,
                       retry_prompt("❌ That is not a valid Solana address.") +
                       f"🤖 <b>Auto {aw['side'].title()}</b>\nSend the token mint address.",
                       cancel(f"ru:{aw['side']}"))
            return
        await start_rule(bot, ref, context, uid, aw["side"], text)
        return

    if kind == "rule_value":
        draft = context.user_data.get("draft")
        if not draft:
            await edit(bot, ref, "Session expired. Please start again.", BACK_HOME)
            return
        value = parse_usd_value(text)
        if value is not None and draft["metric"] == "pnl" and value > 100000:
            value = None
        if value is None:
            await edit(bot, ref,
                       retry_prompt("❌ Invalid number.") + aw["prompt"], cancel(f"ru:{draft['side']}"))
            return
        if draft["metric"] == "pnl":  # stop loss is negative, take profit positive
            value = -value if draft["op"] == "le" else value
        draft["value"] = format(value, "f")
        await show_rule_amount(bot, ref, uid, draft)
        return

    if kind == "rule_amount":
        draft = context.user_data.get("draft")
        if not draft or parse_sol_amount(text, MAX_TRADE_SOL) is None:
            await edit(bot, ref,
                       retry_prompt(f"❌ Invalid amount (max {MAX_TRADE_SOL} SOL).") +
                       "Send the SOL amount to spend, e.g. 0.05",
                       cancel(f"ru:{(draft or {}).get('side', 'buy')}"))
            return
        await finalize_rule(bot, ref, context, uid, text)
# ============================================================
# END: /start AND TEXT MESSAGES
# ============================================================


# ============================================================
# START: BUTTON HANDLER (every inline button click lands here)
# ============================================================
async def on_button(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    uid = query.from_user.id
    data = query.data
    bot = context.bot
    ref = (query.message.chat_id, query.message.message_id)
    context.user_data.pop("await", None)  # any button cancels a pending question
    answered = False

    async def ans(text=None, alert=False):
        nonlocal answered
        if not answered:
            answered = True
            await query.answer(text, show_alert=alert)

    async def ask(kind, text, cancel_cb="m:home", **extra):
        context.user_data["await"] = {"kind": kind, "ref": ref, "prompt": text, **extra}
        await edit(bot, ref, text, InlineKeyboardMarkup([[btn("❌ Cancel", cancel_cb)]]))

    try:
        # ---------- MAIN MENU ----------
        if data in ("m:home", "m:refresh"):
            await ans("Refreshed" if data == "m:refresh" else None)
            await show_main(bot, ref, uid)

        elif data == "m:buy":
            await ans()
            if not wallet_address(uid):
                await edit(bot, ref, "🔑 Import a wallet first.",
                           InlineKeyboardMarkup([[btn("🔑 Import Wallet", "w:import")],
                                                 [btn("⬅️ Main Menu", "m:home")]]))
            else:
                await ask("mint", "🛒 <b>Buy</b>\n\nSend the <b>token mint address</b> you want to buy.")

        elif data in ("m:sell", "m:pos"):
            await ans()
            await show_positions(bot, ref, uid)

        elif data == "m:settings":
            await ans()
            await show_settings(bot, ref, uid)

        # ---------- WALLET ----------
        elif data == "w:import":
            await ans()
            await ask("import", IMPORT_PROMPT, cancel_cb="w:view" if wallet_address(uid) else "m:home")

        elif data == "w:view":
            await ans()
            await show_wallet(bot, ref, uid)

        elif data == "w:remove":
            await ans()
            await edit(bot, ref,
                       "🗑 <b>Remove wallet?</b>\nThe encrypted key and position history will be "
                       "deleted from this bot. Your funds stay on-chain.",
                       InlineKeyboardMarkup([[btn("✅ Yes, remove", "w:removeok"),
                                              btn("❌ Cancel", "w:view")]]))

        elif data == "w:removeok":
            await ans()
            remove_wallet(uid)
            await show_main(bot, ref, uid, note="✅ Wallet removed.\n\n")

        # ---------- SETTINGS ----------
        elif data == "st:presets":
            await ans()
            await ask("presets",
                      "⚡ <b>Quick Buy Amounts</b>\n\n"
                      f"Current: <b>{' / '.join(get_presets(uid))} SOL</b>\n"
                      "Send 1 to 4 amounts separated by commas, e.g.\n<code>0.015, 0.025, 0.05, 0.1</code>",
                      cancel_cb="m:settings")

        elif data == "st:confirm":
            await ans("Confirm Trades " + ("OFF" if confirm_on(uid) else "ON"))
            set_raw(uid, "confirm_trades", "0" if confirm_on(uid) else "1")
            await show_settings(bot, ref, uid)

        elif data.startswith("st:"):
            await ans()
            kind = data.split(":", 1)[1]
            key, label, unit, maximum, minimum = SETTING_PROMPTS[kind]
            await ask(kind, f"⚙️ <b>{label}</b>\n\nCurrent: <b>{get_setting(uid, key)} {unit}</b>\n"
                            f"Send the new value ({unit}), allowed {minimum} - {maximum}.",
                      cancel_cb="m:settings")

        # ---------- TOKEN CARD ----------
        elif data.startswith("tr:"):
            await ans("Refreshed")
            await show_token(bot, ref, uid, data.split(":", 1)[1])

        elif data.startswith("ta:"):  # quick-buy button: buys IMMEDIATELY
            _, amount, mint = data.split(":", 2)
            value = parse_sol_amount(amount, MAX_TRADE_SOL)
            if value is None:
                await ans(f"Amount exceeds the safety limit ({MAX_TRADE_SOL} SOL)", alert=True)
            elif confirm_on(uid):
                await ans()
                await show_buy_confirm(bot, ref, uid, mint, value)
            elif uid in BUSY:
                await ans("A trade is already in progress")
            else:
                await ans("Buying...")
                await do_buy(bot, ref, uid, mint, value)

        elif data.startswith("tc:"):
            await ans()
            mint = data.split(":", 1)[1]
            await ask("buy_custom", f"✏️ <b>Custom amount</b>\n\nSend the SOL amount to buy "
                                    f"(max {MAX_TRADE_SOL}), e.g. 0.025",
                      cancel_cb=f"tr:{mint}", mint=mint)

        # ---------- BUY / SELL EXECUTION ----------
        elif data.startswith("by:"):  # confirm button (only if Confirm Trades is ON)
            _, amount, mint = data.split(":", 2)
            value = parse_sol_amount(amount, MAX_TRADE_SOL)
            if uid in BUSY:
                await ans("A trade is already in progress")
            elif value is None:
                await ans("Invalid amount", alert=True)
            else:
                await ans("Buying...")
                await do_buy(bot, ref, uid, mint, value)

        elif data.startswith("pd:"):
            await ans()
            await show_position(bot, ref, uid, data.split(":", 1)[1])

        elif data.startswith("sl:"):  # sell 25/50/100 button: sells IMMEDIATELY
            _, pct, mint = data.split(":", 2)
            if confirm_on(uid):
                await ans()
                await show_sell_confirm(bot, ref, uid, mint, int(pct))
            elif uid in BUSY:
                await ans("A trade is already in progress")
            else:
                await ans("Selling...")
                await do_sell(bot, ref, uid, mint, int(pct))

        elif data.startswith("sx:"):  # confirm button (only if Confirm Trades is ON)
            _, pct, mint = data.split(":", 2)
            if uid in BUSY:
                await ans("A trade is already in progress")
            else:
                await ans("Selling...")
                await do_sell(bot, ref, uid, mint, int(pct))

        # ---------- AUTO BUY / AUTO SELL ----------
        elif data in ("ru:buy", "ru:sell"):
            await ans()
            context.user_data.pop("draft", None)
            await show_rules(bot, ref, uid, data.split(":", 1)[1])

        elif data.startswith("rn:"):  # new rule: rn:<side> or rn:<side>:<mint>
            await ans()
            parts = data.split(":")
            side = parts[1]
            if len(parts) == 3:
                await start_rule(bot, ref, context, uid, side, parts[2])
            else:
                await ask("rule_mint", f"🤖 <b>Auto {side.title()}</b>\n\nSend the <b>token mint address</b>.",
                          cancel_cb=f"ru:{side}", side=side)

        elif data.startswith("rc:"):  # condition chosen
            draft = context.user_data.get("draft")
            _, metric, op = data.split(":")
            if not draft:
                await ans("Session expired. Start again.", alert=True)
            elif metric == "pnl" and draft["mint"] not in DATA["positions"].get(str(uid), {}):
                await ans("No tracked cost for this token. Use a Price rule.", alert=True)
            else:
                await ans()
                draft["metric"], draft["op"] = metric, op
                if metric == "pnl":
                    prompt = ("🎯 <b>Take Profit</b>\nSend the profit % to sell at, e.g. <code>50</code>"
                              if op == "ge" else
                              "🛑 <b>Stop Loss</b>\nSend the loss % to sell at, e.g. <code>30</code>")
                elif metric == "p":
                    prompt = ("📈 Send the price (USD) at or above which to trigger, e.g. <code>0.0005</code>"
                              if op == "ge" else
                              "📉 Send the price (USD) at or below which to trigger, e.g. <code>0.0001</code>")
                else:
                    prompt = ("📈 Send the market cap (USD) at or above which to trigger, e.g. <code>100k</code>"
                              if op == "ge" else
                              "📉 Send the market cap (USD) at or below which to trigger, e.g. <code>20k</code>")
                await ask("rule_value", prompt, cancel_cb=f"ru:{draft['side']}")

        elif data.startswith("ra:"):  # amount chosen by button
            await ans()
            await finalize_rule(bot, ref, context, uid, data.split(":", 1)[1])

        elif data == "rx":  # custom SOL amount for an auto-buy rule
            draft = context.user_data.get("draft")
            await ans()
            await ask("rule_amount", f"✏️ Send the SOL amount to spend (max {MAX_TRADE_SOL}), e.g. 0.05",
                      cancel_cb=f"ru:{(draft or {}).get('side', 'buy')}")

        elif data.startswith("rd:"):
            await ans("Deleted")
            rule_id = data.split(":", 1)[1]
            side = next((r["side"] for r in user_rules(uid) if r["id"] == rule_id), "buy")
            DATA["rules"][str(uid)] = [r for r in user_rules(uid) if r["id"] != rule_id]
            save_data()
            await show_rules(bot, ref, uid, side)

        await ans()
    except Exception:
        logger.exception("button failed: %s", data)
        await ans("Something went wrong, try again", alert=False)
# ============================================================
# END: BUTTON HANDLER
# ============================================================


# ============================================================
# START: APP SETUP
# ============================================================
async def on_error(update, context: ContextTypes.DEFAULT_TYPE):
    logger.error("Unhandled error", exc_info=context.error)


async def post_init(application: Application):
    application.create_task(rules_loop(application))  # background Auto Buy/Sell checker


def main():
    global fernet
    if not BOT_TOKEN:
        raise RuntimeError("Set TELEGRAM_BOT_TOKEN in the .env file.")
    if not ALLOWED_USER_IDS:
        raise RuntimeError("Set ALLOWED_USER_IDS in the .env file (your Telegram user id).")
    if not ENC_KEY:
        raise RuntimeError(
            "Set WALLET_ENCRYPTION_KEY in .env. Generate one with:\n"
            "python -c \"from cryptography.fernet import Fernet; print(Fernet.generate_key().decode())\""
        )
    fernet = Fernet(ENC_KEY.encode())
    load_data()

    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .concurrent_updates(True)   # handle clicks immediately, no waiting in a queue
        .post_init(post_init)
        .build()
    )
    app.add_handler(TypeHandler(Update, auth_gate), group=-1)
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CallbackQueryHandler(on_button))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_text))
    app.add_error_handler(on_error)

    logger.info("Starting Solana Trading Bot...")
    app.run_polling()


if __name__ == "__main__":
    main()
# ============================================================
# END: APP SETUP
# ============================================================
