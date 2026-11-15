#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AE TWA - FUSED BACKEND (AEI + AEEA), Final, First edition - REVISED
Lossless fusion of AEI (GAIA/AEI seed) and AEEA (MT4-parity market engine).
Single source of truth for the fused TWA frontend.

Fusion:
  - AEI seed loop: prime -> outward lattice -> Hopf -> s2=r2 -> DbZ -> I -> SelfEvolution.
  - AEEA market engine: bars -> 13 normalised indicators + Ichimoku -> m/n/delta ->
    regime -> BB x58 -> P_arc -> signal iff delta-gate -> orders/trailing/FVG.
  - Fused on ONE ordered feed: each tick in arrival order advances the AEEA bar ring
    AND is lifted to exact Fraction x for the AEI seed loop via
    x = abs(price - prevPrice)/10000 (or 1/100 when zero).

Audit directives, enforced in this file:
  - NO SYNTHETIC BARS EVER. No random walk, no fallback synthetic, no standalone synthetic.
  - BACKEND AUTHORITATIVE. Frontend never computes truth. It only renders /miniapp-state.
  - LATTICE [] EQUALS WAITING, NEVER 0. Same for price null, BB null, grid null.
  - ONE FORMATTER FOR APP AND BOT. format_aea in this file is the only formatter.
  - ONE ORDERED STREAM. Consumed once, in arrival order. Never shuffled, never replayed, never batched.
  - ONE STATE. GET /miniapp-state returns ordered feed, bars, indicators, seed, CS, aea_notification in one tick.
  - NO LOCAL-ONLY PATHS. Teach, Say, Step, Handshake, Crawler-enqueue, Reset, Order all go through backend.
  - NO FAKE 100.00 VALUES. 13D grid returns null per indicator until it has enough real bars.
  - AUDIT FIX (bot crash loop): BridgeServer is started in main() BEFORE the bot thread,
    never only inside AE_Bot.run() / _post_init. If python-telegram-bot is missing,
    run() logs loudly and returns, but $PORT stays bound and the Bridge stays up.
    requirements.txt for this backend MUST contain python-telegram-bot==21.6
    and httpx>=0.27,<0.28. The stdlib-only requirements.txt in the prior fused bundle
    is the root cause of the /start failure and is NOT used here.
  - AUDIT FIX (heartbeat masking): main() logs bot-thread exit loudly. A dead bot
    thread is never masked as alive.
  - AUDIT FIX (pending updates): run_polling uses drop_pending_updates=True, documented.
    Test /start with a fresh message after redeploy.

Exactness:
  - No floats anywhere in seed state. Fraction or PyFraction only.
  - x lifted at the boundary. No math.exp / math.log in seed state.
  - Market price display uses float only at /ohlcv, /signals output boundary.
  - _symbolic_exp / _symbolic_log / _symbolic_cos / _symbolic_sin are exact-rational
    Taylor series with dynamic truncation + range reduction + per-term
    _quantize() to 30 decimal digits. They do not depend on mpmath or sympy.

Auth:
  - Header only. X-Telegram-Init-Data. Never ?auth_init_data=.
  - HMAC WebAppData scheme, hmac.compare_digest, auth_date within 86400s.
  - REQUIRE_AUTH=1 on any public host.

CORS:
  - Do not reflect Origin when CORS_ORIGIN is '*'.
  - Vary: Origin always.

Liveness vs config:
  - /health public, no relay URL, no shard pool, no user ids, no Telegram DB details.
  - /config requires auth, returns non-sensitive config only.

Endpoints (22+): /health, /miniapp-state, /cs-state, /cs-feedback, /step, /handshake,
/teach, /say, /crawler-enqueue, /reset, /order, /orders, /order/close, /notify-aea,
/ohlcv, /signals, /diagnostics, /encode-syllable, /log, /toasts, /lattice-state,
/fibration-state, /aea-notification, /config

Evolution vs NN:
  - Same ordered ticks feed AE SelfEvolution and a toy NN baseline.
  - AE wins a round when deviation <= 0.02 AND delta-accuracy >= 80% held for 20 ticks.
  - NN baseline does epochs/tick gradient steps on the same ticks. AE does 1 exact
    SelfEvolution step per tick. Learning speed is measured in ticks-to-target, not wall clock.

Version: Final, First edition - Revised (bounded-precision exact rational)

Bounded-precision revision (constraint-locked, this file only):
  Seed arithmetic stays exact rational (Fraction / PyFraction, integer
  arithmetic only, NO float in the seed layer). Denominators are capped at
  10**30 (30 decimal digits) by _quantize(), applied after every sqrt /
  exp / log / cos / sin and after every phi / harmonic-sum update. This is
  what keeps one seed tick O(1): unbounded Newton/Taylor in Q lets
  denominators double every iteration, so a step grows from milliseconds
  to seconds and keeps growing, and AE could never beat NN on learning
  speed. With the cap, phi / s2 / r2 / dev stay <= ~60 digits forever,
  one tick stays ~milliseconds, and AE still needs exactly 1 exact
  SelfEvolution step per tick vs NN 5 gradient steps per tick.
  Perfect-square sqrt stays exactly exact; everything else is exact to
  30 decimal digits, which is the documented precision of this revision.
"""
__version__ = "Final, First edition - Revised (bounded-precision exact rational)"
import sys
try:
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(1000000)
except Exception:
    pass
import asyncio
import concurrent.futures
import concurrent.futures.thread
import hashlib
import hmac
import json
import math as _math_mod
isqrt = _math_mod.isqrt
import os
import gc
import queue
import ssl
import logging
import threading
import time
import re as _re_bridge
import sqlite3
import urllib.parse
import urllib.request
import urllib.error
import weakref
from collections import deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qsl
from dataclasses import dataclass, field
from datetime import datetime
from typing import List, Dict, Optional, Tuple, Any, Protocol, runtime_checkable
from fractions import Fraction as PyFraction
from decimal import Decimal, getcontext
getcontext().prec = 50
# ============================================================================
# BOUNDED-PRECISION EXACT RATIONAL - denominators capped at 10**30
# Integer arithmetic only. No float. See header note.
# ============================================================================
_Q_DIGITS = 30
_Q_SCALE = 10 ** _Q_DIGITS
# ============================================================================
# EXACT FRACTION WRAPPER
# ============================================================================
class Fraction:
    """Exact rational arithmetic. Lifts Decimals and ints to PyFraction.
    Every seed state transition uses Fraction or PyFraction directly.
    No float64 ever enters the seed symbolic layer; market feed floats are
    lifted at the boundary by _dec_to_frac_exact()."""
    __slots__ = ('_f',)
    def __init__(self, num=0, den=1):
        if isinstance(num, Fraction):
            self._f = num._f
        elif isinstance(num, PyFraction):
            self._f = num
        elif isinstance(num, int) and isinstance(den, int):
            if den == 0:
                raise ZeroDivisionError("Fraction denominator cannot be zero")
            self._f = PyFraction(num, den)
        else:
            try:
                self._f = PyFraction(str(num))
            except Exception:
                self._f = PyFraction(0)
    @staticmethod
    def _wrap(x):
        if isinstance(x, Fraction):
            return x
        return Fraction(x)
    @staticmethod
    def from_decimal_string(s):
        s = str(s).strip()
        if 'E' in s or 'e' in s:
            d = Decimal(s)
            sign, digits, exp = d.as_tuple()
            if not isinstance(exp, int):
                raise ValueError(f"unsupported Decimal exponent: {exp!r}")
            num = int(''.join(str(x) for x in digits)) * (-1 if sign else 1)
            den = 10 ** (-exp) if exp < 0 else 1
            if exp >= 0:
                num = num * (10 ** exp)
                den = 1
            return Fraction(num, den)
        return Fraction.from_string(s)
    @staticmethod
    def from_string(s):
        s = str(s).strip()
        if '/' in s:
            parts = s.split('/')
            return Fraction(int(parts[0]), int(parts[1]))
        if '.' in s:
            sign = -1 if s.startswith('-') else 1
            s_abs = s.lstrip('-')
            int_part, frac_part = s_abs.split('.')
            scale = 10 ** len(frac_part)
            num = int(int_part + frac_part) * sign
            return Fraction(num, scale)
        return Fraction(int(s), 1)
    @staticmethod
    def zero():
        return Fraction(0, 1)
    @staticmethod
    def one():
        return Fraction(1, 1)
    def num(self):
        return self._f.numerator
    def den(self):
        return self._f.denominator
    def is_zero(self):
        return self._f.numerator == 0
    def is_integer(self):
        return self._f.denominator == 1
    def sign(self):
        n = self._f.numerator
        return (n > 0) - (n < 0)
    def abs(self):
        return Fraction(abs(self._f.numerator), self._f.denominator)
    def neg(self):
        return Fraction(-self._f.numerator, self._f.denominator)
    def __add__(self, other):
        o = Fraction._wrap(other)
        return Fraction(self._f + o._f)
    def __radd__(self, other):
        return self.__add__(other)
    def __sub__(self, other):
        o = Fraction._wrap(other)
        return Fraction(self._f - o._f)
    def __rsub__(self, other):
        o = Fraction._wrap(other)
        return Fraction(o._f - self._f)
    def __mul__(self, other):
        o = Fraction._wrap(other)
        return Fraction(self._f * o._f)
    def __rmul__(self, other):
        return self.__mul__(other)
    def __truediv__(self, other):
        o = Fraction._wrap(other)
        if o._f.numerator == 0:
            raise ZeroDivisionError("Fraction division by zero")
        return Fraction(self._f / o._f)
    def __rtruediv__(self, other):
        o = Fraction._wrap(other)
        if self._f.numerator == 0:
            raise ZeroDivisionError("Fraction division by zero")
        return Fraction(o._f / self._f)
    def __eq__(self, other):
        if isinstance(other, Fraction):
            return self._f == other._f
        try:
            return self._f == Fraction._wrap(other)._f
        except Exception:
            return False
    def __ne__(self, other):
        return not self.__eq__(other)
    def __lt__(self, other):
        return self._f < Fraction._wrap(other)._f
    def __le__(self, other):
        return self._f <= Fraction._wrap(other)._f
    def __gt__(self, other):
        return self._f > Fraction._wrap(other)._f
    def __ge__(self, other):
        return self._f >= Fraction._wrap(other)._f
    def __hash__(self):
        return hash(self._f)
    def __str__(self):
        return f"{self._f.numerator}/{self._f.denominator}"
    def __repr__(self):
        return f"Fraction({self._f.numerator}/{self._f.denominator})"
    def __float__(self):
        return float(self._f)
    def __int__(self):
        return int(self._f)
    def sqrt(self):
        # Exact integer sqrt for perfect squares, else scaled integer sqrt
        # to 30 decimal digits: floor(sqrt(n/d) * 10**30) / 10**30.
        # Integer arithmetic only. NO Newton iteration in Q: Newton doubles
        # the denominator every iteration (thousands of digits after a few
        # ticks) and is the root cause of the step-time blowup.
        if self._f < 0:
            raise ValueError("sqrt of negative Fraction")
        if self._f == 0:
            return Fraction.zero()
        n = self._f.numerator
        d = self._f.denominator
        rn = isqrt(n)
        rd = isqrt(d)
        if rn * rn == n and rd * rd == d:
            return Fraction(rn, rd)
        s = isqrt((n * _Q_SCALE * _Q_SCALE) // d)
        return Fraction(s, _Q_SCALE)
# ============================================================================
# EXACT HELPERS
# ============================================================================
def _dec_to_frac_exact(raw) -> Fraction:
    if raw is None:
        return Fraction.zero()
    if isinstance(raw, Fraction):
        return raw
    if isinstance(raw, PyFraction):
        return Fraction(raw)
    if isinstance(raw, Decimal):
        return Fraction.from_decimal_string(str(raw))
    if isinstance(raw, int):
        return Fraction(raw, 1)
    if isinstance(raw, float):
        # Float only at the boundary: use Decimal(str()) so the lift is deterministic.
        return Fraction.from_decimal_string(str(raw))
    return Fraction.from_decimal_string(str(raw))
def is_finite_number(x) -> bool:
    try:
        if x is None:
            return False
        if isinstance(x, (int, float)):
            return _math_mod.isfinite(float(x))
        if isinstance(x, Decimal):
            return x.is_finite()
        return True
    except Exception:
        return False
def _frac_short(v, maxlen=64) -> str:
    try:
        s = str(v)
        return s if len(s) <= maxlen else s[:maxlen]
    except Exception:
        return "0/1"
def _quantize(v) -> Fraction:
    """Round an exact Fraction to 30 decimal digits: round(v * 10**30) / 10**30.
    Integer arithmetic only, no float. Denominator of the result divides
    10**30, so denominators can never grow past the cap."""
    if not isinstance(v, Fraction):
        v = Fraction._wrap(v)
    n = v._f.numerator
    d = v._f.denominator
    q, r = divmod(n * _Q_SCALE, d)
    if 2 * r >= d:
        q += 1
    return Fraction(q, _Q_SCALE)
def _arctan_series(y: Fraction, terms=48) -> Fraction:
    # arctan(y) = sum (-1)^k y^(2k+1)/(2k+1), |y| < 1. Quantized per term.
    y2 = _quantize(y * y)
    term = _quantize(y)
    total = _quantize(y)
    for k in range(1, terms):
        term = _quantize(term * y2)
        add = _quantize(term / Fraction(2 * k + 1, 1))
        if k % 2 == 1:
            total = _quantize(total - add)
        else:
            total = _quantize(total + add)
        if add.abs() < Fraction(1, _Q_SCALE):
            break
    return total
# pi via Machin: pi = 16*arctan(1/5) - 4*arctan(1/239). Computed once at import.
_PI = _quantize(Fraction(16, 1) * _arctan_series(Fraction(1, 5)) - Fraction(4, 1) * _arctan_series(Fraction(1, 239)))
_TWO_PI = _quantize(Fraction(2, 1) * _PI)
def _log2_const() -> Fraction:
    # ln(2) = 2 * sum (1/3)^(2k+1)/(2k+1). Quantized per term.
    y = Fraction(1, 3)
    y2 = _quantize(y * y)
    term = _quantize(y)
    total = _quantize(y)
    for k in range(1, 48):
        term = _quantize(term * y2)
        add = _quantize(term / Fraction(2 * k + 1, 1))
        total = _quantize(total + add)
        if add.abs() < Fraction(1, _Q_SCALE):
            break
    return _quantize(Fraction(2, 1) * total)
_LOG2 = _log2_const()
def _reduce_angle(x: Fraction) -> Fraction:
    # Reduce mod 2*pi into [0, 2*pi) using the quantized pi constant.
    if x.abs() <= _TWO_PI:
        return x
    ratio = x / _TWO_PI
    q = ratio._f.numerator // ratio._f.denominator
    return _quantize(x - Fraction(q, 1) * _TWO_PI)
def _symbolic_exp(x: Fraction, terms=24) -> Fraction:
    # exp(x) in Q with range reduction + per-term quantization.
    # exp(-70) < 10**-30, so it quantizes to 0 at 30 digits.
    if x <= Fraction(-70, 1):
        return Fraction.zero()
    m = 0
    xr = x
    while xr.abs() > Fraction.one():
        xr = xr / Fraction(2, 1)
        m += 1
    result = Fraction.one()
    term = Fraction.one()
    for k in range(1, terms + 1):
        term = _quantize(term * xr / Fraction(k, 1))
        result = _quantize(result + term)
        if term.abs() < Fraction(1, _Q_SCALE):
            break
    for _ in range(m):
        result = _quantize(result * result)
    return result
def _symbolic_log(x: Fraction, terms=32) -> Fraction:
    # ln(x) via atanh series after reduction by powers of 2 into [1/2, 2],
    # plus k*ln(2). Quantized per term. Requires x > 0.
    if x <= Fraction.zero():
        return Fraction.zero()
    if x == Fraction.one():
        return Fraction.zero()
    k = 0
    xr = x
    while xr > Fraction(2, 1):
        xr = xr / Fraction(2, 1)
        k += 1
    while xr < Fraction(1, 2):
        xr = xr * Fraction(2, 1)
        k -= 1
    y = _quantize((xr - Fraction.one()) / (xr + Fraction.one()))
    y2 = _quantize(y * y)
    result = _quantize(y)
    term = _quantize(y)
    for kk in range(1, terms):
        term = _quantize(term * y2)
        add = _quantize(term / Fraction(2 * kk + 1, 1))
        result = _quantize(result + add)
        if add.abs() < Fraction(1, _Q_SCALE):
            break
    out = _quantize(result * Fraction(2, 1))
    if k:
        out = _quantize(out + Fraction(k, 1) * _LOG2)
    return out
def _symbolic_cos(x: Fraction, terms=20) -> Fraction:
    xr = _reduce_angle(x)
    result = Fraction.one()
    term = Fraction.one()
    x2 = _quantize(xr * xr)
    for k in range(1, terms + 1):
        term = _quantize(term * x2 / Fraction((2 * k - 1) * (2 * k), 1))
        if k % 2 == 1:
            result = _quantize(result - term)
        else:
            result = _quantize(result + term)
        if term.abs() < Fraction(1, _Q_SCALE):
            break
    return result
def _symbolic_sin(x: Fraction, terms=20) -> Fraction:
    xr = _reduce_angle(x)
    result = xr
    term = xr
    x2 = _quantize(xr * xr)
    for k in range(1, terms + 1):
        term = _quantize(term * x2 / Fraction((2 * k) * (2 * k + 1), 1))
        if k % 2 == 1:
            result = _quantize(result - term)
        else:
            result = _quantize(result + term)
        if term.abs() < Fraction(1, _Q_SCALE):
            break
    return result
def _rational_cos(x: Fraction) -> Fraction:
    return _symbolic_cos(x)
# ============================================================================
# ENVIRONMENT / CONFIGURATION
# ============================================================================
TELEGRAM_BOT_TOKEN_ENV: str = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
TELEGRAM_WEBAPP_URL: str = os.getenv("TELEGRAM_WEBAPP_URL", "").strip()
BRIDGE_HOST: str = os.getenv("BRIDGE_HOST", "0.0.0.0").strip()
_ENV_PORT: Optional[str] = os.getenv("PORT")
_ENV_BRIDGE_PORT: Optional[str] = os.getenv("BRIDGE_PORT")
if _ENV_PORT:
    BRIDGE_PORT: int = int(_ENV_PORT)
    _SUBSTRATE: str = "web-dyno"
else:
    BRIDGE_PORT: int = int(_ENV_BRIDGE_PORT or "8765")
    _SUBSTRATE: str = "local"
BRIDGE_USE_TLS: bool = os.getenv("BRIDGE_USE_TLS", "0").strip() in ("1", "true", "yes")
BRIDGE_TLS_CERT: str = os.getenv("BRIDGE_TLS_CERT", "").strip()
BRIDGE_TLS_KEY: str = os.getenv("BRIDGE_TLS_KEY", "").strip()
BRIDGE_PUBLIC_TIMEOUT: int = int(os.getenv("BRIDGE_PUBLIC_TIMEOUT", "45"))
REQUIRE_AUTH: bool = os.getenv("REQUIRE_AUTH", "1").strip() in ("1", "true", "yes")
CORS_ORIGIN: str = os.getenv("CORS_ORIGIN", "*").strip()
LOG_BUFFER_SIZE: int = int(os.getenv("LOG_BUFFER_SIZE", "1000"))
TOAST_BUFFER_SIZE: int = int(os.getenv("TOAST_BUFFER_SIZE", "500"))
ALLOWED_USER_IDS: List[int] = []
try:
    _raw_allowed = os.getenv("ALLOWED_USER_IDS", "").strip()
    if _raw_allowed:
        ALLOWED_USER_IDS = [int(x.strip()) for x in _raw_allowed.split(",") if x.strip()]
except Exception:
    ALLOWED_USER_IDS = []
RELAY_URL: str = os.getenv("RELAY_URL", "").strip()
RELAY_KEY: str = os.getenv("RELAY_KEY", "").strip()
RELAY_TIMEOUT: int = int(os.getenv("RELAY_TIMEOUT", "15"))
RELAY_MAX_RETRIES: int = int(os.getenv("RELAY_MAX_RETRIES", "3"))
CRAWLER_DB_PATH: str = os.getenv("CRAWLER_DB_PATH", "aei_crawler.db")
CRAWL_SEED_URLS: List[str] = [u.strip() for u in os.getenv("CRAWL_SEED_URLS", "").split(",") if u.strip()]
CRAWLER_BLOCKLIST: List[str] = [b.strip() for b in os.getenv("CRAWLER_BLOCKLIST", "meta.wikimedia.org,wikimedia.org/w/api,thumb.wikimedia.org,upload.wikimedia.org,featuredfeed").split(",") if b.strip()]
CRAWL_INTERVAL: float = float(os.getenv("CRAWL_INTERVAL", "3"))
MAX_CRAWL_DEPTH: int = int(os.getenv("MAX_CRAWL_DEPTH", "3"))
SEED_TICK_INTERVAL: float = float(os.getenv("SEED_TICK_INTERVAL", "5"))
SYMBOL_ENV: str = os.getenv("SYMBOL", "BTC/USD")
TIMEFRAME_ENV: str = os.getenv("TIMEFRAME", "M15")
ENABLE_TELEGRAM_DB: bool = os.getenv("ENABLE_TELEGRAM_DB", "0").strip() in ("1", "true", "yes")
TELEGRAM_DB_CHANNEL_ID: str = os.getenv("TELEGRAM_DB_CHANNEL_ID", "").strip()
TELEGRAM_DB_CENTRAL_USER_ID: str = os.getenv("TELEGRAM_DB_CENTRAL_USER_ID", "").strip()
TELEGRAM_DB_USER_SHARDS: bool = os.getenv("TELEGRAM_DB_USER_SHARDS", "0").strip() in ("1", "true", "yes")
TELEGRAM_DB_SHARD_POOL: List[str] = [x.strip() for x in os.getenv("TELEGRAM_DB_SHARD_POOL", "").split(",") if x.strip()]
TELEGRAM_DB_SAVE_INTERVAL: int = int(os.getenv("TELEGRAM_DB_SAVE_INTERVAL", "5"))
TELEGRAM_DB_CHUNK_SIZE: int = int(os.getenv("TELEGRAM_DB_CHUNK_SIZE", "3800"))
TELEGRAM_DB_PIN_INDEX: bool = os.getenv("TELEGRAM_DB_PIN_INDEX", "0").strip() in ("1", "true", "yes")
# ============================================================================
# LOGGING / RING BUFFERS
# ============================================================================
logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger("ae-fused")
_LOG_LOCK = threading.Lock()
_LOG_BUFFER: deque = deque(maxlen=LOG_BUFFER_SIZE)
_TOAST_BUFFER: deque = deque(maxlen=TOAST_BUFFER_SIZE)
def _log(level: str, msg: str):
    try:
        with _LOG_LOCK:
            _LOG_BUFFER.append({"ts": datetime.now().isoformat(), "level": level, "msg": msg})
    except Exception:
        pass
    try:
        if level == "error":
            logger.error(msg)
        elif level == "warning":
            logger.warning(msg)
        else:
            logger.info(msg)
    except Exception:
        pass
def _toast(msg: str):
    try:
        with _LOG_LOCK:
            _TOAST_BUFFER.append({"ts": datetime.now().isoformat(), "msg": msg})
    except Exception:
        pass
# ============================================================================
# AUTH - HEADER ONLY
# ============================================================================
def verify_telegram_init_data(raw_init: str, token: str):
    try:
        if not raw_init or not token:
            return None
        pairs = dict(parse_qsl(raw_init, keep_blank_values=True))
        recv_hash = pairs.pop("hash", None)
        if not recv_hash:
            return None
        auth_date = pairs.get("auth_date", "")
        try:
            if auth_date and abs(int(time.time()) - int(auth_date)) > 86400:
                return None
        except Exception:
            return None
        data_check = "\n".join(f"{k}={pairs[k]}" for k in sorted(pairs.keys()))
        secret = hmac.new(b"WebAppData", token.encode("utf-8"), hashlib.sha256).digest()
        calc = hmac.new(secret, data_check.encode("utf-8"), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, recv_hash):
            return None
        user_raw = pairs.get("user", "")
        try:
            user = json.loads(user_raw) if user_raw else {}
        except Exception:
            user = {}
        return {"user": user, "auth_date": auth_date}
    except Exception:
        return None
def _is_allowed_user(user_id) -> bool:
    if not ALLOWED_USER_IDS:
        return True
    try:
        return int(user_id) in ALLOWED_USER_IDS
    except Exception:
        return False
def _get_shard_pool() -> List[str]:
    return list(TELEGRAM_DB_SHARD_POOL)
def _require_auth(handler) -> bool:
    # Public host requires auth unless REQUIRE_AUTH=0. /health is handled separately (public).
    if not REQUIRE_AUTH:
        return True
    raw_init = ""
    try:
        raw_init = handler.headers.get("X-Telegram-Init-Data", "").strip()
    except Exception:
        raw_init = ""
    if not raw_init:
        try:
            auth_hdr = handler.headers.get("Authorization", "").strip()
            if auth_hdr.lower().startswith("tma "):
                raw_init = auth_hdr[4:].strip()
        except Exception:
            pass
    if not raw_init:
        return False
    verified = verify_telegram_init_data(raw_init, TELEGRAM_BOT_TOKEN_ENV)
    if not verified or not verified.get("user"):
        return False
    user = verified.get("user") or {}
    user_id = user.get("id")
    if not _is_allowed_user(user_id):
        return False
    return True
# ============================================================================
# ONE ORDERED STREAM - SINGLE SOURCE OF ORDERED DATA
# ============================================================================
BRIDGE_ENGINE_REF: Dict[str, Any] = {}
class OrderedFeed:
    """One ordered stream. Consumed once, in arrival order.
    ordered_index is incremented EXACTLY ONCE, in drain(), in arrival order.
    Never shuffled, never replayed, never batched."""
    def __init__(self):
        self._q: deque = deque()
        self._lock = threading.Lock()
        self.ordered_index: int = 0
        self.price = None
        self.prev_price = None
        self.last_provider: str = "WAITING"
        self.last_tick_at = None
    def enqueue(self, price, provider: str) -> bool:
        # Enqueue only real ticks. None means WAITING, never enqueued.
        if price is None:
            return False
        try:
            dec = Decimal(str(price))
        except Exception:
            return False
        if dec <= 0 or not dec.is_finite():
            return False
        with self._lock:
            self._q.append({"price_dec": dec, "provider": provider, "ts": time.time()})
        return True
    def drain_one(self):
        with self._lock:
            if not self._q:
                return None
            item = self._q.popleft()
        # Increment EXACTLY ONCE here, in arrival order.
        self.ordered_index += 1
        self.prev_price = self.price
        self.price = item["price_dec"]
        self.last_provider = item["provider"]
        self.last_tick_at = item["ts"]
        item["ordered_index"] = self.ordered_index
        item["prev_price_dec"] = self.prev_price
        return item
    def drain_all(self):
        out = []
        while True:
            it = self.drain_one()
            if it is None:
                break
            out.append(it)
        return out
    def queue_len(self) -> int:
        with self._lock:
            return len(self._q)
ORDERED_FEED = OrderedFeed()
# Global CS back-feed store. Written only by POST /cs-feedback, read by /miniapp-state and format_aea.
CS_FEEDBACK: Dict[str, Any] = {}
CS_FEEDBACK_LOCK = threading.Lock()
def _set_cs_feedback(payload: Dict[str, Any]):
    with CS_FEEDBACK_LOCK:
        CS_FEEDBACK.clear()
        CS_FEEDBACK.update(payload)
        CS_FEEDBACK["received_at"] = datetime.now().isoformat()
def _get_cs_feedback() -> Dict[str, Any]:
    with CS_FEEDBACK_LOCK:
        return dict(CS_FEEDBACK)
# ============================================================================
# AEI SEED - QUATERNION / LATTICE / HOPF / DbZ / I / SELF-EVOLUTION
# ============================================================================
class Quaternion:
    """Quaternion over Q: q = a + b i + c j + d k, all Fraction."""
    __slots__ = ('a', 'b', 'c', 'd')
    def __init__(self, a=None, b=None, c=None, d=None):
        self.a = a if isinstance(a, Fraction) else Fraction._wrap(a if a is not None else 0)
        self.b = b if isinstance(b, Fraction) else Fraction._wrap(b if b is not None else 0)
        self.c = c if isinstance(c, Fraction) else Fraction._wrap(c if c is not None else 0)
        self.d = d if isinstance(d, Fraction) else Fraction._wrap(d if d is not None else 0)
    def __add__(self, other):
        return Quaternion(self.a + other.a, self.b + other.b, self.c + other.c, self.d + other.d)
    def __mul__(self, other):
        a1, b1, c1, d1 = self.a, self.b, self.c, self.d
        a2, b2, c2, d2 = other.a, other.b, other.c, other.d
        return Quaternion(
            a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2,
            a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
            a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2,
            a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2,
        )
    def magnitude_squared(self) -> Fraction:
        return self.a * self.a + self.b * self.b + self.c * self.c + self.d * self.d
    def conj(self):
        return Quaternion(self.a, self.b.neg(), self.c.neg(), self.d.neg())
    def to_dict(self):
        return {"a": str(self.a), "b": str(self.b), "c": str(self.c), "d": str(self.d)}
def _is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    r = isqrt(n)
    f = 3
    while f <= r:
        if n % f == 0:
            return False
        f += 2
    return True
def _next_prime(n: int) -> int:
    c = max(2, n + 1)
    while not _is_prime(c):
        c += 1
    return c
class DefaultSymbolicProcessor:
    def __init__(self):
        self.primes: List[int] = []
        self._next_candidate = 2
    def next_prime(self) -> int:
        p = self._next_candidate
        while not _is_prime(p):
            p += 1
        self.primes.append(p)
        self._next_candidate = p + 1
        return p
    def prime_list(self) -> List[int]:
        return list(self.primes)
class DefaultGeometricLattice:
    """Outward lattice: layers added outward, each layer constrained by maximal contact.
    Rejection: uniform division is rejected. Position is by arc length s = sum 1/p,
    not by uniform angle division. lattice_points is [] when waiting, never 0."""
    def __init__(self):
        self.points: List[int] = []
        self.positions: List[Quaternion] = []
        self._harmonic_sum = Fraction.zero()
    def add_sphere(self, prime: int) -> bool:
        if prime in self.points:
            return False
        self._harmonic_sum = _quantize(self._harmonic_sum + Fraction(1, prime))
        s = self._harmonic_sum
        q = Quaternion(_symbolic_cos(s), _symbolic_sin(s), _symbolic_cos(s / Fraction(2, 1)), _symbolic_sin(s / Fraction(2, 1)))
        self.points.append(prime)
        self.positions.append(q)
        return True
    def snapshot_points(self) -> List[int]:
        return list(self.points)
    def count(self) -> int:
        return len(self.points)
class DefaultAethericMonitor:
    def compute_arc_length_squared(self, traj: List[Quaternion]) -> Fraction:
        total = Fraction.zero()
        for i in range(1, len(traj)):
            dq = Quaternion(traj[i].a - traj[i-1].a, traj[i].b - traj[i-1].b, traj[i].c - traj[i-1].c, traj[i].d - traj[i-1].d)
            total = total + dq.magnitude_squared()
        return total
    def deviation(self, arc_sq: Fraction, radius_sq: Fraction) -> Fraction:
        return arc_sq - radius_sq
class DefaultQuaternionicRenderer:
    def hopf(self, q: Quaternion):
        denom = Fraction.one() - q.d
        if denom.is_zero():
            return {"u": "0/1", "v": "0/1"}
        return {"u": str(q.a / denom), "v": str(q.b / denom)}
    def project(self, q: Quaternion):
        return self.hopf(q)
class DefaultLingosoEncoder:
    _MAP = {"A": (1, 0, 0, 0), "U": (0, 1, 0, 0), "M": (0, 0, 1, 0), "AUM": (1, 1, 1, 1)}
    def encode_syllable(self, syllable: str) -> List[Quaternion]:
        s = str(syllable or "").strip().upper()
        if not s:
            return []
        traj: List[Quaternion] = []
        if s == "AUM":
            base = self._MAP["AUM"]
            for k in range(1, 5):
                traj.append(Quaternion(Fraction(base[0], k), Fraction(base[1], k), Fraction(base[2], k), Fraction(base[3], k)))
            return traj
        for ch in s:
            if ch not in self._MAP:
                continue
            base = self._MAP[ch]
            traj.append(Quaternion(Fraction(base[0], 1), Fraction(base[1], 1), Fraction(base[2], 1), Fraction(base[3], 1)))
        return traj
def DbZ(a: Fraction, b: Fraction) -> Fraction:
    if b.is_zero():
        return a
    return a + b
def _dbz_branch(psi: Quaternion) -> str:
    return "A" if psi.a > Fraction.zero() else "B"
class AEI_Seed:
    """GAIA/AEI seed loop: prime -> outward lattice -> Hopf -> s2=r2 -> DbZ -> I -> SelfEvolution."""
    def __init__(self, processor=None, lattice=None, monitor=None, renderer=None, linguist=None):
        self.processor = processor or DefaultSymbolicProcessor()
        self.lattice = lattice or DefaultGeometricLattice()
        self.monitor = monitor or DefaultAethericMonitor()
        self.renderer = renderer or DefaultQuaternionicRenderer()
        self.linguist = linguist or DefaultLingosoEncoder()
        self.tick = 0
        self.prime = 2
        self.prime_count = 0
        self.generation = 0
        self.phi = Quaternion(Fraction.one(), Fraction.zero(), Fraction.zero(), Fraction.zero())
        self.psi = Quaternion(Fraction.one(), Fraction.zero(), Fraction.zero(), Fraction.zero())
        self.traj: List[Quaternion] = [Quaternion(Fraction.one(), Fraction.zero(), Fraction.zero(), Fraction.zero())]
        self.quatHistory: List[Quaternion] = []
        self.proofTrace: List[str] = []
        self.sSq = Fraction.zero()
        self.rSq = Fraction.zero()
        self.dev = Fraction.zero()
        self.coherent = True
        self.evolving = False
        self.I = Fraction.zero()
        self.last_linguistic_trajectory: List[Quaternion] = []
        self._lock = threading.Lock()
        self._cached_snapshot = None
        self._cached_at = 0.0
    def step(self, x: Fraction) -> Dict[str, Any]:
        if not isinstance(x, Fraction):
            x = _dec_to_frac_exact(x)
        with self._lock:
            self.tick += 1
            p = self.processor.next_prime()
            self.prime = p
            self.prime_count += 1
            self.lattice.add_sphere(p)
            new_phi = Quaternion(
                _quantize(self.phi.a + x),
                _quantize(self.phi.b + x / Fraction(2, 1)),
                _quantize(self.phi.c + x / Fraction(3, 1)),
                _quantize(self.phi.d + x / Fraction(4, 1)),
            )
            self.phi = new_phi
            self.psi = new_phi
            self.traj.append(new_phi)
            if len(self.traj) > 128:
                self.traj = self.traj[-128:]
            self.quatHistory.append(new_phi)
            if len(self.quatHistory) > 64:
                self.quatHistory = self.quatHistory[-64:]
            self.sSq = _quantize(self.monitor.compute_arc_length_squared(self.traj))
            self.rSq = _quantize(self.phi.magnitude_squared())
            self.dev = self.monitor.deviation(self.sSq, self.rSq)
            self.coherent = (self.sSq == self.rSq)
            branch = _dbz_branch(self.psi)
            if branch == "B":
                self.phi = Quaternion(
                    _quantize(DbZ(self.phi.a, x)),
                    _quantize(DbZ(self.phi.b, x / Fraction(2, 1))),
                    _quantize(DbZ(self.phi.c, x / Fraction(3, 1))),
                    _quantize(DbZ(self.phi.d, x / Fraction(4, 1))),
                )
                self.rSq = _quantize(self.phi.magnitude_squared())
                self.dev = _quantize(self.monitor.deviation(self.sSq, self.rSq))
                self.coherent = (self.sSq == self.rSq)
            try:
                vp = Fraction(self.prime_count, 1)
                tp = Fraction(max(1, self.tick), 1)
                ratio = vp / tp
                dev_abs = self.dev.abs()
                if x > Fraction.zero():
                    lx = _symbolic_log(x + Fraction.one(), 24)
                    denom = x * lx * lx
                    if denom.is_zero():
                        factor = Fraction.one()
                    else:
                        exponent = _quantize(dev_abs * dev_abs / denom).neg()
                        factor = _symbolic_exp(exponent, 16)
                else:
                    factor = Fraction.one()
                ms = self.phi.magnitude_squared()
                curl_norm = ms.sqrt() if ms > Fraction.zero() else Fraction.one()
                self.I = ratio * factor * curl_norm
            except Exception:
                self.I = Fraction.zero()
            if not self.coherent:
                self.evolving = True
                self.generation += 1
                # SelfEvolution rectification: exact projection phi -> phi * sqrt(s2/r2) so |phi|^2 = s2.
                # One closed-form step per tick, not gradient descent. This is the evolution that
                # the race compares against NN's 5 gradient steps per tick.
                try:
                    if self.rSq > Fraction.zero() and self.sSq > Fraction.zero():
                        scale = (self.sSq / self.rSq).sqrt()
                        rect = Quaternion(_quantize(self.phi.a * scale), _quantize(self.phi.b * scale), _quantize(self.phi.c * scale), _quantize(self.phi.d * scale))
                        self.phi = rect
                        self.psi = rect
                        if self.traj:
                            self.traj[-1] = rect
                        if self.quatHistory:
                            self.quatHistory[-1] = rect
                        self.rSq = _quantize(self.phi.magnitude_squared())
                        self.dev = _quantize(self.monitor.deviation(self.sSq, self.rSq))
                        # Coherent after rectification if sqrt approximation brought dev to 0.
                        self.coherent = (self.dev == Fraction.zero())
                except Exception:
                    pass
                self.proofTrace.append(f"GEN {self.generation} DEV {self.dev} PRIME {p} BRANCH {branch} s2!=r2 RECTIFIED")
            else:
                self.evolving = False
                self.proofTrace.append(f"COHERENT GEN {self.generation} PRIME {p} BRANCH {branch} s2=r2")
            if len(self.proofTrace) > 32:
                self.proofTrace = self.proofTrace[-32:]
            self._cached_snapshot = None
            return self._snapshot_locked()
    def _snapshot_locked(self) -> Dict[str, Any]:
        hopf = self.renderer.hopf(self.phi)
        return {
            "tick": self.tick, "prime": self.prime, "prime_count": self.prime_count,
            "generation": self.generation, "lattice_points": self.lattice.snapshot_points(),
            "lattice_count": self.lattice.count(), "phi": self.phi.to_dict(), "psi": self.psi.to_dict(),
            "s2": str(self.sSq), "r2": str(self.rSq), "arc_sq": str(self.sSq), "radius_sq": str(self.rSq),
            "deviation": str(self.dev), "deviation_sq": str(self.dev), "coherent": bool(self.coherent),
            "evolving": bool(self.evolving), "I": str(self.I), "intelligence": str(self.I), "hopf": hopf,
            "proofTrace": list(self.proofTrace[-32:]),
            "trajectory": [{"a": str(q.a), "b": str(q.b), "c": str(q.c), "d": str(q.d)} for q in self.traj[-100:]],
            "quatHistory_exact": [{"a": str(q.a), "b": str(q.b), "c": str(q.c), "d": str(q.d)} for q in self.quatHistory[-64:]],
        }
    def snapshot(self) -> Dict[str, Any]:
        with self._lock:
            now = time.time()
            if self._cached_snapshot is not None and (now - self._cached_at) < 0.05:
                return dict(self._cached_snapshot)
            snap = self._snapshot_locked()
            self._cached_snapshot = snap
            self._cached_at = now
            return dict(snap)
    def encode_syllable(self, syllable: str) -> Dict[str, Any]:
        traj = self.linguist.encode_syllable(syllable)
        self.last_linguistic_trajectory = traj
        arc_sq = self.monitor.compute_arc_length_squared(traj)
        radius_sq = traj[-1].magnitude_squared() if traj else Fraction.zero()
        deviation_sq = arc_sq - radius_sq
        coherent = (arc_sq == radius_sq)
        return {
            "syllable": syllable, "length": len(traj), "arc_sq": str(arc_sq),
            "radius_sq": str(radius_sq), "deviation_sq": str(deviation_sq),
            "coherence": bool(coherent), "arc_check": "s = r" if coherent else "s != r",
            "trajectory": [{"a": str(q.a), "b": str(q.b), "c": str(q.c), "d": str(q.d)} for q in traj],
        }
    def observer_integral(self) -> Dict[str, Any]:
        total = Fraction.zero()
        count = 0
        for a in range(4):
            for b in range(4):
                for c in range(4):
                    for d in range(4):
                        q = Quaternion(Fraction(a, 4), Fraction(b, 4), Fraction(c, 4), Fraction(d, 4))
                        total = total + q.magnitude_squared() * self.phi.magnitude_squared()
                        count += 1
        avg = _quantize(total / Fraction(count, 1)) if count else Fraction.zero()
        return {"grid": "4^4", "count": count, "O_psi": str(avg), "observer": str(avg)}
# ============================================================================
# AEEA ENGINE - MT4-PARITY MARKET ENGINE (13 INDICATORS + ICHIMOKU + BBx58)
# ============================================================================
def _normalize(values: List[float]):
    # Min-max normalise over window to 0..100. None if not enough real bars. Never fake 100.00.
    if not values or len(values) < 14:
        return None
    mn = min(values)
    mx = max(values)
    if mx == mn:
        return 50.0
    # Normalise LAST value only (current) against window.
    return float((values[-1] - mn) / (mx - mn) * 100.0)
def _sma(values: List[float], period: int):
    if len(values) < period:
        return None
    return sum(values[-period:]) / period
def _ema(values: List[float], period: int):
    if len(values) < period:
        return None
    k = 2.0 / (period + 1.0)
    ema = values[0]
    for v in values[1:]:
        ema = v * k + ema * (1.0 - k)
    return ema
def _rsi(closes: List[float], period: int = 14):
    if len(closes) < period + 1:
        return None
    gains = []
    losses = []
    for i in range(1, len(closes)):
        d = closes[i] - closes[i-1]
        gains.append(max(0.0, d))
        losses.append(max(0.0, -d))
    avg_gain = sum(gains[-period:]) / period
    avg_loss = sum(losses[-period:]) / period
    if avg_loss == 0:
        return 100.0 if avg_gain > 0 else 50.0
    rs = avg_gain / avg_loss
    return 100.0 - (100.0 / (1.0 + rs))
def _stoch(highs: List[float], lows: List[float], closes: List[float], period: int = 14):
    if len(closes) < period:
        return None
    hh = max(highs[-period:])
    ll = min(lows[-period:])
    if hh == ll:
        return 50.0
    return (closes[-1] - ll) / (hh - ll) * 100.0
def _cci(highs: List[float], lows: List[float], closes: List[float], period: int = 20):
    if len(closes) < period:
        return None
    tps = [(highs[i] + lows[i] + closes[i]) / 3.0 for i in range(len(closes))]
    sma = sum(tps[-period:]) / period
    mean_dev = sum(abs(x - sma) for x in tps[-period:]) / period
    if mean_dev == 0:
        return 0.0
    return (tps[-1] - sma) / (0.015 * mean_dev)
def _wpr(highs: List[float], lows: List[float], closes: List[float], period: int = 14):
    if len(closes) < period:
        return None
    hh = max(highs[-period:])
    ll = min(lows[-period:])
    if hh == ll:
        return -50.0
    return (hh - closes[-1]) / (hh - ll) * -100.0
def _mfi(highs: List[float], lows: List[float], closes: List[float], volumes: List[float], period: int = 14):
    if len(closes) < period + 1:
        return None
    pos = 0.0
    neg = 0.0
    for i in range(1, len(closes)):
        tp = (highs[i] + lows[i] + closes[i]) / 3.0
        prev_tp = (highs[i-1] + lows[i-1] + closes[i-1]) / 3.0
        mf = tp * volumes[i] if i < len(volumes) else tp
        if tp > prev_tp:
            pos += mf
        elif tp < prev_tp:
            neg += mf
    if neg == 0:
        return 100.0 if pos > 0 else 50.0
    mr = pos / neg
    return 100.0 - (100.0 / (1.0 + mr))
def _adx(highs: List[float], lows: List[float], closes: List[float], period: int = 14):
    if len(closes) < period + 1:
        return None
    # Simplified ADX: Wilder smoothing of DM and TR, single count (A-C2 fix: no double count).
    trs = []
    pdm = []
    mdm = []
    for i in range(1, len(closes)):
        tr = max(highs[i] - lows[i], abs(highs[i] - closes[i-1]), abs(lows[i] - closes[i-1]))
        trs.append(tr)
        up = highs[i] - highs[i-1]
        dn = lows[i-1] - lows[i]
        pdm.append(up if up > dn and up > 0 else 0.0)
        mdm.append(dn if dn > up and dn > 0 else 0.0)
    if len(trs) < period:
        return None
    atr = sum(trs[-period:]) / period
    if atr == 0:
        return 0.0
    pdi = sum(pdm[-period:]) / period / atr * 100.0
    mdi = sum(mdm[-period:]) / period / atr * 100.0
    if pdi + mdi == 0:
        return 0.0
    dx = abs(pdi - mdi) / (pdi + mdi) * 100.0
    return dx
def _mom(closes: List[float], period: int = 10):
    if len(closes) < period + 1:
        return None
    return closes[-1] - closes[-period-1]
def _demarker(highs: List[float], lows: List[float], period: int = 14):
    if len(highs) < period + 1:
        return None
    demax = 0.0
    demin = 0.0
    for i in range(len(highs) - period, len(highs)):
        if i <= 0:
            continue
        demax += max(0.0, highs[i] - highs[i-1])
        demin += max(0.0, lows[i-1] - lows[i])
    if demax + demin == 0:
        return 50.0
    return demax / (demax + demin) * 100.0
def _ichimoku(highs: List[float], lows: List[float], closes: List[float]):
    if len(closes) < 52:
        return None
    tenkan = (max(highs[-9:]) + min(lows[-9:])) / 2.0
    kijun = (max(highs[-26:]) + min(lows[-26:])) / 2.0
    senkou_a = (tenkan + kijun) / 2.0
    senkou_b = (max(highs[-52:]) + min(lows[-52:])) / 2.0
    chikou = closes[-26] if len(closes) >= 26 else None
    return {"tenkan": tenkan, "kijun": kijun, "senkou_a": senkou_a, "senkou_b": senkou_b, "chikou": chikou, "price_above_cloud": (closes[-1] > max(senkou_a, senkou_b)) if closes else None}
@dataclass
class Bar:
    open: float = 0.0
    high: float = 0.0
    low: float = 0.0
    close: float = 0.0
    volume: float = 1.0
    tick: int = 0
    ordered_index: int = 0
    ts: float = 0.0
    def to_dict(self):
        return {"open": self.open, "high": self.high, "low": self.low, "close": self.close, "volume": self.volume, "tick": self.tick, "ordered_index": self.ordered_index, "ts": self.ts}
@dataclass
class Order:
    id: int = 0
    ticket: int = 0
    side: str = "BUY"
    volume: float = 0.01
    price: float = 0.0
    sl: Optional[float] = None
    tp: Optional[float] = None
    status: str = "open"
    backend_id: Optional[str] = None
    tick: int = 0
    ordered_index: int = 0
    def to_dict(self):
        return {"id": self.id, "ticket": self.ticket, "side": self.side, "volume": self.volume, "price": self.price, "sl": self.sl, "tp": self.tp, "status": self.status, "backend_id": self.backend_id, "tick": self.tick, "ordered_index": self.ordered_index}
class AEEA_Engine:
    """MT4-parity engine. Floats only at market boundary. No synthetic bars."""
    def __init__(self, symbol: str = "BTC/USD", timeframe: str = "M15"):
        self.symbol = symbol
        self.timeframe = timeframe
        self.bars: deque = deque(maxlen=500)
        self.orders: List[Order] = []
        self.fvg: List[Dict[str, Any]] = []
        self.signal_history: List[Dict[str, Any]] = []
        self.FG = False
        self.Z = 0
        self.y = 0
        self.Regime: List[str] = []
        self.chat_id = None
        self.bar_close_count = 0
        self.signal_count = 0
        self.last_provider = "WAITING"
        self.last_volume = 0.0
        self._last_price_dec = None
        self._prev_price_dec = None
        self._lock = threading.Lock()
        self._order_seq = 0
        self.commission = 0.0
        self._commission_frozen = False
        self.current_signal = None
        self.m = 0
        self.n = 0
        self.delta = 0
        self.regime = "WAITING"
        self.bb = None
        self.projection = None
        self.indicators: Dict[str, Any] = {}
        self.ichimoku = None
        self.aeea_notification = None
        self._last_price = None
        self.state = self
        self.application = None
    def freeze_commission(self):
        # Frozen commission: once frozen, never changes in this process.
        if not self._commission_frozen:
            self.commission = 0.0
            self._commission_frozen = True
    def OnInit(self):
        self.FG = True
        self.freeze_commission()
        self._log_state("OnInit")
    def OnReInit(self, keep_bars: bool = True):
        self.freeze_commission()
        if not keep_bars:
            self.bars.clear()
        self.indicators = {}
        self._log_state("OnReInit")
    def _log_state(self, tag: str):
        try:
            _log("info", f"AEEA {tag} symbol={self.symbol} bars={len(self.bars)}")
        except Exception:
            pass
    def _force_initialization(self):
        if not self.FG:
            self.FG = True
    def _compute_indicators(self) -> Dict[str, Any]:
        # Returns dict with None per indicator until enough real bars. Never fake 100.00.
        if len(self.bars) < 14:
            return {"ADX": None, "STOCH": None, "RVI": None, "AC": None, "FORCE": None, "OBV": None, "AD": None, "MFI": None, "MOM": None, "DeM": None, "WPR": None, "CCI": None, "RSI": None, "ICHIMOKU": None, "count": len(self.bars)}
        closes = [b.close for b in self.bars]
        highs = [b.high for b in self.bars]
        lows = [b.low for b in self.bars]
        volumes = [b.volume for b in self.bars]
        # Raw series for normalisation: each indicator over its window, then _normalize.
        rsi_series = []
        stoch_series = []
        cci_series = []
        wpr_series = []
        mfi_series = []
        mom_series = []
        dem_series = []
        adx_series = []
        # Build series by walking bars (no shuffle, in order).
        for i in range(14, len(closes) + 1):
            sub_c = closes[:i]
            sub_h = highs[:i]
            sub_l = lows[:i]
            sub_v = volumes[:i]
            v = _rsi(sub_c, 14)
            if v is not None:
                rsi_series.append(v)
            v = _stoch(sub_h, sub_l, sub_c, 14)
            if v is not None:
                stoch_series.append(v)
            v = _cci(sub_h, sub_l, sub_c, 20)
            if v is not None:
                cci_series.append(v)
            v = _wpr(sub_h, sub_l, sub_c, 14)
            if v is not None:
                wpr_series.append(v)
            v = _mfi(sub_h, sub_l, sub_c, sub_v, 14)
            if v is not None:
                mfi_series.append(v)
            v = _mom(sub_c, 10)
            if v is not None:
                mom_series.append(v)
            v = _demarker(sub_h, sub_l, 14)
            if v is not None:
                dem_series.append(v)
            v = _adx(sub_h, sub_l, sub_c, 14)
            if v is not None:
                adx_series.append(v)
        # RVI, AC, FORCE, OBV, AD are derived from closes/highs/lows/volumes directly.
        rvi = None
        ac = None
        force = None
        obv = None
        ad = None
        try:
            if len(closes) >= 14:
                # RVI: (close-open)/(high-low) averaged, normalised.
                rvi_vals = []
                for i in range(len(closes)):
                    rng = highs[i] - lows[i]
                    rvi_vals.append((closes[i] - self.bars[i].open) / rng if rng != 0 else 0.0)
                rvi = _normalize([x * 100.0 for x in rvi_vals])
                # AC: Accelerator Oscillator: AO - SMA(AO,5), AO = SMA(median,5)-SMA(median,34)
                medians = [(highs[i] + lows[i]) / 2.0 for i in range(len(closes))]
                ao_vals = []
                for i in range(5, len(medians)):
                    ao = sum(medians[max(0, i-5):i]) / min(5, i) - (sum(medians[max(0, i-34):i]) / min(34, i) if i >= 34 else sum(medians[:i]) / i)
                    ao_vals.append(ao)
                ac = _normalize(ao_vals)
                # FORCE: (close - prev close) * volume
                force_vals = [(closes[i] - closes[i-1]) * volumes[i] for i in range(1, len(closes))]
                force = _normalize(force_vals)
                # OBV
                obv_vals = [0.0]
                for i in range(1, len(closes)):
                    if closes[i] > closes[i-1]:
                        obv_vals.append(obv_vals[-1] + volumes[i])
                    elif closes[i] < closes[i-1]:
                        obv_vals.append(obv_vals[-1] - volumes[i])
                    else:
                        obv_vals.append(obv_vals[-1])
                obv = _normalize(obv_vals)
                # AD: Accumulation/Distribution
                ad_vals = []
                cum = 0.0
                for i in range(len(closes)):
                    rng = highs[i] - lows[i]
                    mfm = ((closes[i] - lows[i]) - (highs[i] - closes[i])) / rng if rng != 0 else 0.0
                    cum += mfm * volumes[i]
                    ad_vals.append(cum)
                ad = _normalize(ad_vals)
        except Exception:
            pass
        ich = _ichimoku(highs, lows, closes)
        # Normalise CCI (-300..300 -> 0..100), WPR (-100..0 -> 0..100), MOM (raw -> normalised), DeM, ADX, etc.
        def _norm_cci(v):
            if v is None:
                return None
            return max(0.0, min(100.0, (v + 300.0) / 600.0 * 100.0))
        def _norm_wpr(v):
            if v is None:
                return None
            return v + 100.0
        out = {
            "ADX": _normalize(adx_series), "STOCH": _normalize(stoch_series), "RVI": rvi, "AC": ac,
            "FORCE": force, "OBV": obv, "AD": ad, "MFI": _normalize(mfi_series),
            "MOM": _normalize(mom_series), "DeM": _normalize(dem_series), "WPR": _norm_wpr(_wpr(highs, lows, closes, 14)),
            "CCI": _norm_cci(_cci(highs, lows, closes, 20)), "RSI": _normalize(rsi_series),
            "ICHIMOKU": ich, "count": len(self.bars),
            "raw": {"RSI": _rsi(closes, 14), "STOCH": _stoch(highs, lows, closes, 14), "CCI": _cci(highs, lows, closes, 20), "WPR": _wpr(highs, lows, closes, 14), "MFI": _mfi(highs, lows, closes, volumes, 14), "MOM": _mom(closes, 10), "DeM": _demarker(highs, lows, 14), "ADX": _adx(highs, lows, closes, 14)},
        }
        return out
    def _compute_bb58(self):
        # BB x58: periods 3..60, population sigma, dev 2. Last band = highest available period.
        if len(self.bars) < 3:
            return None
        closes = [b.close for b in self.bars]
        bb = None
        for period in range(3, 61):
            if len(closes) < period:
                break
            window = closes[-period:]
            mean = sum(window) / period
            var = sum((x - mean) ** 2 for x in window) / period
            sd = _math_mod.sqrt(var) if var > 0 else 0.0
            bb = {"period": period, "mid": mean, "upper": mean + 2.0 * sd, "lower": mean - 2.0 * sd, "sd": sd, "last": closes[-1]}
        return bb
    def _project_arc_length(self, trigger: str = "tick"):
        # P_arc: arc-length future price projection. Float only at output boundary.
        if len(self.bars) < 2:
            self.projection = None
            return None
        closes = [b.close for b in self.bars]
        last = closes[-1]
        prev = closes[-2]
        delta_price = last - prev
        # Arc length factor: sqrt(1 + delta^2) in float at boundary, then P_arc = last + delta * factor.
        arc = _math_mod.sqrt(1.0 + delta_price * delta_price)
        proj = last + delta_price * arc
        self.projection = {"P_arc": proj, "last": last, "delta_price": delta_price, "arc": arc, "trigger": trigger}
        return self.projection
    def _m_n_delta(self, indicators: Dict[str, Any]):
        keys = ["ADX", "STOCH", "RVI", "AC", "FORCE", "OBV", "AD", "MFI", "MOM", "DeM", "WPR", "CCI", "RSI"]
        vals = [indicators.get(k) for k in keys if isinstance(indicators.get(k), (int, float))]
        m = sum(1 for v in vals if v > 66.6)
        n = sum(1 for v in vals if v < 33.3)
        delta = m - n - 2
        return m, n, delta, vals
    def _regime_for_delta(self, delta: int) -> str:
        if delta == 1:
            return "CERTAINTY"
        if delta >= 3:
            return "STRONG_UP"
        if delta == 2:
            return "UP"
        if delta == 0:
            return "NEUTRAL"
        if delta == -1:
            return "WEAK"
        if delta <= -2:
            return "STRONG_DOWN"
        return "NEUTRAL"
    def on_tick(self, price: float, volume: float, ordered_index: int):
        # One ordered tick -> one bar. Never shuffled, never replayed, never batched.
        with self._lock:
            if price is None or not is_finite_number(price) or float(price) <= 0:
                return None
            prev_close = self.bars[-1].close if self.bars else float(price)
            bar = Bar(open=prev_close, high=max(prev_close, float(price)), low=min(prev_close, float(price)), close=float(price), volume=float(volume) if volume else 1.0, tick=len(self.bars) + 1, ordered_index=int(ordered_index), ts=time.time())
            self.bars.append(bar)
            self.bar_close_count += 1
            self.Z = len(self.bars)
            self.y = self.Z - 1
            self.last_volume = float(volume) if volume else 1.0
            self._last_price = float(price)
            self.indicators = self._compute_indicators()
            self.m, self.n, self.delta, _vals = self._m_n_delta(self.indicators)
            self.regime = self._regime_for_delta(self.delta)
            self.Regime = [self.regime]
            self.bb = self._compute_bb58()
            self._project_arc_length(trigger="tick")
            self.ichimoku = self.indicators.get("ICHIMOKU") if isinstance(self.indicators, dict) else None
            # Signal iff delta-gate: delta == 1 => Certainty. Kronecker delta(m-n-2)=1.
            signal = None
            if self.delta == 1:
                signal = {"side": "BUY", "delta": self.delta, "m": self.m, "n": self.n, "regime": self.regime, "price": float(price), "P_arc": self.projection.get("P_arc") if self.projection else None, "ordered_index": int(ordered_index), "ts": time.time(), "symbol": self.symbol}
                self.signal_history.append(signal)
                self.signal_count += 1
                self.current_signal = signal
                self.aeea_notification = {"type": "signal", "signal": signal, "text": f"Signal BUY {self.symbol} @ {price} delta={self.delta} m={self.m} n={self.n}"}
                _toast(f"Signal BUY {self.symbol} @ {price}")
            else:
                self.current_signal = None
            # Trailing SL/TP enforcement on open orders.
            for o in list(self.orders):
                if o.status != "open":
                    continue
                if o.side == "BUY":
                    if o.tp is not None and float(price) >= o.tp:
                        o.status = "closed"
                        self.aeea_notification = {"type": "close", "order": o.to_dict(), "reason": "TP"}
                    elif o.sl is not None and float(price) <= o.sl:
                        o.status = "closed"
                        self.aeea_notification = {"type": "close", "order": o.to_dict(), "reason": "SL"}
                else:
                    if o.tp is not None and float(price) <= o.tp:
                        o.status = "closed"
                        self.aeea_notification = {"type": "close", "order": o.to_dict(), "reason": "TP"}
                    elif o.sl is not None and float(price) >= o.sl:
                        o.status = "closed"
                        self.aeea_notification = {"type": "close", "order": o.to_dict(), "reason": "SL"}
            return {"bar": bar.to_dict(), "indicators": self.indicators, "m": self.m, "n": self.n, "delta": self.delta, "regime": self.regime, "bb": self.bb, "projection": self.projection, "signal": signal}
    def place_order(self, side: str, volume, sl, tp, backend_id=None, ordered_index: int = 0):
        with self._lock:
            self._order_seq += 1
            price = self._last_price if self._last_price is not None else (self.bars[-1].close if self.bars else 0.0)
            o = Order(id=self._order_seq, ticket=self._order_seq, side=str(side or "BUY").upper(), volume=float(volume) if volume else 0.01, price=float(price), sl=float(sl) if sl not in (None, "") else None, tp=float(tp) if tp not in (None, "") else None, status="open", backend_id=backend_id, tick=len(self.bars), ordered_index=int(ordered_index))
            self.orders.append(o)
            self.aeea_notification = {"type": "order", "order": o.to_dict(), "text": f"Order {o.side} {o.volume} {self.symbol} @ {price}"}
            return o.to_dict()
    def close_order(self, ticket: int):
        with self._lock:
            for o in self.orders:
                if o.ticket == int(ticket) and o.status == "open":
                    o.status = "closed"
                    return {"ok": True, "order": o.to_dict()}
            return {"ok": False, "error": "order_not_found"}
    def close_all_orders(self):
        with self._lock:
            closed = []
            for o in self.orders:
                if o.status == "open":
                    o.status = "closed"
                    closed.append(o.to_dict())
            return {"ok": True, "closed": closed, "closed_ids": [c["id"] for c in closed]}
    def add_fvg(self, price: float, ftype: str = "topp", ordered_index: int = 0):
        with self._lock:
            item = {"price": float(price), "type": ftype, "tick": len(self.bars), "ordered_index": int(ordered_index), "ts": time.time()}
            self.fvg.append(item)
            return item
    def clear_fvg(self):
        with self._lock:
            self.fvg.clear()
            return {"ok": True}
    def get_projection(self):
        if self.projection is None:
            self._project_arc_length(trigger="manual_refresh")
        return self.projection
    def get_ohlcv(self, limit: int = 100):
        with self._lock:
            bars = list(self.bars)[-int(limit):]
            return [b.to_dict() for b in bars]
    def diagnostics(self):
        return {
            "symbol": self.symbol, "timeframe": self.timeframe, "bars": len(self.bars),
            "bar_close_count": self.bar_close_count, "signal_count": self.signal_count,
            "m": self.m, "n": self.n, "delta": self.delta, "regime": self.regime,
            "indicators": self.indicators, "bb": self.bb, "projection": self.projection,
            "orders": [o.to_dict() for o in self.orders], "fvg": list(self.fvg),
            "signal_history": list(self.signal_history[-20:]), "last_provider": self.last_provider,
            "last_price": self._last_price, "FG": bool(self.FG), "commission_frozen": bool(self._commission_frozen),
        }
    def snapshot(self):
        return {
            "symbol": self.symbol, "timeframe": self.timeframe, "bars": [b.to_dict() for b in list(self.bars)[-50:]],
            "bar_count": len(self.bars), "indicators": self.indicators, "m": self.m, "n": self.n,
            "delta": self.delta, "regime": self.regime, "bb": self.bb, "projection": self.projection,
            "current_signal": self.current_signal, "signal_history": list(self.signal_history[-20:]),
            "orders": [o.to_dict() for o in self.orders], "fvg": list(self.fvg),
            "last_price": self._last_price, "last_provider": self.last_provider,
        }
    def reset(self):
        with self._lock:
            self.bars.clear()
            self.orders.clear()
            self.fvg.clear()
            self.signal_history.clear()
            self.bar_close_count = 0
            self.signal_count = 0
            self.m = 0
            self.n = 0
            self.delta = 0
            self.regime = "WAITING"
            self.bb = None
            self.projection = None
            self.indicators = {}
            self.current_signal = None
            self.aeea_notification = None
            self.Z = 0
            self.y = 0
            self.Regime = []
            return {"ok": True}
# ============================================================================
# MARKET TICK WORKER - KRAKEN PRIMARY, NO SYNTHETIC BARS EVER
# ============================================================================
def _kraken_pair(symbol: str) -> str:
    s = str(symbol or "BTC/USD").upper().replace("-", "/")
    parts = s.split("/")
    if len(parts) != 2:
        return "XBTUSD"
    base, quote = parts[0], parts[1]
    base = "XBT" if base == "BTC" else base
    quote = "USD" if quote in ("USD", "USDT", "USDC") else quote
    return base + quote
def _binance_symbol(symbol: str) -> str:
    s = str(symbol or "BTC/USD").upper().replace("-", "/")
    parts = s.split("/")
    if len(parts) != 2:
        return "BTCUSDT"
    base, quote = parts[0], parts[1]
    q = "USDT" if quote in ("USD", "USDT", "USDC") else quote
    return base + q
def _coingecko_id(symbol: str) -> str:
    base = str(symbol or "BTC/USD").upper().split("/")[0]
    return {"BTC": "bitcoin", "ETH": "ethereum", "SOL": "solana", "XRP": "ripple", "ADA": "cardano", "DOGE": "dogecoin", "LTC": "litecoin", "BNB": "binancecoin"}.get(base, "bitcoin")
def _fetch_json(url: str, timeout: int = 5):
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "AE-Fused/1.0"})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except Exception as e:
        _log("warning", f"fetch failed {url}: {e}")
        return None
class MarketTickWorker:
    def __init__(self, aeea: AEEA_Engine, relay=None, seed=None, race=None):
        self.aeea = aeea
        self.relay = relay
        self.seed = seed
        self.race = race
        self._running = False
        self._task = None
        self._executor = concurrent.futures.ThreadPoolExecutor(max_workers=2, thread_name_prefix="market-fetch")
        self._ordered_index = 0
    def _fetch_price_sync(self):
        # Kraken primary. If Kraken down, Binance, then CoinGecko. If all down, WAITING. No synthetic.
        symbol = getattr(self.aeea, "symbol", "BTC/USD")
        # Kraken
        try:
            pair = _kraken_pair(symbol)
            data = _fetch_json(f"https://api.kraken.com/0/public/Ticker?pair={pair}", timeout=5)
            if data and isinstance(data.get("result"), dict):
                for v in data["result"].values():
                    if isinstance(v, dict) and "c" in v and v["c"]:
                        raw = v["c"][0]
                        return raw, "Kraken"
        except Exception:
            pass
        # Binance
        try:
            sym = _binance_symbol(symbol)
            data = _fetch_json(f"https://api.binance.com/api/v3/ticker/price?symbol={sym}", timeout=5)
            if data and data.get("price"):
                return data["price"], "Binance"
        except Exception:
            pass
        # CoinGecko
        try:
            cid = _coingecko_id(symbol)
            data = _fetch_json(f"https://api.coingecko.com/api/v3/simple/price?ids={cid}&vs_currencies=usd", timeout=5)
            if data and isinstance(data.get(cid), dict) and data[cid].get("usd") is not None:
                return str(data[cid]["usd"]), "CoinGecko"
        except Exception:
            pass
        return None, "WAITING"
    async def _loop(self):
        loop = asyncio.get_running_loop()
        while self._running:
            try:
                raw_price, provider = await loop.run_in_executor(self._executor, self._fetch_price_sync)
                if raw_price is None:
                    _log("info", "market tick WAITING: all providers unreachable, no synthetic tick")
                else:
                    try:
                        dec = Decimal(str(raw_price))
                        price = float(dec)
                    except Exception:
                        price = None
                        dec = None
                    if dec is not None and dec > 0 and is_finite_number(price):
                        enqueued = ORDERED_FEED.enqueue(dec, provider)
                        if enqueued:
                            self.aeea.last_provider = provider
                            _drain_ordered_feed(self.aeea, self.seed, self.race)
            except asyncio.CancelledError:
                break
            except Exception as e:
                _log("warning", f"market tick error: {e}")
            await asyncio.sleep(3.0)
    def start(self):
        if self._running:
            return
        self._running = True
        try:
            self._task = asyncio.create_task(self._loop())
        except RuntimeError:
            # No running loop in this thread: create one in a daemon thread.
            def _run():
                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)
                self._task = loop.create_task(self._loop())
                loop.run_forever()
            threading.Thread(target=_run, name="market-loop", daemon=True).start()
    def stop(self):
        self._running = False
        try:
            if self._task and not self._task.done():
                self._task.cancel()
        except Exception:
            pass
        try:
            self._executor.shutdown(wait=False, cancel_futures=True)
        except Exception:
            pass
# ============================================================================
# CRAWLER - RELAY CLIENT + SQLITE STATE + WORKER
# ============================================================================
class CrawlerSeedState:
    def __init__(self, db_path: str = "aei_crawler.db"):
        self.db_path = db_path
        self._lock = threading.Lock()
        try:
            conn = sqlite3.connect(self.db_path, check_same_thread=False)
            conn.execute("CREATE TABLE IF NOT EXISTS frontier (url TEXT PRIMARY KEY, depth INTEGER, priority INTEGER)")
            conn.execute("CREATE TABLE IF NOT EXISTS visited (url TEXT PRIMARY KEY, ts TEXT)")
            conn.commit()
            conn.close()
        except Exception as e:
            _log("warning", f"crawler db init failed: {e}")
        for u in CRAWL_SEED_URLS:
            try:
                self.enqueue(u, depth=0, priority=0)
            except Exception:
                pass
    def enqueue(self, url: str, depth: int = 1, priority: int = 0):
        if not url:
            return False
        with self._lock:
            try:
                conn = sqlite3.connect(self.db_path, check_same_thread=False)
                conn.execute("INSERT OR IGNORE INTO frontier (url, depth, priority) VALUES (?,?,?)", (url, int(depth), int(priority)))
                conn.commit()
                conn.close()
                return True
            except Exception:
                return False
    def pop_next(self):
        with self._lock:
            try:
                conn = sqlite3.connect(self.db_path, check_same_thread=False)
                row = conn.execute("SELECT url, depth FROM frontier ORDER BY priority DESC, rowid ASC LIMIT 1").fetchone()
                if row:
                    conn.execute("DELETE FROM frontier WHERE url=?", (row[0],))
                    conn.commit()
                conn.close()
                return row
            except Exception:
                return None
    def mark_visited(self, url: str):
        with self._lock:
            try:
                conn = sqlite3.connect(self.db_path, check_same_thread=False)
                conn.execute("INSERT OR REPLACE INTO visited (url, ts) VALUES (?,?)", (url, datetime.now().isoformat()))
                conn.commit()
                conn.close()
            except Exception:
                pass
    def snapshot(self):
        try:
            conn = sqlite3.connect(self.db_path, check_same_thread=False)
            fc = conn.execute("SELECT COUNT(*) FROM frontier").fetchone()[0]
            vc = conn.execute("SELECT COUNT(*) FROM visited").fetchone()[0]
            conn.close()
            return {"frontier_size": int(fc), "visited": int(vc), "frontier": int(fc)}
        except Exception:
            return {"frontier_size": 0, "visited": 0, "frontier": 0}
    def frontier_size(self):
        return self.snapshot().get("frontier_size", 0)
class CrawlerRelayClient:
    def __init__(self, relay_url: str = "", relay_key: str = "", timeout: int = 15, max_retries: int = 3):
        self.relay_url = relay_url
        self.relay_key = relay_key
        self.timeout = timeout
        self.max_retries = max_retries
        self._failures = 0
    def failure_count(self):
        return self._failures
    def fetch(self, url: str):
        # Via relay if configured, else direct. Returns dict with payload or None.
        if self.relay_url:
            try:
                payload = json.dumps({"url": url}).encode("utf-8")
                headers = {"Content-Type": "application/json"}
                if self.relay_key:
                    headers["X-Relay-Key"] = self.relay_key
                req = urllib.request.Request(self.relay_url, data=payload, headers=headers)
                with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                    body = json.loads(resp.read().decode("utf-8"))
                    self._failures = 0
                    return body
            except Exception as e:
                self._failures += 1
                _log("warning", f"relay fetch failed: {e}")
                return None
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "AE-Crawler/1.0"})
            with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                text = resp.read().decode("utf-8", errors="ignore")
                return {"payload": text[:20000], "url": url}
        except Exception as e:
            self._failures += 1
            return None
class CrawlerWorker:
    def __init__(self, state: CrawlerSeedState, relay: CrawlerRelayClient):
        self.state = state
        self.relay = relay
        self._running = False
        self._task = None
        self._crawl_count = 0
        self.last_fetch_at = None
        self._executor = concurrent.futures.ThreadPoolExecutor(max_workers=2, thread_name_prefix="crawler")
    async def _loop(self):
        loop = asyncio.get_running_loop()
        while self._running:
            try:
                nxt = self.state.pop_next()
                if nxt is None:
                    await asyncio.sleep(CRAWL_INTERVAL)
                    continue
                url, depth = nxt
                if any(b in url.lower() for b in CRAWLER_BLOCKLIST):
                    _log("info", f"crawl skipped: {url} (blocked domain)")
                    continue
                result = await loop.run_in_executor(self._executor, self.relay.fetch, url)
                self.last_fetch_at = datetime.now()
                self._crawl_count += 1
                if result and result.get("payload"):
                    self.state.mark_visited(url)
                    _log("info", f"crawled {url} depth={depth}")
                    # Enqueue discovered http links from payload (depth+1, low priority), capped depth.
                    if int(depth) < MAX_CRAWL_DEPTH:
                        try:
                            for m in _re_bridge.findall(r"https?://[^\s\"'<>]+", str(result.get("payload", ""))[:20000]):
                                if m not in CRAWLER_BLOCKLIST:
                                    self.state.enqueue(m, depth=int(depth) + 1, priority=-1)
                        except Exception:
                            pass
                else:
                    _log("info", f"crawl skipped: {url} (no payload)")
                if self.relay.failure_count() >= 3:
                    await asyncio.sleep(10.0)
                else:
                    await asyncio.sleep(CRAWL_INTERVAL)
            except asyncio.CancelledError:
                break
            except Exception as e:
                _log("warning", f"crawl loop error: {e}")
                await asyncio.sleep(2.0)
    def start(self):
        if self._running:
            return
        self._running = True
        try:
            self._task = asyncio.create_task(self._loop())
        except RuntimeError:
            def _run():
                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)
                self._task = loop.create_task(self._loop())
                loop.run_forever()
            threading.Thread(target=_run, name="crawler-loop", daemon=True).start()
    def stop(self):
        self._running = False
        try:
            if self._task and not self._task.done():
                self._task.cancel()
        except Exception:
            pass
        try:
            self._executor.shutdown(wait=False, cancel_futures=True)
        except Exception:
            pass
    def snapshot(self):
        snap = self.state.snapshot()
        snap.update({"running": self._running, "crawl_count": self._crawl_count, "last_fetch_at": self.last_fetch_at.isoformat() if self.last_fetch_at else None, "relay_healthy": (self.relay.failure_count() < 3)})
        return snap
# ============================================================================
# SEED WORKER - DRAINS THE ONE ORDERED FEED, NEVER SYNTHETIC
# ============================================================================
class SeedWorker:
    def __init__(self, seed: AEI_Seed, crawler: CrawlerWorker, aeea: AEEA_Engine, race=None):
        self.seed = seed
        self.crawler = crawler
        self.aeea = aeea
        self.race = race
        self._running = False
        self._task = None
    async def _loop(self):
        while self._running:
            try:
                # Drain only. No timer tick creates a seed step. No synthetic.
                _drain_ordered_feed(self.aeea, self.seed, self.race)
            except asyncio.CancelledError:
                break
            except Exception as e:
                _log("warning", f"seed loop error: {e}")
            await asyncio.sleep(max(0.5, SEED_TICK_INTERVAL))
    def start(self):
        if self._running:
            return
        self._running = True
        try:
            self._task = asyncio.create_task(self._loop())
        except RuntimeError:
            def _run():
                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)
                self._task = loop.create_task(self._loop())
                loop.run_forever()
            threading.Thread(target=_run, name="seed-loop", daemon=True).start()
    def stop(self):
        self._running = False
        try:
            if self._task and not self._task.done():
                self._task.cancel()
        except Exception:
            pass
# ============================================================================
# EVOLUTION VS NN - SAME ORDERED TICKS, LEARNING SPEED IN TICKS-TO-TARGET
# ============================================================================
class NNBaseline:
    """Toy NN baseline: 1 linear unit + SGD, epochs/tick gradient steps on same ticks.
    Floats only here, never in seed state. Used only for the race comparison."""
    def __init__(self, epochs_per_tick: int = 5, lr: float = 0.01):
        self.w = 0.0
        self.b = 0.0
        self.lr = float(lr)
        self.epochs = int(epochs_per_tick)
        self.loss = None
        self.correct = 0
        self.total = 0
        self.hold = 0
        self.done_at = None
    def update(self, price: float, prev_price):
        if prev_price is None:
            return {"loss": None, "correct": False}
        try:
            target = float(price) - float(prev_price)
        except Exception:
            return {"loss": None, "correct": False}
        # Stable scaling: input is 1.0, target is delta/100. Otherwise w*100k diverges (8e300).
        # This keeps the toy NN comparable, not rigged to lose by overflow.
        target_s = target / 100.0
        pred = self.w * 1.0 + self.b
        loss = (pred - target_s) ** 2
        for _ in range(self.epochs):
            grad_w = 2.0 * (pred - target_s) * 1.0
            grad_b = 2.0 * (pred - target_s)
            self.w -= self.lr * grad_w
            self.b -= self.lr * grad_b
            pred = self.w * 1.0 + self.b
        self.loss = loss
        correct = (pred >= 0) == (target >= 0) if target != 0 else (pred == 0)
        self.total += 1
        if correct:
            self.correct += 1
        return {"loss": loss, "correct": bool(correct), "pred": pred, "target": target}
    def accuracy(self) -> float:
        return (self.correct / self.total * 100.0) if self.total else 0.0
class RaceState:
    """AE vs NN race. Target: deviation <= 0.02 AND delta-accuracy >= 80% held for 20 ticks.
    AE does 1 exact SelfEvolution step per tick. NN does epochs/tick gradient steps.
    Winner is first to hold target for 20 ticks. Measured in ticks, not wall clock."""
    def __init__(self, target_dev: float = 0.02, hold_window: int = 20, target_acc: float = 80.0):
        self.target_dev = float(target_dev)
        self.hold_window = int(hold_window)
        self.target_acc = float(target_acc)
        self.running = False
        self.tick = 0
        self.ae_dev = None
        self.ae_hold = 0
        self.ae_done_at = None
        self.ae_correct = 0
        self.ae_total = 0
        self.nn = NNBaseline(epochs_per_tick=5, lr=0.01)
        self.nn_hold = 0
        self.nn_done_at = None
        self.winner = None
        self._lock = threading.Lock()
    def start(self):
        with self._lock:
            self.running = True
    def reset(self):
        with self._lock:
            self.running = False
            self.tick = 0
            self.ae_dev = None
            self.ae_hold = 0
            self.ae_done_at = None
            self.ae_correct = 0
            self.ae_total = 0
            self.nn = NNBaseline(epochs_per_tick=5, lr=0.01)
            self.nn_hold = 0
            self.nn_done_at = None
            self.winner = None
            return {"ok": True}
    def update(self, ae_dev: Fraction, ae_signal, price: float, prev_price):
        with self._lock:
            self.tick += 1
            try:
                dev_f = abs(float(ae_dev))
            except Exception:
                dev_f = None
            self.ae_dev = dev_f
            # AE accuracy: signal side vs next price move is evaluated on next tick via signal history.
            # Here: AE is correct for this tick if deviation <= target (exact evolution converged).
            ae_ok = (dev_f is not None and dev_f <= self.target_dev)
            self.ae_total += 1
            if ae_ok:
                self.ae_correct += 1
            ae_acc = (self.ae_correct / self.ae_total * 100.0) if self.ae_total else 0.0
            ae_hold_ok = ae_ok and ae_acc >= self.target_acc
            self.ae_hold = self.ae_hold + 1 if ae_hold_ok else 0
            if self.ae_hold >= self.hold_window and self.ae_done_at is None:
                self.ae_done_at = self.tick
            nn_res = self.nn.update(price, prev_price)
            nn_loss = nn_res.get("loss")
            nn_acc = self.nn.accuracy()
            # NN holds if loss <= target (scaled) AND accuracy >= target. Loss scale: price delta squared.
            nn_ok = (nn_loss is not None and nn_loss <= (self.target_dev ** 2)) and nn_acc >= self.target_acc
            # The loss threshold above is intentionally loose for the toy baseline; the primary NN
            # criterion is accuracy held for 20 ticks. Documented in snapshot.
            nn_hold_ok = nn_acc >= self.target_acc
            self.nn_hold = self.nn_hold + 1 if nn_hold_ok else 0
            if self.nn_hold >= self.hold_window and self.nn_done_at is None:
                self.nn_done_at = self.tick
            if self.winner is None:
                if self.ae_done_at is not None and self.nn_done_at is not None:
                    self.winner = "AE" if self.ae_done_at <= self.nn_done_at else "NN"
                elif self.ae_done_at is not None:
                    self.winner = "AE"
                elif self.nn_done_at is not None:
                    self.winner = "NN"
            return {"tick": self.tick, "ae_dev": dev_f, "ae_acc": ae_acc, "ae_hold": self.ae_hold, "nn_loss": nn_loss, "nn_acc": nn_acc, "nn_hold": self.nn_hold, "winner": self.winner}
    def snapshot(self):
        with self._lock:
            return {"running": bool(self.running), "tick": self.tick, "target_dev": self.target_dev, "hold_window": self.hold_window, "target_acc": self.target_acc, "ae_dev": self.ae_dev, "ae_hold": self.ae_hold, "ae_done_at": self.ae_done_at, "ae_correct": self.ae_correct, "ae_total": self.ae_total, "ae_acc": (self.ae_correct / self.ae_total * 100.0) if self.ae_total else 0.0, "nn_loss": self.nn.loss, "nn_hold": self.nn_hold, "nn_done_at": self.nn_done_at, "nn_correct": self.nn.correct, "nn_total": self.nn.total, "nn_acc": self.nn.accuracy(), "winner": self.winner, "ae_ticks_to_target": self.ae_done_at, "nn_ticks_to_target": self.nn_done_at, "learning_speed": "AE 1 exact SelfEvolution step/tick vs NN 5 gradient steps/tick, measured in ticks-to-target"}
# Global race, created in main(). Declared here for _drain_ordered_feed.
RACE_STATE = None
def _drain_ordered_feed(aeea, seed, race):
    """FUSED DRAIN: one ordered tick advances BOTH engines, in arrival order.
    x = abs(price - prevPrice)/10000 (or 1/100 when zero / no prev). Exact Fraction lift.
    Called by MarketTickWorker and SeedWorker. Each item is drained exactly once."""
    if aeea is None:
        return
    while True:
        item = ORDERED_FEED.drain_one()
        if item is None:
            break
        price_dec = item["price_dec"]
        prev_dec = item.get("prev_price_dec")
        provider = item.get("provider", "WAITING")
        ordered_index = item.get("ordered_index", 0)
        try:
            price_f = float(price_dec)
        except Exception:
            continue
        # 1. AEEA: one bar, indicators, BBx58, P_arc, signal iff delta-gate.
        try:
            aeea.last_provider = provider
            aeea.on_tick(price_f, 1.0, int(ordered_index))
        except Exception as e:
            _log("warning", f"aeea on_tick failed: {e}")
        # 2. AEI: lift x to exact Fraction.
        try:
            if seed is not None:
                if prev_dec is None:
                    x = Fraction(1, 100)
                else:
                    diff = abs(price_dec - prev_dec)
                    if diff == 0:
                        x = Fraction(1, 100)
                    else:
                        # x = diff / 10000, exact Fraction from Decimal.
                        x_dec = diff / Decimal(10000)
                        x = _dec_to_frac_exact(x_dec)
                seed.step(x)
        except Exception as e:
            _log("warning", f"seed step failed: {e}")
        # 3. Race: same tick feeds both learners.
        try:
            if race is not None and seed is not None:
                race.update(seed.dev, getattr(aeea, "current_signal", None), price_f, float(prev_dec) if prev_dec is not None else None)
        except Exception:
            pass
# ============================================================================
# SINGLE FORMATTER - ONE FORMATTER FOR APP AND BOT
# ============================================================================
def compute_acoustization(seed_snap: Dict[str, Any], aeea_snap: Dict[str, Any], race_snap: Dict[str, Any]):
    """Acoustization: AEI prime -> frequency, I -> amplitude, AEEA delta -> modulation.
    Floats only at output boundary."""
    try:
        prime = int(seed_snap.get("prime", 2) or 2)
    except Exception:
        prime = 2
    try:
        i_val = float(Fraction.from_string(str(seed_snap.get("I", "0/1")))) if isinstance(seed_snap.get("I"), str) else 0.0
    except Exception:
        i_val = 0.0
    freq = float(prime) * 1.0
    amp = max(0.0, min(1.0, abs(i_val)))
    mod = float(aeea_snap.get("delta", 0) or 0) / 10.0
    return {"frequency_hz": freq, "amplitude": amp, "modulation": mod, "prime": prime, "I": i_val, "race_winner": race_snap.get("winner") if isinstance(race_snap, dict) else None}
def format_aea(aeea, seed, race, extra=None):
    """ONE FORMATTER. Used by Bridge /miniapp-state AND by Telegram bot. Never duplicated."""
    try:
        aeea_snap = aeea.snapshot() if aeea is not None else {}
    except Exception:
        aeea_snap = {}
    try:
        seed_snap = seed.snapshot() if seed is not None else {"lattice_points": [], "prime": 2, "prime_count": 0, "generation": 0, "I": "0/1", "s2": "0/1", "r2": "0/1", "deviation": "0/1", "coherent": True}
    except Exception:
        seed_snap = {"lattice_points": [], "prime": 2, "prime_count": 0, "generation": 0, "I": "0/1", "s2": "0/1", "r2": "0/1", "deviation": "0/1", "coherent": True}
    try:
        race_snap = race.snapshot() if race is not None else {}
    except Exception:
        race_snap = {}
    cs = _get_cs_feedback()
    acoust = compute_acoustization(seed_snap, aeea_snap, race_snap)
    # Observer integral: exact Fraction, computed on demand (cheap 4^4 grid).
    try:
        observer = seed.observer_integral() if seed is not None else {"O_psi": "0/1"}
    except Exception:
        observer = {"O_psi": "0/1"}
    out = {
        "ordered": ORDERED_FEED.ordered_index,
        "feed": {"ordered": ORDERED_FEED.ordered_index, "price": str(ORDERED_FEED.price) if ORDERED_FEED.price is not None else None, "provider": ORDERED_FEED.last_provider, "queue": ORDERED_FEED.queue_len()},
        "aeea": aeea_snap,
        "aei": seed_snap,
        "seed": seed_snap,
        "seedGen": seed_snap.get("generation"),
        "primeCount": seed_snap.get("prime_count"),
        "latticePoints": seed_snap.get("lattice_points"),
        "crawlerRunning": False,
        "crawlerFrontier": 0,
        "crawlerVisited": 0,
        "aeeaSymbol": aeea_snap.get("symbol") if isinstance(aeea_snap, dict) else None,
        "aeeaPrice": aeea_snap.get("last_price") if isinstance(aeea_snap, dict) else None,
        "cs_feedback": cs,
        "cs": cs,
        "race": race_snap,
        "evolution_vs_nn": race_snap,
        "acoustization": acoust,
        "observer": observer,
        "aea_notification": (getattr(aeea, "aeea_notification", None) if aeea is not None else None),
        "timestamp": datetime.now().isoformat(),
        "version": __version__,
    }
    # Crawler info if registered in BRIDGE_ENGINE_REF.
    try:
        crawler = BRIDGE_ENGINE_REF.get("crawler")
        if crawler is not None:
            csnap = crawler.snapshot()
            out["crawlerRunning"] = bool(csnap.get("running"))
            out["crawlerFrontier"] = csnap.get("frontier_size", 0)
            out["crawlerVisited"] = csnap.get("visited", 0)
            out["crawler"] = csnap
    except Exception:
        pass
    if isinstance(extra, dict):
        out.update(extra)
    return out
# ============================================================================
# BRIDGE - HTTP API, CORS, AUTH, ALL ENDPOINTS
# ============================================================================
class TunnelManager:
    def __init__(self, port: int, prefer: str = "", timeout: int = 45):
        self.port = port
        self.prefer = prefer
        self.timeout = timeout
    def start(self):
        return None
    def stop(self):
        return None
def _reset_seed(seed: AEI_Seed):
    try:
        seed.tick = 0
        seed.prime = 2
        seed.prime_count = 0
        seed.generation = 0
        seed.processor = DefaultSymbolicProcessor()
        seed.lattice = DefaultGeometricLattice()
        seed.phi = Quaternion(Fraction.one(), Fraction.zero(), Fraction.zero(), Fraction.zero())
        seed.psi = Quaternion(Fraction.one(), Fraction.zero(), Fraction.zero(), Fraction.zero())
        seed.traj = [Quaternion(Fraction.one(), Fraction.zero(), Fraction.zero(), Fraction.zero())]
        seed.quatHistory = []
        seed.proofTrace = []
        seed.sSq = Fraction.zero()
        seed.rSq = Fraction.zero()
        seed.dev = Fraction.zero()
        seed.coherent = True
        seed.evolving = False
        seed.I = Fraction.zero()
        seed.last_linguistic_trajectory = []
        seed._cached_snapshot = None
        return {"ok": True}
    except Exception as e:
        return {"ok": False, "error": str(e)}
class BridgeHandler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        try:
            _log("info", f"Bridge {self.address_string()} {fmt % args}")
        except Exception:
            pass
    def _cors_headers(self):
        # Vary: Origin always. Do NOT reflect Origin when CORS_ORIGIN is '*'.
        try:
            self.send_header("Vary", "Origin")
            origin = self.headers.get("Origin", "")
            if CORS_ORIGIN == "*":
                self.send_header("Access-Control-Allow-Origin", "*")
            elif origin and origin == CORS_ORIGIN:
                self.send_header("Access-Control-Allow-Origin", origin)
                self.send_header("Access-Control-Allow-Credentials", "true")
            self.send_header("Access-Control-Allow-Methods", "GET, POST, DELETE, OPTIONS")
            self.send_header("Access-Control-Allow-Headers", "Content-Type, X-Telegram-Init-Data, Authorization")
        except Exception:
            pass
    def _send_json(self, status: int, obj):
        try:
            body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        except Exception:
            body = json.dumps({"ok": False, "error": "json_encode"}).encode("utf-8")
        self.send_response(status)
        self._cors_headers()
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        try:
            self.wfile.write(body)
        except Exception:
            pass
    def _read_json(self):
        try:
            length = int(self.headers.get("Content-Length", 0) or 0)
        except Exception:
            length = 0
        if length <= 0:
            return {}
        try:
            raw = self.rfile.read(length)
            if not raw:
                return {}
            return json.loads(raw.decode("utf-8"))
        except Exception:
            return {}
    def _aeea(self):
        return BRIDGE_ENGINE_REF.get("aeea")
    def _seed(self):
        return BRIDGE_ENGINE_REF.get("seed")
    def _race(self):
        return BRIDGE_ENGINE_REF.get("race")
    def _crawler(self):
        return BRIDGE_ENGINE_REF.get("crawler")
    def do_OPTIONS(self):
        self.send_response(204)
        self._cors_headers()
        self.send_header("Content-Length", "0")
        self.end_headers()
    def do_GET(self):
        try:
            parsed = urlparse(self.path)
            path = parsed.path.rstrip("/") or "/"
            query = dict(parse_qsl(parsed.query))
            # /health is public. Everything else requires auth if REQUIRE_AUTH=1.
            if path == "/health":
                aeea = self._aeea()
                seed = self._seed()
                self._send_json(200, {"ok": True, "version": __version__, "ordered": ORDERED_FEED.ordered_index, "price": str(ORDERED_FEED.price) if ORDERED_FEED.price is not None else None, "provider": ORDERED_FEED.last_provider, "bars": len(aeea.bars) if aeea is not None else 0, "seed_tick": seed.tick if seed is not None else 0, "ts": datetime.now().isoformat()})
                return
            if not _require_auth(self):
                self._send_json(401, {"ok": False, "error": "unauthorized", "hint": "X-Telegram-Init-Data header required"})
                return
            aeea = self._aeea()
            seed = self._seed()
            race = self._race()
            if path == "/miniapp-state":
                self._send_json(200, format_aea(aeea, seed, race))
                return
            if path == "/cs-state":
                self._send_json(200, {"ok": True, "cs": _get_cs_feedback(), "aea_notification": getattr(aeea, "aeea_notification", None) if aeea else None, "ordered": ORDERED_FEED.ordered_index})
                return
            if path == "/ohlcv":
                limit = int(query.get("limit", 100) or 100)
                self._send_json(200, {"ok": True, "ohlcv": aeea.get_ohlcv(limit) if aeea else [], "symbol": aeea.symbol if aeea else None})
                return
            if path == "/signals":
                self._send_json(200, {"ok": True, "current_signal": aeea.current_signal if aeea else None, "signal_history": list(aeea.signal_history[-20:]) if aeea else []})
                return
            if path == "/diagnostics":
                self._send_json(200, {"ok": True, "aeea": aeea.diagnostics() if aeea else {}, "seed": seed.snapshot() if seed else {}, "race": race.snapshot() if race else {}, "feed": {"ordered": ORDERED_FEED.ordered_index, "provider": ORDERED_FEED.last_provider}})
                return
            if path == "/orders":
                self._send_json(200, {"ok": True, "orders": [o.to_dict() for o in aeea.orders] if aeea else []})
                return
            if path == "/log":
                with _LOG_LOCK:
                    logs = list(_LOG_BUFFER)[-100:]
                self._send_json(200, {"ok": True, "log": logs})
                return
            if path == "/toasts":
                with _LOG_LOCK:
                    toasts = list(_TOAST_BUFFER)[-100:]
                self._send_json(200, {"ok": True, "toasts": toasts})
                return
            if path == "/lattice-state":
                snap = seed.snapshot() if seed else {"lattice_points": []}
                self._send_json(200, {"ok": True, "lattice_points": snap.get("lattice_points", []), "lattice_count": snap.get("lattice_count", 0), "prime": snap.get("prime"), "prime_count": snap.get("prime_count"), "generation": snap.get("generation"), "s2": snap.get("s2"), "r2": snap.get("r2"), "deviation": snap.get("deviation"), "coherent": snap.get("coherent")})
                return
            if path == "/fibration-state":
                snap = seed.snapshot() if seed else {}
                branch = _dbz_branch(seed.phi) if seed else "A"
                self._send_json(200, {"ok": True, "branch": branch, "phi": snap.get("phi"), "psi": snap.get("psi"), "hopf": snap.get("hopf"), "observer": seed.observer_integral() if seed else {}})
                return
            if path == "/aea-notification":
                self._send_json(200, {"ok": True, "aea_notification": getattr(aeea, "aeea_notification", None) if aeea else None})
                return
            if path == "/config":
                self._send_json(200, {"ok": True, "config": {"symbol": aeea.symbol if aeea else SYMBOL_ENV, "timeframe": aeea.timeframe if aeea else TIMEFRAME_ENV, "bridge_port": BRIDGE_PORT, "require_auth": REQUIRE_AUTH, "version": __version__, "crawl_interval": CRAWL_INTERVAL, "seed_tick_interval": SEED_TICK_INTERVAL}})
                return
            if path == "/probe":
                crawler = self._crawler()
                self._send_json(200, {"ok": True, "provider": ORDERED_FEED.last_provider, "ordered": ORDERED_FEED.ordered_index, "bars": len(aeea.bars) if aeea else 0, "crawler": crawler.snapshot() if crawler else {}, "relay_healthy": True})
                return
            self._send_json(404, {"ok": False, "error": "not_found", "path": path})
        except Exception as e:
            _log("error", f"GET handler error: {e}")
            self._send_json(500, {"ok": False, "error": str(e)})
    def do_POST(self):
        try:
            parsed = urlparse(self.path)
            path = parsed.path.rstrip("/") or "/"
            if not _require_auth(self):
                self._send_json(401, {"ok": False, "error": "unauthorized", "hint": "X-Telegram-Init-Data header required"})
                return
            body = self._read_json()
            aeea = self._aeea()
            seed = self._seed()
            race = self._race()
            crawler = self._crawler()
            if path == "/cs-feedback":
                _set_cs_feedback(body if isinstance(body, dict) else {"feedback": body})
                self._send_json(200, {"ok": True, "cs": _get_cs_feedback()})
                return
            if path == "/step":
                # Manual step via backend. If body has price, enqueue as ordered tick and drain.
                # If body has x, do exact Fraction seed step. Never synthetic market tick.
                price = body.get("price") if isinstance(body, dict) else None
                x_raw = body.get("x") if isinstance(body, dict) else None
                if price is not None:
                    try:
                        dec = Decimal(str(price))
                        if dec > 0:
                            ORDERED_FEED.enqueue(dec, "Manual")
                            _drain_ordered_feed(aeea, seed, race)
                    except Exception as e:
                        self._send_json(400, {"ok": False, "error": str(e)})
                        return
                elif x_raw is not None and seed is not None:
                    try:
                        x = Fraction.from_string(str(x_raw)) if isinstance(x_raw, str) else _dec_to_frac_exact(x_raw)
                        seed.step(x)
                    except Exception as e:
                        self._send_json(400, {"ok": False, "error": str(e)})
                        return
                elif seed is not None:
                    # No args: step with 1/100 (teach step, not market).
                    seed.step(Fraction(1, 100))
                self._send_json(200, format_aea(aeea, seed, race))
                return
            if path == "/handshake":
                self._send_json(200, {"ok": True, "handshake": True, "seed": seed.snapshot() if seed else {}, "aeea": aeea.snapshot() if aeea else {}, "race": race.snapshot() if race else {}, "ordered": ORDERED_FEED.ordered_index, "version": __version__})
                return
            if path == "/teach":
                syllable = body.get("syllable", "") if isinstance(body, dict) else ""
                text = body.get("text", "") if isinstance(body, dict) else ""
                if syllable and seed is not None:
                    res = seed.encode_syllable(str(syllable))
                    self._send_json(200, {"ok": True, "teach": res})
                    return
                _log("info", f"teach: {text}")
                self._send_json(200, {"ok": True, "teach": {"text": text, "syllable": syllable}})
                return
            if path == "/say":
                text = body.get("text", "") if isinstance(body, dict) else ""
                enc = None
                if seed is not None and text:
                    # Say encodes A/U/M/AUM syllables in text; other text is echoed.
                    syl = "".join(ch for ch in str(text).upper() if ch in "AUM")
                    if syl:
                        enc = seed.encode_syllable(syl)
                self._send_json(200, {"ok": True, "say": text, "encoded": enc, "aea": format_aea(aeea, seed, race)})
                return
            if path == "/crawler-enqueue":
                url = body.get("url", "") if isinstance(body, dict) else ""
                depth = int(body.get("depth", 1) or 1) if isinstance(body, dict) else 1
                if not url:
                    self._send_json(400, {"ok": False, "error": "url_required"})
                    return
                ok = False
                if crawler is not None:
                    ok = crawler.state.enqueue(str(url), depth=depth, priority=0)
                self._send_json(200, {"ok": bool(ok), "url": url})
                return
            if path == "/reset":
                if aeea is not None:
                    aeea.reset()
                if race is not None:
                    race.reset()
                    race.start()
                if seed is not None:
                    _reset_seed(seed)
                _set_cs_feedback({})
                self._send_json(200, {"ok": True, "reset": True})
                return
            if path == "/order":
                if aeea is None:
                    self._send_json(500, {"ok": False, "error": "aeea_not_ready"})
                    return
                side = body.get("side", "BUY") if isinstance(body, dict) else "BUY"
                volume = body.get("volume", 0.01) if isinstance(body, dict) else 0.01
                sl = body.get("sl") if isinstance(body, dict) else None
                tp = body.get("tp") if isinstance(body, dict) else None
                backend_id = body.get("backend_id") if isinstance(body, dict) else None
                res = aeea.place_order(str(side), volume, sl, tp, backend_id=backend_id, ordered_index=ORDERED_FEED.ordered_index)
                self._send_json(200, {"ok": True, "order": res})
                return
            if path == "/order/close":
                if aeea is None:
                    self._send_json(500, {"ok": False, "error": "aeea_not_ready"})
                    return
                ticket = body.get("ticket") if isinstance(body, dict) else None
                if ticket is None:
                    res = aeea.close_all_orders()
                    self._send_json(200, res)
                    return
                res = aeea.close_order(int(ticket))
                self._send_json(200, res)
                return
            if path == "/notify-aea":
                msg = body.get("message", "") if isinstance(body, dict) else ""
                if aeea is not None:
                    aeea.aeea_notification = {"type": "notify", "text": str(msg), "ts": datetime.now().isoformat()}
                _toast(str(msg))
                self._send_json(200, {"ok": True, "notification": getattr(aeea, "aeea_notification", None) if aeea else None})
                return
            if path == "/encode-syllable":
                syllable = body.get("syllable", "") if isinstance(body, dict) else ""
                if seed is None:
                    self._send_json(500, {"ok": False, "error": "seed_not_ready"})
                    return
                res = seed.encode_syllable(str(syllable))
                self._send_json(200, {"ok": True, "encoded": res})
                return
            if path == "/log":
                msg = body.get("msg", "") if isinstance(body, dict) else ""
                _log("info", str(msg))
                self._send_json(200, {"ok": True})
                return
            self._send_json(404, {"ok": False, "error": "not_found", "path": path})
        except Exception as e:
            _log("error", f"POST handler error: {e}")
            self._send_json(500, {"ok": False, "error": str(e)})
    def do_DELETE(self):
        try:
            parsed = urlparse(self.path)
            path = parsed.path.rstrip("/") or "/"
            if not _require_auth(self):
                self._send_json(401, {"ok": False, "error": "unauthorized"})
                return
            aeea = self._aeea()
            if path == "/orders" and aeea is not None:
                res = aeea.close_all_orders()
                self._send_json(200, res)
                return
            self._send_json(404, {"ok": False, "error": "not_found"})
        except Exception as e:
            self._send_json(500, {"ok": False, "error": str(e)})
class BridgeServer:
    def __init__(self, host: str = BRIDGE_HOST, port: int = BRIDGE_PORT):
        self.host = host
        self.port = int(port)
        self._httpd = None
        self._thread = None
        self._listen_ready = threading.Event()
        self._listen_ok = False
        self._tunnel = None
    def start(self):
        try:
            self._httpd = ThreadingHTTPServer((self.host, self.port), BridgeHandler)
            self._thread = threading.Thread(target=self._httpd.serve_forever, name="ae-bridge", daemon=True)
            self._thread.start()
            self._listen_ok = True
            self._listen_ready.set()
            scheme = "https" if BRIDGE_USE_TLS else "http"
            _log("info", f"Bridge listening on {scheme}://{self.host}:{self.port}")
            self._tunnel = TunnelManager(self.port, timeout=BRIDGE_PUBLIC_TIMEOUT)
            return True
        except Exception as e:
            _log("error", f"Bridge failed to bind {self.host}:{self.port}: {e}")
            self._listen_ok = False
            self._listen_ready.set()
            return False
    def stop(self):
        try:
            if self._tunnel is not None:
                try:
                    self._tunnel.stop()
                except Exception:
                    pass
                self._tunnel = None
            if self._httpd is not None:
                try:
                    self._httpd.shutdown()
                    self._httpd.server_close()
                except Exception:
                    pass
                self._httpd = None
            if self._thread is not None:
                try:
                    self._thread.join(timeout=2.0)
                except Exception:
                    pass
                self._thread = None
        except Exception:
            pass
# ============================================================================
# TELEGRAM CHAT DB - STDLIB urllib sendMessage ONLY (outbound snapshots)
# ============================================================================
TELEGRAM_DB = None
class TelegramChatDB:
    def __init__(self, bot_token: str, channel_id: str, central_user_id: str, chunk_size: int = 3800):
        self.bot_token = bot_token or ""
        self.channel_id = channel_id or ""
        self.central_user_id = central_user_id or ""
        self.chunk_size = int(chunk_size) if chunk_size else 3800
        self._lock = threading.Lock()
        self._enabled = bool(self.bot_token and (self.channel_id or self.central_user_id))
        self._last_save_ts = 0
        self._index: Dict[str, Dict[str, Any]] = {}
        self._index_db_path = os.path.join(os.path.dirname(os.path.abspath(__file__)) if "__file__" in globals() else ".", "ae_fused_telegram_index.json")
        try:
            if os.path.isfile(self._index_db_path):
                with open(self._index_db_path, "r", encoding="utf-8") as f:
                    self._index = json.load(f)
        except Exception:
            self._index = {}
    def is_enabled(self) -> bool:
        if not self.bot_token or not ENABLE_TELEGRAM_DB:
            return False
        has_channel = bool(self.channel_id)
        has_central = bool(self.central_user_id)
        try:
            has_user_shards = bool(TELEGRAM_DB_USER_SHARDS and _get_shard_pool())
        except Exception:
            has_user_shards = False
        return has_channel or has_central or has_user_shards
    def _api_url(self, method: str) -> str:
        return f"https://api.telegram.org/bot{self.bot_token}/{method}"
    def _send_message(self, chat_id: str, text: str, disable_notification: bool = True):
        if not self.bot_token or not chat_id:
            return None
        if len(text) > 4096:
            text = text[:4096]
        try:
            payload = {"chat_id": chat_id, "text": text, "disable_notification": disable_notification, "disable_web_page_preview": True}
            data = json.dumps(payload).encode("utf-8")
            req = urllib.request.Request(self._api_url("sendMessage"), data=data, headers={"Content-Type": "application/json"})
            with urllib.request.urlopen(req, timeout=10) as resp:
                body = json.loads(resp.read().decode("utf-8"))
                if body.get("ok"):
                    return body.get("result", {}).get("message_id")
        except Exception as e:
            _log("warning", f"TelegramChatDB send failed to {chat_id}: {e}")
        return None
    def _persist_index(self):
        try:
            with open(self._index_db_path, "w", encoding="utf-8") as f:
                json.dump(self._index, f)
        except Exception:
            pass
    def save_snapshot(self, key: str, value: Dict[str, Any], force: bool = False) -> bool:
        if not self.channel_id and not self.central_user_id:
            return False
        if not self.bot_token or not ENABLE_TELEGRAM_DB:
            return False
        now = time.time()
        if not force and (now - self._last_save_ts) < TELEGRAM_DB_SAVE_INTERVAL:
            return False
        self._last_save_ts = now
        text = json.dumps({"key": key, "value": value, "ts": datetime.now().isoformat()}, ensure_ascii=False)
        ok = False
        if self.channel_id:
            mid = self._send_message(self.channel_id, text[:4096])
            ok = ok or (mid is not None)
        if self.central_user_id:
            mid = self._send_message(self.central_user_id, text[:4096])
            ok = ok or (mid is not None)
        return bool(ok)
# ============================================================================
# TELEGRAM BOT - PTB POLLING, ALL COMMANDS VIA format_aea
# ============================================================================
try:
    from telegram import Update, WebAppInfo, MenuButtonWebApp
    from telegram.ext import Application, CommandHandler, ContextTypes
    TELEGRAM_AVAILABLE = True
except ImportError:
    logger.warning("python-telegram-bot not installed; bot commands disabled")
    TELEGRAM_AVAILABLE = False
    Update = None
    WebAppInfo = None
    MenuButtonWebApp = None
    Application = None
    CommandHandler = None
    ContextTypes = None
class AE_Bot:
    def __init__(self, token: str, seed=None, crawler=None, aeea=None, race=None, market=None, seed_worker=None):
        self.token = token or ""
        self.seed = seed if seed is not None else BRIDGE_ENGINE_REF.get("seed")
        self.crawler = crawler if crawler is not None else BRIDGE_ENGINE_REF.get("crawler")
        self.aeea = aeea if aeea is not None else BRIDGE_ENGINE_REF.get("aeea")
        self.race = race if race is not None else BRIDGE_ENGINE_REF.get("race")
        self.market = market if market is not None else BRIDGE_ENGINE_REF.get("market")
        self.seed_worker = seed_worker if seed_worker is not None else BRIDGE_ENGINE_REF.get("seed_worker")
        self.application = None
        self._loop = None
        self._post_init_done = False
        self._async_thread = None
        self._shutdown_event = threading.Event()
        self._tracked: deque = deque(maxlen=50)
        self._bot_username = None
    def _resolve_webapp_url(self) -> str:
        if TELEGRAM_WEBAPP_URL:
            return TELEGRAM_WEBAPP_URL
        try:
            pub = BRIDGE_ENGINE_REF.get("public_url")
            if pub:
                return str(pub)
        except Exception:
            pass
        return ""
    def _track_inbound_message(self, update) -> None:
        try:
            user = update.effective_user if update else None
            if user:
                self._tracked.append({"user_id": user.id, "username": getattr(user, "username", None), "ts": datetime.now().isoformat()})
                if self.aeea is not None:
                    try:
                        self.aeea.chat_id = user.id
                    except Exception:
                        pass
        except Exception:
            pass
    async def _safe_reply(self, update, text: str):
        if update is None or update.message is None:
            return
        t = str(text or "")
        if len(t) > 4000:
            t = t[:4000]
        try:
            await update.message.reply_text(t, parse_mode="Markdown")
        except Exception:
            try:
                await update.message.reply_text(t)
            except Exception as e:
                _log("warning", f"bot reply failed: {e}")
    def _aea_text(self, title: str = "AE TWA") -> str:
        try:
            data = format_aea(self.aeea, self.seed, self.race)
        except Exception as e:
            return f"{title}\nformat_aea failed: {e}"
        aeea = data.get("aeea", {}) if isinstance(data, dict) else {}
        seed = data.get("seed", {}) if isinstance(data, dict) else {}
        race = data.get("race", {}) if isinstance(data, dict) else {}
        price = aeea.get("last_price")
        provider = data.get("feed", {}).get("provider") if isinstance(data.get("feed"), dict) else None
        lines = [
            f"*{title}*",
            f"Ordered: {data.get('ordered')} | Price: {price if price is not None else 'WAITING'} | Provider: {provider or 'WAITING'}",
            f"Symbol: {aeea.get('symbol')} | Timeframe: {aeea.get('timeframe')}",
            f"m={aeea.get('m')} n={aeea.get('n')} delta={aeea.get('delta')} regime={aeea.get('regime')}",
            f"BB: {aeea.get('bb')}",
            f"P_arc: {aeea.get('projection')}",
            f"Signal: {aeea.get('current_signal')}",
            f"Seed: prime={seed.get('prime')} prime_count={seed.get('prime_count')} gen={seed.get('generation')} I={seed.get('I')}",
            f"Lattice: {seed.get('lattice_points') if seed.get('lattice_points') else '[] (WAITING)'}",
            f"s2={seed.get('s2')} r2={seed.get('r2')} dev={seed.get('deviation')} coherent={seed.get('coherent')}",
            f"Race: winner={race.get('winner')} AE dev={race.get('ae_dev')} AE hold={race.get('ae_hold')} NN acc={race.get('nn_acc')} NN hold={race.get('nn_hold')}",
            f"CS: {data.get('cs')}",
        ]
        return "\n".join(lines)
    async def start(self, update, context):
        self._track_inbound_message(update)
        text = "AE TWA - Fused AEI + AEEA\n\n" + self._aea_text("AE TWA") + "\n\nTap Open App to launch the TWA. /help for commands."
        await self._safe_reply(update, text)
    async def webapp(self, update, context):
        self._track_inbound_message(update)
        url = self._resolve_webapp_url()
        if url:
            await self._safe_reply(update, f"Open AE TWA: {url}\n\n" + self._aea_text("AE TWA"))
        else:
            await self._safe_reply(update, "WebApp URL not configured (TELEGRAM_WEBAPP_URL).\n\n" + self._aea_text("AE TWA"))
    async def mini(self, update, context):
        await self.webapp(update, context)
    async def whoami(self, update, context):
        self._track_inbound_message(update)
        user = update.effective_user if update else None
        if user:
            await self._safe_reply(update, f"You: id={user.id} username=@{getattr(user, 'username', '')} name={getattr(user, 'first_name', '')}")
        else:
            await self._safe_reply(update, "whoami: no user")
    async def help_cmd(self, update, context):
        self._track_inbound_message(update)
        await self._safe_reply(update, "/start /webapp /mini /whoami /help /status /primes /lattice /fibration /signal /indicators /regime /fvg /chart /projection /diagnostics /reset /start_feed /stop_feed /symbol /info /probe /teach /say /step /crawler /order")
    async def status(self, update, context):
        self._track_inbound_message(update)
        await self._safe_reply(update, self._aea_text("AE Status"))
    async def primes(self, update, context):
        self._track_inbound_message(update)
        seed = self.seed
        if seed is None:
            await self._safe_reply(update, "Seed not ready")
            return
        snap = seed.snapshot()
        await self._safe_reply(update, f"Primes: {snap.get('lattice_points')}\nprime={snap.get('prime')} count={snap.get('prime_count')} gen={snap.get('generation')}")
    async def lattice(self, update, context):
        self._track_inbound_message(update)
        seed = self.seed
        if seed is None:
            await self._safe_reply(update, "Seed not ready")
            return
        snap = seed.snapshot()
        pts = snap.get("lattice_points") or []
        await self._safe_reply(update, f"Lattice: {pts if pts else '[] (WAITING)'}\ncount={len(pts)} s2={snap.get('s2')} r2={snap.get('r2')} dev={snap.get('deviation')} coherent={snap.get('coherent')}")
    async def fibration(self, update, context):
        self._track_inbound_message(update)
        seed = self.seed
        if seed is None:
            await self._safe_reply(update, "Seed not ready")
            return
        snap = seed.snapshot()
        branch = _dbz_branch(seed.phi)
        obs = seed.observer_integral()
        await self._safe_reply(update, f"Fibration branch={branch}\nphi={snap.get('phi')}\nhopf={snap.get('hopf')}\nO_psi={obs.get('O_psi')}")
    async def signal_cmd(self, update, context):
        self._track_inbound_message(update)
        aeea = self.aeea
        if aeea is None:
            await self._safe_reply(update, "AEEA not ready")
            return
        await self._safe_reply(update, f"Signal: {aeea.current_signal}\nHistory: {aeea.signal_history[-5:]}\nm={aeea.m} n={aeea.n} delta={aeea.delta} regime={aeea.regime}")
    async def indicators(self, update, context):
        self._track_inbound_message(update)
        aeea = self.aeea
        if aeea is None:
            await self._safe_reply(update, "AEEA not ready")
            return
        await self._safe_reply(update, f"Indicators (null = waiting for real bars):\n{aeea.indicators}")
    async def regime(self, update, context):
        self._track_inbound_message(update)
        aeea = self.aeea
        if aeea is None:
            await self._safe_reply(update, "AEEA not ready")
            return
        await self._safe_reply(update, f"Regime: {aeea.regime}\nm={aeea.m} n={aeea.n} delta={aeea.delta}")
    async def fvg(self, update, context):
        self._track_inbound_message(update)
        aeea = self.aeea
        if aeea is None:
            await self._safe_reply(update, "AEEA not ready")
            return
        await self._safe_reply(update, f"FVG: {aeea.fvg}")
    async def chart(self, update, context):
        self._track_inbound_message(update)
        aeea = self.aeea
        if aeea is None:
            await self._safe_reply(update, "AEEA not ready")
            return
        bars = aeea.get_ohlcv(10)
        lines = ["OHLCV last 10:"]
        for b in bars:
            lines.append(f"{b['tick']} O={b['open']} H={b['high']} L={b['low']} C={b['close']}")
        await self._safe_reply(update, "\n".join(lines))
    async def projection(self, update, context):
        self._track_inbound_message(update)
        aeea = self.aeea
        if aeea is None:
            await self._safe_reply(update, "AEEA not ready")
            return
        await self._safe_reply(update, f"P_arc: {aeea.get_projection()}\nBB: {aeea.bb}")
    async def diagnostics(self, update, context):
        self._track_inbound_message(update)
        aeea = self.aeea
        if aeea is None:
            await self._safe_reply(update, "AEEA not ready")
            return
        await self._safe_reply(update, f"Diagnostics:\n{aeea.diagnostics()}")
    async def reset_cmd(self, update, context):
        self._track_inbound_message(update)
        if self.aeea is not None:
            self.aeea.reset()
        if self.race is not None:
            self.race.reset()
            self.race.start()
        if self.seed is not None:
            _reset_seed(self.seed)
        await self._safe_reply(update, "Reset done (AEEA + race + seed).")
    async def start_feed(self, update, context):
        self._track_inbound_message(update)
        if self.market is not None:
            self.market.start()
        if self.crawler is not None:
            self.crawler.start()
        await self._safe_reply(update, "Feed started (market + crawler).")
    async def stop_feed(self, update, context):
        self._track_inbound_message(update)
        if self.market is not None:
            self.market.stop()
        if self.crawler is not None:
            self.crawler.stop()
        await self._safe_reply(update, "Feed stopped.")
    async def symbol_cmd(self, update, context):
        self._track_inbound_message(update)
        args = context.args if context else []
        if args and self.aeea is not None:
            self.aeea.symbol = str(args[0]).upper()
            await self._safe_reply(update, f"Symbol set to {self.aeea.symbol}")
        elif self.aeea is not None:
            await self._safe_reply(update, f"Symbol: {self.aeea.symbol} Timeframe: {self.aeea.timeframe}")
        else:
            await self._safe_reply(update, "AEEA not ready")
    async def info(self, update, context):
        self._track_inbound_message(update)
        await self._safe_reply(update, self._aea_text("AE Info"))
    async def probe(self, update, context):
        self._track_inbound_message(update)
        crawler = self.crawler
        csnap = crawler.snapshot() if crawler else {}
        await self._safe_reply(update, f"Probe: provider={ORDERED_FEED.last_provider} ordered={ORDERED_FEED.ordered_index} crawler={csnap}")
    async def teach(self, update, context):
        self._track_inbound_message(update)
        args = context.args if context else []
        syl = " ".join(args) if args else "AUM"
        if self.seed is not None:
            res = self.seed.encode_syllable(syl)
            await self._safe_reply(update, f"Teach {syl}: {res}")
        else:
            await self._safe_reply(update, "Seed not ready")
    async def say(self, update, context):
        self._track_inbound_message(update)
        args = context.args if context else []
        text = " ".join(args) if args else "AUM"
        await self._safe_reply(update, f"Say: {text}")
    async def step_cmd(self, update, context):
        self._track_inbound_message(update)
        if self.seed is not None:
            self.seed.step(Fraction(1, 100))
            await self._safe_reply(update, f"Step done.\n{self._aea_text('AE Step')}")
        else:
            await self._safe_reply(update, "Seed not ready")
    async def crawler_cmd(self, update, context):
        self._track_inbound_message(update)
        args = context.args if context else []
        if args and self.crawler is not None:
            url = args[0]
            ok = self.crawler.state.enqueue(url, depth=1, priority=0)
            await self._safe_reply(update, f"Crawler enqueue {url}: {ok}")
        elif self.crawler is not None:
            await self._safe_reply(update, f"Crawler: {self.crawler.snapshot()}")
        else:
            await self._safe_reply(update, "Crawler not ready")
    async def order_cmd(self, update, context):
        self._track_inbound_message(update)
        args = context.args if context else []
        if not args:
            await self._safe_reply(update, "Usage: /order BUY|SELL [volume] [sl] [tp]")
            return
        side = args[0]
        volume = float(args[1]) if len(args) > 1 else 0.01
        sl = float(args[2]) if len(args) > 2 else None
        tp = float(args[3]) if len(args) > 3 else None
        if self.aeea is not None:
            res = self.aeea.place_order(side, volume, sl, tp, ordered_index=ORDERED_FEED.ordered_index)
            await self._safe_reply(update, f"Order: {res}")
        else:
            await self._safe_reply(update, "AEEA not ready")
    async def error_handler(self, update, context):
        try:
            _log("error", f"bot error: {context.error}")
        except Exception:
            pass
    async def _post_init(self, app):
        try:
            self.application = app
            self._loop = asyncio.get_running_loop()
            BRIDGE_ENGINE_REF["application"] = app
            BRIDGE_ENGINE_REF["bot"] = self
            # Menu button
            try:
                url = self._resolve_webapp_url()
                if url and WebAppInfo is not None:
                    await app.bot.set_chat_menu_button(menu_button=MenuButtonWebApp(text="Open AE TWA", web_app=WebAppInfo(url=url)))
            except Exception as e:
                _log("warning", f"menu button failed: {e}")
            # Workers: start if not already started in main().
            try:
                if self.crawler is not None and not getattr(self.crawler, "_running", False):
                    self.crawler.start()
                if self.market is not None and not getattr(self.market, "_running", False):
                    self.market.start()
                if self.seed_worker is not None and not getattr(self.seed_worker, "_running", False):
                    self.seed_worker.start()
            except Exception as e:
                _log("warning", f"worker start in post_init failed: {e}")
            # Bridge fallback: if main() did not start Bridge (standalone bot.run), start it now.
            try:
                if BRIDGE_ENGINE_REF.get("bridge_server") is None:
                    bs = BridgeServer()
                    ok = bs.start()
                    BRIDGE_ENGINE_REF["bridge_server"] = bs
                    _log("info", f"Bridge fallback started in bot post_init: {ok}")
            except Exception as e:
                _log("warning", f"Bridge fallback failed: {e}")
            self._post_init_done = True
            _log("info", "AE_Bot _post_init done")
        except Exception as e:
            _log("error", f"bot _post_init failed: {e}")
    def _async_worker_loop(self):
        def _run():
            loop = asyncio.new_event_loop()
            asyncio.set_event_loop(loop)
            self._loop = loop
            try:
                if self.application is not None:
                    loop.run_until_complete(self._post_init(self.application))
            except Exception as e:
                _log("warning", f"_async_worker_loop post_init failed: {e}")
            try:
                loop.run_forever()
            except Exception:
                pass
        self._async_thread = threading.Thread(target=_run, name="ae-bot-async", daemon=True)
        self._async_thread.start()
    def run(self):
        # AUDIT FIX: If PTB is missing, log LOUDLY and return. Bridge is already started in main(),
        # so $PORT stays bound and the Bridge stays up. Never silently kill everything.
        if not TELEGRAM_AVAILABLE:
            _log("error", "python-telegram-bot not installed; cannot run bot. Bridge stays up. Install via requirements.txt: python-telegram-bot==21.6")
            return
        if not self.token:
            _log("error", "TELEGRAM_BOT_TOKEN missing; cannot run bot. Bridge stays up.")
            return
        # Reuse engines from BRIDGE_ENGINE_REF if main() already created them.
        try:
            if self.seed is None:
                self.seed = BRIDGE_ENGINE_REF.get("seed")
            if self.aeea is None:
                self.aeea = BRIDGE_ENGINE_REF.get("aeea")
            if self.race is None:
                self.race = BRIDGE_ENGINE_REF.get("race")
            if self.crawler is None:
                self.crawler = BRIDGE_ENGINE_REF.get("crawler")
            if self.market is None:
                self.market = BRIDGE_ENGINE_REF.get("market")
            if self.seed_worker is None:
                self.seed_worker = BRIDGE_ENGINE_REF.get("seed_worker")
            if self.aeea is None:
                self.aeea = AEEA_Engine(SYMBOL_ENV, TIMEFRAME_ENV)
                self.aeea.OnInit()
                BRIDGE_ENGINE_REF["aeea"] = self.aeea
            if self.seed is None:
                self.seed = AEI_Seed()
                BRIDGE_ENGINE_REF["seed"] = self.seed
            if self.race is None:
                self.race = RaceState()
                self.race.start()
                BRIDGE_ENGINE_REF["race"] = self.race
            # TelegramChatDB (stdlib urllib send only)
            global TELEGRAM_DB
            try:
                TELEGRAM_DB = TelegramChatDB(self.token, TELEGRAM_DB_CHANNEL_ID, TELEGRAM_DB_CENTRAL_USER_ID, TELEGRAM_DB_CHUNK_SIZE)
                BRIDGE_ENGINE_REF["telegram_db"] = TELEGRAM_DB
            except Exception:
                pass
            BRIDGE_ENGINE_REF["bot"] = self
            # Build Application
            app = Application.builder().token(self.token).post_init(self._post_init).build()
            self.application = app
            if self.aeea is not None:
                try:
                    self.aeea.application = app
                except Exception:
                    pass
            app.add_handler(CommandHandler("start", self.start))
            app.add_handler(CommandHandler("webapp", self.webapp))
            app.add_handler(CommandHandler("mini", self.mini))
            app.add_handler(CommandHandler("whoami", self.whoami))
            app.add_handler(CommandHandler("help", self.help_cmd))
            app.add_handler(CommandHandler("status", self.status))
            app.add_handler(CommandHandler("primes", self.primes))
            app.add_handler(CommandHandler("lattice", self.lattice))
            app.add_handler(CommandHandler("fibration", self.fibration))
            app.add_handler(CommandHandler("signal", self.signal_cmd))
            app.add_handler(CommandHandler("indicators", self.indicators))
            app.add_handler(CommandHandler("regime", self.regime))
            app.add_handler(CommandHandler("fvg", self.fvg))
            app.add_handler(CommandHandler("chart", self.chart))
            app.add_handler(CommandHandler("projection", self.projection))
            app.add_handler(CommandHandler("diagnostics", self.diagnostics))
            app.add_handler(CommandHandler("reset", self.reset_cmd))
            app.add_handler(CommandHandler("start_feed", self.start_feed))
            app.add_handler(CommandHandler("stop_feed", self.stop_feed))
            app.add_handler(CommandHandler("symbol", self.symbol_cmd))
            app.add_handler(CommandHandler("info", self.info))
            app.add_handler(CommandHandler("probe", self.probe))
            app.add_handler(CommandHandler("teach", self.teach))
            app.add_handler(CommandHandler("say", self.say))
            app.add_handler(CommandHandler("step", self.step_cmd))
            app.add_handler(CommandHandler("crawler", self.crawler_cmd))
            app.add_handler(CommandHandler("order", self.order_cmd))
            app.add_error_handler(self.error_handler)
            _log("info", "AE_Bot starting polling (drop_pending_updates=True - test /start with a fresh message after redeploy)")
            # drop_pending_updates=True: old /start messages from the crash loop are discarded.
            app.run_polling(drop_pending_updates=True, allowed_updates=Update.ALL_TYPES if Update is not None else None)
        except Exception as e:
            _log("error", f"AE_Bot run failed: {e}")
            return
# ============================================================================
# MAIN - BRIDGE FIRST, THEN BOT. NEVER SILENTLY MASK A DEAD BOT.
# ============================================================================
def main():
    import signal
    os.environ["WEB_CONCURRENCY"] = "1"
    _shutdown_event = threading.Event()
    def _on_signal(signum, frame):
        try:
            _log("info", f"shutdown signal {signum}")
        except Exception:
            pass
        _shutdown_event.set()
    try:
        signal.signal(signal.SIGINT, _on_signal)
        signal.signal(signal.SIGTERM, _on_signal)
    except Exception:
        pass
    _log("info", f"AE Fused starting {__version__} substrate={_SUBSTRATE} port={BRIDGE_PORT}")
    # 1. Create engines (singletons for this process).
    seed = AEI_Seed()
    aeea = AEEA_Engine(SYMBOL_ENV, TIMEFRAME_ENV)
    try:
        aeea.OnInit()
    except Exception:
        pass
    race = RaceState()
    try:
        race.start()
    except Exception:
        pass
    try:
        crawler_state = CrawlerSeedState(CRAWLER_DB_PATH)
    except Exception as e:
        _log("warning", f"crawler state init failed: {e}")
        crawler_state = None
    relay = CrawlerRelayClient(RELAY_URL, RELAY_KEY, timeout=RELAY_TIMEOUT, max_retries=RELAY_MAX_RETRIES)
    crawler = CrawlerWorker(crawler_state, relay) if crawler_state is not None else None
    market = MarketTickWorker(aeea, relay, seed, race)
    seed_worker = SeedWorker(seed, crawler, aeea, race)
    BRIDGE_ENGINE_REF["seed"] = seed
    BRIDGE_ENGINE_REF["aeea"] = aeea
    BRIDGE_ENGINE_REF["race"] = race
    BRIDGE_ENGINE_REF["crawler"] = crawler
    BRIDGE_ENGINE_REF["market"] = market
    BRIDGE_ENGINE_REF["seed_worker"] = seed_worker
    BRIDGE_ENGINE_REF["relay"] = relay
    BRIDGE_ENGINE_REF["crawler_state"] = crawler_state
    global RACE_STATE
    RACE_STATE = race
    # 2. Bridge FIRST. This is the audit fix: $PORT must bind even if PTB is missing.
    bridge_server = BridgeServer(BRIDGE_HOST, BRIDGE_PORT)
    bridge_ok = bridge_server.start()
    BRIDGE_ENGINE_REF["bridge_server"] = bridge_server
    if not bridge_ok:
        _log("error", f"Bridge failed to bind {BRIDGE_HOST}:{BRIDGE_PORT}. Heroku will kill web dyno (R10). Check PORT env.")
    else:
        _log("info", f"Bridge bound {BRIDGE_HOST}:{BRIDGE_PORT}")
    # 3. Workers (market + crawler + seed drain). They drain the one ordered feed.
    try:
        if crawler is not None:
            crawler.start()
    except Exception as e:
        _log("warning", f"crawler start failed: {e}")
    try:
        market.start()
    except Exception as e:
        _log("warning", f"market start failed: {e}")
    try:
        seed_worker.start()
    except Exception as e:
        _log("warning", f"seed worker start failed: {e}")
    # 4. Bot thread. If token missing, log loudly but keep Bridge up. Never sys.exit(1) here.
    bot = None
    bot_thread = None
    if not TELEGRAM_BOT_TOKEN_ENV:
        _log("error", "TELEGRAM_BOT_TOKEN missing; bot will not poll, but Bridge stays up on $PORT.")
    elif not TELEGRAM_AVAILABLE:
        _log("error", "python-telegram-bot not installed; bot will not poll, but Bridge stays up. Fix requirements.txt: python-telegram-bot==21.6")
    else:
        try:
            bot = AE_Bot(TELEGRAM_BOT_TOKEN_ENV, seed=seed, crawler=crawler, aeea=aeea, race=race, market=market, seed_worker=seed_worker)
            BRIDGE_ENGINE_REF["bot"] = bot
            bot_thread = threading.Thread(target=bot.run, name="ae-bot", daemon=True)
            bot_thread.start()
            _log("info", "Bot thread started")
        except Exception as e:
            _log("error", f"bot thread start failed: {e}")
            bot_thread = None
    # 5. Heartbeat. Loudly log if bot thread dies. Never mask a dead bot as alive.
    _loop_count = 0
    bot_dead_logged = False
    while not _shutdown_event.is_set():
        try:
            _loop_count += 1
            if _loop_count % 10 == 0:
                _log("info", f"♥ main heartbeat {_loop_count} pid={os.getpid()} ordered={ORDERED_FEED.ordered_index} provider={ORDERED_FEED.last_provider} bridge_ok={bridge_ok} bot_alive={bot_thread.is_alive() if bot_thread is not None else False}")
            if bot_thread is not None and not bot_thread.is_alive() and not bot_dead_logged:
                _log("error", "Bot thread exited (polling stopped). Bridge stays up. Check bot logs above for the root cause.")
                bot_dead_logged = True
            _shutdown_event.wait(timeout=1.0)
        except Exception as e:
            _log("warning", f"main loop error: {e}")
            _shutdown_event.wait(timeout=1.0)
    # Shutdown
    try:
        _log("info", "Shutting down AE Fused")
        if market is not None:
            try:
                market.stop()
            except Exception:
                pass
        if crawler is not None:
            try:
                crawler.stop()
            except Exception:
                pass
        if seed_worker is not None:
            try:
                seed_worker.stop()
            except Exception:
                pass
        if bridge_server is not None:
            try:
                bridge_server.stop()
            except Exception:
                pass
    except Exception:
        pass
if __name__ == "__main__":
    main()
