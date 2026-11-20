#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AE TWA - Fused backend.

One ordered feed advances both engines:
  - AEEA market engine: bars -> 13 normalised indicators + Ichimoku -> m/n/delta
    -> regime -> BB family 3-60 -> P_arc -> signal iff H/L gate -> orders/trailing/FVG.
  - AEI seed loop: prime -> outward lattice -> Hopf -> s2 vs r2 -> deviation
    -> DbZ -> I -> SelfEvolution. The seed step runs in the backend, on the
    same tick, with x lifted in the backend from the crawler hash fraction when a crawled
    document has been hashed (CrawlerState.last_hash_frac), else price fallback
    x = abs(price - prevPrice) / 10000, or 1/100 when the delta is zero,
    labelled x_source='price-fallback' and never presented as FG x.
    The frontend never computes x and never sends x.

Canonical contracts in this file:
  - m/n: 13 loop votes plus one Ichimoku vote. Maximum is 14, not 13.
    Effective thresholds are F_PLUS_GF = 208/3 = 69.333... for m and
    G_MINUS_GF = 92/3 = 30.666... for n. The tolerance is 8/3.
  - Identity: AEEA TWA is FF itself. AEI TWA is FG itself. AE TWA is
    the FF/FG fusion. FF takes precedence for market engine. FG takes
    precedence for seed loop.
  - Intelligence gate (FG): I = alignment x riemann x stability x refined.
    Gate is I >= 2/3. Unity is I = 1. Coherence gate is s = r, checked
    as s2 = r2 for s, r >= 0. A generation is kept when s2 = r2 and
    I >= 2/3. Unity is s = r and I = 1.
  - H/L gate: H fires when m >= 12, L fires when n >= 12.
  - H/L gate (signal firing, FF _signal): BUY when m >= 12, SELL when n >= 12.
    This H/L gate is NOT the Kronecker gate. Do not label H/L as delta.
  - Kronecker gate: imbalance = m - n - 2. Kronecker delta(imbalance) = 1 iff
    imbalance == 0 iff m - n == 2. delta_gate_met = (imbalance == 0).
    The Kronecker gate is reported separately and does NOT fire signals.
  - Bridge regime (display only, NOT FF Regime): BULLISH when imbalance > 2,
    BEARISH when imbalance < -2, else NEUTRAL. FF engine Regime is the
    sRange/tRange/sVolatile/tVolatile/sTrend/tTrend/Stable/Unknown taxonomy
    in st.Regime, reported as engine_regime.
  - BB family (FF): Bollinger family, integer periods 3 to 60, deviation 2, close, shift 0, population sigma. Backend _bb_family_from_bars computes the whole family from real bars. Backend _bb58_from_bars is ONE member (period 58), never canonical. Null until that period has that many real bars. Frontend renders backend family and provides bbToBigFixed as a display helper (BigInt accumulators exact, final sqrt float64 per FF A-M6).
  - One formatter: format_aea is the single entry point for bot and
    TWA messages. The _format_push_message is an internal helper
    called only through format_aea.
  - One state: GET /miniapp-state returns feed, aeea, seed, ordered, cs, acoustization (FUSION INVENTION, not FG), observer (FG integral), evolution (FG SelfEvolutionCore), crawler, aea_notification in one tick. No toy opponent. No race field.
  - CS display: the CS closure display shows the closure value as
    defined in the file. It is display, not a formal proof.
  - Auth fails closed: if REQUIRE_AUTH is on and no bot token is
    configured, requests are rejected. Explicit REQUIRE_AUTH=0 is the
    only opt-out.
  - CORS: when CORS_ORIGIN is "*", the backend returns "*". It never
    reflects an arbitrary request Origin.
"""


import asyncio
import hashlib
import hmac
import json
import math
import os
import queue
import sys
if hasattr(sys, "set_int_max_str_digits"):
    try:
        sys.set_int_max_str_digits(1000000)
    except Exception:
        pass
import ssl
import logging
import subprocess
import threading
import time
import re as _re_bridge
import urllib.parse
import urllib.request
import urllib.error
from collections import deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qsl
from dataclasses import dataclass, field
from datetime import datetime
from typing import List, Dict, Optional, Tuple, Any
from fractions import Fraction as PyFraction
from decimal import Decimal, getcontext

getcontext().prec = 50

ARC_COHERENCE_TOLERANCE = 1e-6

# ============================================================================
# SYMBOLIC π DERIVATION
# ============================================================================
def _compute_pi_decimal() -> Decimal:
    _saved_prec = getcontext().prec
    getcontext().prec = 60
    try:
        def atan_inv(n: int) -> Decimal:
            n_d = Decimal(n)
            n_sq = n_d * n_d
            term = Decimal(1) / n_d
            total = term
            sign = -1
            k = 1
            while True:
                term = term / n_sq
                add = term / Decimal(2 * k + 1)
                if add == 0:
                    break
                total = total + Decimal(sign) * add
                sign = -sign
                k += 1
                if k > 1000:
                    break
            return total
        pi_val = Decimal(16) * atan_inv(5) - Decimal(4) * atan_inv(239)
    finally:
        getcontext().prec = _saved_prec
    return pi_val

_PI_D: Decimal = _compute_pi_decimal()
_TWO_PI_D: Decimal = _PI_D * Decimal(2)
# : 15-digit convergent of π. Relative error ≈ 3×10⁻¹⁶, compatible
# with the 5-decimal-place final quantization of the projection.
_PI_FRAC: PyFraction = PyFraction(3141592653589793, 1000000000000000)

# ============================================================================
# EXACT FRACTION WRAPPER
# ============================================================================
class Fraction:
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

    def __neg__(self):
        return Fraction(-self._f.numerator, self._f.denominator)

    def __pos__(self):
        return self

    def __eq__(self, other):
        try:
            o = Fraction._wrap(other)
            return self._f == o._f
        except Exception:
            return False

    def __lt__(self, other):
        o = Fraction._wrap(other)
        return self._f < o._f

    def __le__(self, other):
        o = Fraction._wrap(other)
        return self._f <= o._f

    def __gt__(self, other):
        o = Fraction._wrap(other)
        return self._f > o._f

    def __ge__(self, other):
        o = Fraction._wrap(other)
        return self._f >= o._f

    def __hash__(self):
        return hash(self._f)

    def to_decimal(self) -> Decimal:
        return Decimal(self._f.numerator) / Decimal(self._f.denominator)

    def to_float(self) -> float:
        return float(self._f.numerator) / float(self._f.denominator)

    def __str__(self):
        if self._f.denominator == 1:
            return str(self._f.numerator)
        return f"{self._f.numerator}/{self._f.denominator}"

    def __repr__(self):
        return f"Fraction({self._f.numerator}/{self._f.denominator})"

# ============================================================================
# : ULP-SAFE THRESHOLD COMPARISON
# ============================================================================
def _dec_to_frac_exact(d: Decimal) -> PyFraction:
    """Lift a Decimal to an exact PyFraction via its digit tuple.
    No float64 round-trip. This is the C-3 primitive: it allows the
    indicator value (a Decimal constructed from a float64 in
    _normalize) to be compared against the exact rational threshold
    without a ±1 ULP flip at the seam."""
    if not isinstance(d, Decimal):
        d = Decimal(str(d))
    if d.is_zero():
        return PyFraction(0, 1)
    sign, digits, exp = d.as_tuple()
    if not isinstance(exp, int):
        return PyFraction(0, 1)
    int_val = 0
    for digit in digits:
        int_val = int_val * 10 + digit
    if sign:
        int_val = -int_val
    if exp < 0:
        return PyFraction(int_val, 10 ** (-exp))
    return PyFraction(int_val * (10 ** exp), 1)

def _cmp_frac(dec_value: Decimal, frac_threshold: PyFraction) -> int:
    """Return -1, 0, or 1 as dec_value <, ==, or > frac_threshold.
    Exact rational comparison. No float64 round-trip."""
    a = _dec_to_frac_exact(dec_value)
    if a < frac_threshold:
        return -1
    if a > frac_threshold:
        return 1
    return 0

# ============================================================================
# / m-6: CS-TRANSLATION HELPERS
# ============================================================================
def _md_escape(value) -> str:
    if value is None:
        return "—"
    s = str(value)
    out_chars = []
    for ch in s:
        if ch == '\\':
            out_chars.append('\\\\')
        elif ch == '*':
            out_chars.append('\\*')
        elif ch == '_':
            out_chars.append('\\_')
        elif ch == '`':
            out_chars.append('\\`')
        elif ch == '[':
            out_chars.append('\\[')
        elif ch == ']':
            out_chars.append('\\]')
        elif ch == '<':
            out_chars.append('&lt;')
        elif ch == '>':
            out_chars.append('&gt;')
        else:
            out_chars.append(ch)
    return ''.join(out_chars)

_CS_VALUE_MAP: Dict[str, str] = {
    "BUY": "↑",
    "SELL": "↓",
    "NEUTRAL": "⊙",
    "ACTIVE": "𝒜₃",
    "INACTIVE": "𝒜₄",
    "ON": "𝒜₃",
    "OFF": "𝒜₄",
    "UP": "↟",
    "DOWN": "↡",
    "LONG": "↑",
    "SHORT": "↓",
    "CLOSE": "𝒞_Close",
    "NONE": "𝒩",
    "FLYING": "↟",
    "FALLING": "↡",
    "WAIT/DECERN": "⋯",
    "YES": "⟦𝒴⟧",
    "NO": "⟦𝒩⟧",
    "TRUE": "⟦𝒯⟧",
    "FALSE": "⟦ℱ⟧",
    "BULLISH": "𝒮_Bull",
    "BEARISH": "𝒮_Bear",
    "UNKNOWN": "𝒰",
    "STABLE": "𝒮_Stable",
}

def _cs(value) -> str:
    """C-2: Translate a natural-language value-string to its CS notation.
    Idempotent: an already-CS string is returned unchanged. Falls through
    to the original string for values not in the map (so prices, ticket
    numbers, and free-text reasons pass through cleanly)."""
    if value is None:
        return "—"
    s = str(value).strip()
    if not s:
        return "—"
    upper = s.upper()
    if upper in _CS_VALUE_MAP:
        return _CS_VALUE_MAP[upper]
    return s

_EXEC_CS_MAP: Dict[str, str] = {
    "Bull": "𝒟_Bull", "Bear": "𝒟_Bear", "Whisky": "𝒲_Whisky",
    "Wine": "𝒲_Wine", "Watter": "𝒲_Watter", "Blood": "ℬ_Blood",
    "Hawk": "ℋ_Hawk", "Dove": "𝒟_Dove", "Diamond": "𝒟_Diamond",
    "Ruby": "ℛ_Ruby", "Top": "𝒯_Top", "Bott": "ℬ_Bott",
    "A": "𝒜", "B": "ℬ_Close",
    "ManualOrder": "ℳ_Order", "ManualClose": "ℳ_Close",
    "ManualOpen": "ℳ_Open", "Pending": "𝒫_Pending",
    "Long": "↑_Long", "Short": "↓_Short",
}

def _cs_exec(event: str) -> str:
    """m-6: Translate an execution event to CS notation, with a
    ℰ_<Event> fallback for unknown events (rather than passing raw)."""
    if event is None:
        return "ℰ_Unknown"
    if event in _EXEC_CS_MAP:
        return _EXEC_CS_MAP[event]
    return "ℰ_" + str(event)

_ALERT_CS_MAP: Dict[str, str] = {
    "long": "𝒮_Long",
    "short": "𝒮_Short",
    "sin": "𝒮_sin",
    "sine": "𝒮_sine",
}

def _cs_alert(kind: str) -> str:
    """C-A2: Translate an alert sub-kind to its CS glyph."""
    if kind is None:
        return "𝒮_alert"
    if kind in _ALERT_CS_MAP:
        return _ALERT_CS_MAP[kind]
    return "𝒮_" + str(kind)

def _looks_like_reply_error(desc: str) -> bool:
    if not desc:
        return False
    d = desc.lower()
    if 'reply' in d:
        return True
    if 'replied' in d:
        return True
    if 'message to be replied' in d:
        return True
    if 'reply_to_message_id' in d:
        return True
    if 'reply message not found' in d:
        return True
    if 'message_id_invalid' in d:
        return True
    return False

def _looks_like_parse_error(desc: str) -> bool:
    if not desc:
        return False
    d = desc.lower()
    if 'parse' in d:
        return True
    if 'entities' in d:
        return True
    if 'entity' in d:
        return True
    if 'unsupported start tag' in d:
        return True
    if 'unsupported end tag' in d:
        return True
    if 'unexpected end of' in d:
        return True
    if 'can\'t find end' in d:
        return True
    if 'can\'t parse' in d:
        return True
    if 'markdown' in d:
        return True
    return False

def _looks_like_length_error(desc: str) -> bool:
    if not desc:
        return False
    d = desc.lower()
    if 'too long' in d:
        return True
    if 'message is too long' in d:
        return True
    if 'text is too long' in d:
        return True
    if '4096' in d:
        return True
    return False

# ============================================================================
# CONSTANTS & CONFIGURATION — MQL4 PARITY
# ============================================================================
COMMISSION: Decimal = Decimal('0.0')
STOP_LOSS: Decimal = Decimal('0.0')
TAKE_PROFIT: Decimal = Decimal('0.0')
LOT_SIZE: Decimal = Decimal('0.01')
SLIPPAGE: int = 100
MAX_PERIOD: int = 60
MIN_PERIOD: int = 3
X_PERIOD: int = MAX_PERIOD + 2
Y_START: int = MIN_PERIOD - 2
MIN_HISTORY_WINDOW: int = 52
Memory: int = -1

MAX_MIN_GAP: int = int(os.getenv("MAX_MIN_GAP", "2"))
MIN_PERIOD_FLOOR: int = int(os.getenv("MIN_PERIOD_FLOOR", "3"))
MAX_PERIOD_MIN: int = MIN_PERIOD_FLOOR + MAX_MIN_GAP
MAX_PERIOD_MAX: int = 1000
MIN_PERIOD_MIN: int = MIN_PERIOD_FLOOR
MIN_PERIOD_MAX: int = 1000

# ============================================================================
# : ARC-LENGTH PROJECTION PARAMETERS
# ============================================================================
ARC_PROJECTION_HORIZON: int = int(os.getenv("ARC_PROJECTION_HORIZON", "30"))
ARC_PROJECTION_STEP: int = int(os.getenv("ARC_PROJECTION_STEP", "1"))
_ARC_PROJECTION_DAMPING_RAW: str = os.getenv("ARC_PROJECTION_DAMPING", "0.94").strip()
try:
    ARC_PROJECTION_DAMPING_D: Decimal = Decimal(_ARC_PROJECTION_DAMPING_RAW)
    if not (Decimal('0.0') < ARC_PROJECTION_DAMPING_D < Decimal('1.0')):
        raise ValueError(
            f"ARC_PROJECTION_DAMPING must be in (0, 1); got {_ARC_PROJECTION_DAMPING_RAW!r}"
        )
except Exception as _arc_damp_exc:
    raise RuntimeError(
        f"ARC_PROJECTION_DAMPING could not be parsed as a Decimal in (0, 1): "
        f"{_ARC_PROJECTION_DAMPING_RAW!r} ({_arc_damp_exc})"
    ) from _arc_damp_exc

# ============================================================================
# / C-3: EXACT SYMBOLIC THRESHOLDS + FRACTION SHADOWS
# ============================================================================
F_THRESHOLD: Fraction = Fraction(200, 3)
G_THRESHOLD: Fraction = Fraction(100, 3)
GF_TOLERANCE: Fraction = Fraction(40, 15)

F_THRESHOLD_D: Decimal = F_THRESHOLD.to_decimal()
G_THRESHOLD_D: Decimal = G_THRESHOLD.to_decimal()
GF_TOLERANCE_D: Decimal = GF_TOLERANCE.to_decimal()

F_PLUS_GF_D: Decimal = (F_THRESHOLD + GF_TOLERANCE).to_decimal()
G_MINUS_GF_D: Decimal = (G_THRESHOLD - GF_TOLERANCE).to_decimal()

# : exact PyFraction thresholds used by _cmp_frac() in _M()/_N().
F_PLUS_GF_FRAC: PyFraction = F_THRESHOLD._f + GF_TOLERANCE._f
G_MINUS_GF_FRAC: PyFraction = G_THRESHOLD._f - GF_TOLERANCE._f

F_THRESHOLD_F64: float = float(F_THRESHOLD_D)
G_THRESHOLD_F64: float = float(G_THRESHOLD_D)
GF_TOLERANCE_F64: float = float(GF_TOLERANCE_D)
F_PLUS_GF_F: float = float(F_PLUS_GF_D)
G_MINUS_GF_F: float = float(G_MINUS_GF_D)

# ============================================================================
# : SYMBOL DIGITS TABLE (Point-Size Emulation)
# ============================================================================
_DEFAULT_SYMBOL_DIGITS: Dict[str, int] = {
    "BTC-USD": 2, "ETH-USD": 2,
    "GRAM-USD": 3, "TON-USD": 3,
    "SOL-USD": 3, "LTC-USD": 3, "ETC-USD": 3, "QNT-USD": 3,
    "AAVE-USD": 3, "MKR-USD": 3, "YFI-USD": 3,
    "LINK-USD": 4, "DOT-USD": 4, "AVAX-USD": 4, "UNI-USD": 4,
    "ATOM-USD": 4, "NEAR-USD": 4, "FIL-USD": 4, "ICP-USD": 4,
    "ARB-USD": 4, "OP-USD": 4, "SUI-USD": 4, "APT-USD": 4,
    "INJ-USD": 4, "TIA-USD": 4, "SEI-USD": 4, "RNDR-USD": 4,
    "FET-USD": 4, "GRT-USD": 4, "IMX-USD": 4, "LDO-USD": 4,
    "CRV-USD": 4, "SNX-USD": 4, "COMP-USD": 4, "SUSHI-USD": 4,
    "BAL-USD": 4, "KNC-USD": 4, "ZRX-USD": 4, "BAT-USD": 4,
    "ENJ-USD": 4, "MANA-USD": 4, "SAND-USD": 4, "AXS-USD": 4,
    "GALA-USD": 4, "CHZ-USD": 4, "APE-USD": 4, "GMT-USD": 4,
    "LRC-USD": 4, "STORJ-USD": 4, "ANKR-USD": 4, "CVC-USD": 4,
    "OMG-USD": 4, "REN-USD": 4, "ZIL-USD": 4, "KSM-USD": 4,
    "GLMR-USD": 4, "MOVR-USD": 4, "ASTR-USD": 4, "CFX-USD": 4,
    "MASK-USD": 4, "DYDX-USD": 4, "GMX-USD": 4, "RPL-USD": 4,
    "BLUR-USD": 4, "ENS-USD": 4, "LQTY-USD": 4, "PENDLE-USD": 4,
    "MAGIC-USD": 4, "HIGH-USD": 4, "ID-USD": 4, "ARKM-USD": 4,
    "WLD-USD": 4, "EDU-USD": 4, "HOOK-USD": 4, "JTO-USD": 4,
    "BOME-USD": 4, "ETHFI-USD": 4, "ENA-USD": 4, "W-USD": 4,
    "OMNI-USD": 4, "REZ-USD": 4, "ZK-USD": 4, "STRK-USD": 4,
    "DYM-USD": 4, "ALT-USD": 4, "MANTA-USD": 4, "PIXEL-USD": 4,
    "PORTAL-USD": 4, "AEVO-USD": 4,
    "STX-USD": 4, "MINA-USD": 4, "FLOW-USD": 4, "EGLD-USD": 4,
    "XTZ-USD": 4, "ALGO-USD": 4, "VET-USD": 4, "THETA-USD": 4,
    "FTM-USD": 4, "ONE-USD": 4, "ROSE-USD": 4, "KAVA-USD": 4,
    "CELO-USD": 4, "IOTX-USD": 4, "CKB-USD": 4, "AR-USD": 4,
    "TAO-USD": 4, "1INCH-USD": 4, "OCEAN-USD": 4,
    "MEME-USD": 4, "MOG-USD": 4, "FLOKI-USD": 5,
    "AI-USD": 4, "EIGEN-USD": 4, "MOVE-USD": 4, "ME-USD": 4,
    "PNUT-USD": 4, "ACT-USD": 4, "GOAT-USD": 4, "MOODENG-USD": 4,
    "POPCAT-USD": 4, "NEIRO-USD": 5, "TURBO-USD": 5, "MEW-USD": 5,
    "BRETT-USD": 4, "TOSHI-USD": 5, "DEGEN-USD": 5,
    "CYBER-USD": 4, "RDNT-USD": 4, "MUBI-USD": 4, "BIGTIME-USD": 4,
    "NTRN-USD": 4, "SXP-USD": 4, "TRB-USD": 3, "UMA-USD": 4,
    "API3-USD": 4, "BAND-USD": 4, "CTSI-USD": 4, "NMR-USD": 3,
    "REQ-USD": 4, "POWR-USD": 4, "RLC-USD": 4, "OGN-USD": 4,
    "SNT-USD": 4, "MLN-USD": 3, "KEEP-USD": 4, "TBTC-USD": 5,
    "WAXL-USD": 4, "OSMO-USD": 4, "JUNO-USD": 4, "AKT-USD": 4,
    "SCRT-USD": 4, "DVPN-USD": 5, "IRIS-USD": 4, "CTK-USD": 4,
    "STRAX-USD": 4, "PUNDIX-USD": 4, "FXS-USD": 4, "FRAX-USD": 4,
    "CFG-USD": 4, "POLYX-USD": 4, "NODL-USD": 4, "ACH-USD": 5,
    "KEY-USD": 5, "DENT-USD": 5, "HOT-USD": 5, "COTI-USD": 4,
    "DUSK-USD": 4, "OXT-USD": 4, "RARI-USD": 4, "SUPER-USD": 4,
    "TRIBE-USD": 4, "TRU-USD": 4, "TVK-USD": 4, "UNFI-USD": 4,
    "VANRY-USD": 4, "VTHO-USD": 5, "WOO-USD": 4, "XAI-USD": 4,
    "XEC-USD": 5, "XNO-USD": 4, "YGG-USD": 4, "ZEN-USD": 3,
    "AMP-USD": 5, "ANT-USD": 4, "ARPA-USD": 4, "AUDIO-USD": 4,
    "BADGER-USD": 3, "BLZ-USD": 4, "BNT-USD": 4, "CELR-USD": 5,
    "CHR-USD": 4, "COCOS-USD": 5, "CQT-USD": 4, "CTXC-USD": 4,
    "DATA-USD": 5, "DCR-USD": 3, "DIA-USD": 4, "DOCK-USD": 5,
    "DODO-USD": 4, "DREP-USD": 5, "ELF-USD": 4, "ENG-USD": 4,
    "FIDA-USD": 4, "FLM-USD": 4, "FORTH-USD": 3, "FRONT-USD": 4,
    "FTT-USD": 4, "GAS-USD": 3, "GLM-USD": 4, "HIVE-USD": 4,
    "ICX-USD": 4, "ILV-USD": 3, "IOST-USD": 5, "JASMY-USD": 5,
    "LIT-USD": 4, "LOOM-USD": 4, "LPT-USD": 3, "LSK-USD": 4,
    "MBOX-USD": 4, "NKN-USD": 4, "OG-USD": 3, "ONT-USD": 4,
    "PAXG-USD": 2, "PERP-USD": 4, "POLS-USD": 4, "POLY-USD": 5,
    "POND-USD": 4, "PROM-USD": 3, "QKC-USD": 5, "RAD-USD": 3,
    "RARE-USD": 4, "REP-USD": 3, "RIF-USD": 5, "RSR-USD": 5,
    "RUNE-USD": 3, "SFP-USD": 4, "SKL-USD": 4, "SLP-USD": 5,
    "SRM-USD": 4, "STMX-USD": 5, "TFUEL-USD": 5, "TWT-USD": 4,
    "WAN-USD": 4, "WNXM-USD": 3, "WRX-USD": 4, "XEM-USD": 4,
    "XVG-USD": 5, "XVS-USD": 3, "YFII-USD": 2,
    "XRP-USD": 5, "ADA-USD": 5, "DOGE-USD": 5, "MATIC-USD": 5,
    "XLM-USD": 5, "HBAR-USD": 5,
    "JUP-USD": 5, "PYTH-USD": 5,
    "PEPE-USD": 6, "SHIB-USD": 6, "WIF-USD": 6, "BONK-USD": 6,
    "USDT-USD": 4, "USDC-USD": 4, "DAI-USD": 4,
    "BNB-USD": 2, "OKB-USD": 3, "HT-USD": 3, "KCS-USD": 3,
    "BCH-USD": 2, "XMR-USD": 2, "DASH-USD": 3,
    "ZEC-USD": 3, "EOS-USD": 4, "TRX-USD": 5, "NEO-USD": 3,
    "IOTA-USD": 4, "QTUM-USD": 3, "DGB-USD": 5,
    "SC-USD": 5, "RVN-USD": 5, "KAS-USD": 5,
    "GC=F": 2, "CL=F": 2, "ZS=F": 2, "ZM=F": 2, "ZW=F": 2, "KE=F": 2,
    "HG=F": 2, "PL=F": 2, "PA=F": 2, "RB=F": 2, "HO=F": 2, "CC=F": 2,
    "KC=F": 2, "SB=F": 2, "CT=F": 2, "LH=F": 2, "LE=F": 2, "GF=F": 2,
    "ZO=F": 2, "ZR=F": 2, "ZL=F": 2, "ES=F": 2, "NQ=F": 2, "YM=F": 2,
    "RTY=F": 2, "ZB=F": 3, "ZN=F": 4, "ZF=F": 4, "ZT=F": 4, "ZQ=F": 4,
    "GE=F": 4, "SR3=F": 4, "TN=F": 4, "BZ=F": 2, "QM=F": 2, "QA=F": 2,
    "ZC=F": 2, "ZP=F": 2, "OJ=F": 2, "LBS=F": 2, "HE=F": 2, "ALI=F": 2,
    "NKD=F": 2, "VX=F": 2, "MES=F": 2, "MNQ=F": 2, "MYM=F": 2, "M2K=F": 2,
    "BTC=F": 2, "ETH=F": 2, "MBT=F": 2, "MET=F": 2,
    "DX=F": 3, "6E=F": 5, "6J=F": 5, "6B=F": 5, "6A=F": 5, "6C=F": 5,
    "6S=F": 5, "6N=F": 5, "6M=F": 5, "6Z=F": 5,
    "AD=F": 4, "CD=F": 4, "NE=F": 4, "SS=F": 4, "NI=F": 4, "PB=F": 4,
    "SN=F": 4,
    "EURUSD=X": 5, "GBPUSD=X": 5, "USDJPY=X": 3, "USDCHF=X": 5,
    "USDCAD=X": 5, "AUDUSD=X": 5, "NZDUSD=X": 5, "EURGBP=X": 5,
    "EURJPY=X": 3, "EURCHF=X": 5, "EURCAD=X": 5, "EURAUD=X": 5,
    "EURNZD=X": 5, "GBPJPY=X": 3, "GBPCHF=X": 5, "GBPCAD=X": 5,
    "GBPAUD=X": 5, "GBPNZD=X": 5, "AUDJPY=X": 3, "AUDCHF=X": 5,
    "AUDCAD=X": 5, "AUDNZD=X": 5, "NZDJPY=X": 3, "NZDCHF=X": 5,
    "NZDCAD=X": 5, "CADJPY=X": 3, "CADCHF=X": 5, "CHFJPY=X": 3,
    "USDSEK=X": 4, "USDNOK=X": 4, "USDDKK=X": 4, "USDPLN=X": 4,
    "USDHUF=X": 2, "USDCZK=X": 4, "USDTRY=X": 4, "USDMXN=X": 4,
    "USDZAR=X": 4, "USDSGD=X": 4, "USDHKD=X": 4, "USDCNH=X": 4,
    "USDINR=X": 4, "USDKRW=X": 2, "USDTWD=X": 3, "USDTHB=X": 3,
    "USDMYR=X": 4, "USDPHP=X": 3, "USDIDR=X": 1, "USDBRL=X": 4,
    "USDARS=X": 4, "USDCLP=X": 2,
    "^GSPC": 2, "^DJI": 2, "^IXIC": 2, "^RUT": 2, "^VIX": 2,
    "^FTSE": 2, "^GDAXI": 2, "^FCHI": 2, "^STOXX50E": 2,
    "^N225": 2, "^HSI": 2, "^KS11": 2, "^AXJO": 2, "^BSESN": 2,
    "^BVSP": 2, "^MXX": 2, "^TWII": 2, "^STI": 2,
}

def _load_symbol_digits() -> Dict[str, int]:
    raw = os.getenv("SYMBOL_DIGITS", "").strip()
    if not raw:
        return dict(_DEFAULT_SYMBOL_DIGITS)
    try:
        parsed = json.loads(raw)
        if isinstance(parsed, dict):
            out = dict(_DEFAULT_SYMBOL_DIGITS)
            for k, v in parsed.items():
                if isinstance(k, str) and isinstance(v, int) and v >= 0:
                    out[k] = v
            return out
    except Exception:
        pass
    return dict(_DEFAULT_SYMBOL_DIGITS)

SYMBOL_DIGITS: Dict[str, int] = _load_symbol_digits()
SYMBOL_DIGITS_DEFAULT: int = int(os.getenv("SYMBOL_DIGITS_DEFAULT", "2"))

# ============================================================================
# ENVIRONMENT
# ============================================================================
TELEGRAM_WEBAPP_URL: str = os.getenv("TELEGRAM_WEBAPP_URL", "").strip()
BRIDGE_HOST: str = os.getenv("BRIDGE_HOST", "0.0.0.0").strip()
BRIDGE_PORT: int = int(os.getenv("PORT", os.getenv("BRIDGE_PORT", "8765")))
BRIDGE_USE_TLS: bool = os.getenv("BRIDGE_USE_TLS", "0").strip() in ("1", "true", "yes")
BRIDGE_TLS_CERT: str = os.getenv("BRIDGE_TLS_CERT", "").strip()
BRIDGE_TLS_KEY: str = os.getenv("BRIDGE_TLS_KEY", "").strip()
BRIDGE_TUNNEL: str = os.getenv("BRIDGE_TUNNEL", "cloudflared").strip().lower()
BRIDGE_PUBLIC_TIMEOUT: int = int(os.getenv("BRIDGE_PUBLIC_TIMEOUT", "45"))
TELEGRAM_BOT_TOKEN_ENV: str = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
REQUIRE_AUTH: bool = os.getenv("REQUIRE_AUTH", "1").strip() in ("1", "true", "yes")
LOG_BUFFER_SIZE: int = int(os.getenv("LOG_BUFFER_SIZE", "1000"))
TOAST_BUFFER_SIZE: int = int(os.getenv("TOAST_BUFFER_SIZE", "500"))

PUSH_ON_SIGNAL: bool = os.getenv("PUSH_ON_SIGNAL", "1").strip() in ("1", "true", "yes")
PUSH_ON_EXECUTION: bool = os.getenv("PUSH_ON_EXECUTION", "1").strip() in ("1", "true", "yes")
PUSH_ON_FVG: bool = os.getenv("PUSH_ON_FVG", "1").strip() in ("1", "true", "yes")
PUSH_ON_CLOSE: bool = os.getenv("PUSH_ON_CLOSE", "1").strip() in ("1", "true", "yes")
PUSH_DEDUP_WINDOW_MS: int = int(os.getenv("PUSH_DEDUP_WINDOW_MS", "800"))

RELAY_URL: str = os.getenv("RELAY_URL", "").strip().rstrip("/")
RELAY_KEY: str = os.getenv("RELAY_KEY", "").strip()
RELAY_TIMEOUT: int = int(os.getenv("RELAY_TIMEOUT", "10"))
RELAY_MAX_RETRIES: int = int(os.getenv("RELAY_MAX_RETRIES", "3"))

CORS_ORIGIN: str = os.getenv("CORS_ORIGIN", "*").strip()
SYMBOL: str = os.getenv("SYMBOL", "BTC-USD").strip() or "BTC-USD"
INTERVAL: str = "1m"
UPDATE_INTERVAL: int = int(os.getenv("UPDATE_INTERVAL", "30"))
# ============================================================================
# PRIVATE BOT GATE — ENV-CONTROLLED ALLOWLIST (Heroku var: ALLOWED_IDS)
# ============================================================================
# Only the user IDs in ALLOWED_IDS may interact with the bot (Telegram
# commands, callback buttons, Mini App initData, and every non-/health
# bridge endpoint).
#
# Heroku control:
#   heroku config:set ALLOWED_IDS="8769538718,123456789" -a your-app-name  -> private
#   heroku config:set ALLOWED_IDS="" -a your-app-name                      -> open to all
#   heroku config:unset ALLOWED_IDS -a your-app-name                       -> open to all (same as blank)
#
# Format: comma, space, or semicolon separated ints. Blank/unset = open bot.
# Legacy env var ALLOWED_USER_IDS is still read as fallback.
#
# This gate is enforced in three places:
#   1. _track_inbound_message() — every Telegram update passes through
#      here before any handler runs. A disallowed user is silently
#      dropped (no reply, no log line visible to them).
#   2. _require_auth() — every non-/health HTTP bridge endpoint. A
#      disallowed initData user receives HTTP 401.
#   3. _require_auth() on the /handshake path — a disallowed user
#      receives HTTP 403 instead of a session binding.
# ============================================================================
def _load_allowed_ids_from_env() -> set:
    # Primary var requested: ALLOWED_IDS
    raw = os.getenv("ALLOWED_IDS", "")
    # Fallback: support ALLOWED_USER_IDS as env var for legacy deploys
    if not raw.strip():
        raw = os.getenv("ALLOWED_USER_IDS", "")
    raw = raw.strip()
    if not raw:
        # Blank / unset = open bot to all (what you asked for)
        return set()
    ids: set = set()
    # Split on comma, semicolon, or whitespace
    for part in _re_bridge.split(r'[\s,;]+', raw):
        part = part.strip()
        if not part:
            continue
        try:
            ids.add(int(part))
        except ValueError:
            # Ignore non-numeric junk
            continue
    return ids

ALLOWED_USER_IDS: set = _load_allowed_ids_from_env()

# Optional: log what mode we are in at startup (visible in heroku logs --tail)
# This does not log the IDs themselves if you want more privacy, just count.
# Comment out if you prefer silent.
try:
    if ALLOWED_USER_IDS:
        logging.getLogger(__name__).info(f"🔐 Private bot gate ACTIVE — {len(ALLOWED_USER_IDS)} ID(s) allowed (from ALLOWED_IDS env)")
    else:
        logging.getLogger(__name__).info("🔓 Private bot gate OPEN — ALLOWED_IDS blank/unset, bot open to all")
except Exception:
    pass

def _is_allowed_user(user_id) -> bool:
    """Return True if user_id is allowed to interact with the bot.
    Empty ALLOWED_USER_IDS means the gate is open (legacy behavior + blank ALLOWED_IDS)."""
    if not ALLOWED_USER_IDS:
        return True
    try:
        return int(user_id) in ALLOWED_USER_IDS
    except (TypeError, ValueError):
        return False

# ============================================================================
# BAN LIST — ENV-CONTROLLED DENYLIST (Heroku var: BANNED_IDS)
# ============================================================================
# User IDs in BANNED_IDS are blocked everywhere, even if they are also
# in ALLOWED_IDS. Ban wins over allowlist.
#
# Heroku control:
#   heroku config:set BANNED_IDS="111111111,222222222" -a your-app-name  -> ban those users
#   heroku config:set BANNED_IDS="" -a your-app-name                      -> no bans
#   heroku config:unset BANNED_IDS -a your-app-name                       -> no bans (same as blank)
#
# Format: comma, space, or semicolon separated ints. Blank/unset = no bans.
# Legacy env var BANNED_USER_IDS is still read as fallback.
#
# This gate is enforced in four places (ban checked before allowlist):
#   1. _track_inbound_message() — every Telegram update (commands,
#      group mentions, private chats). A banned user is silently
#      dropped (no reply, no log line visible to them).
#   2. button_handler() — callback buttons. A banned user gets a
#      "Banned." alert (the same shape as the existing "Unauthorized."
#      alert, needed to dismiss the button spinner).
#   3. _require_auth() — every non-/health HTTP bridge endpoint.
#      A banned initData user receives HTTP 401.
#   4. _require_auth() on the /handshake path — a banned user
#      receives HTTP 403 instead of a session binding.
# A restart / redeploy is required for a BANNED_IDS change to take effect.
# ============================================================================
def _load_banned_ids_from_env() -> set:
    # Primary var: BANNED_IDS
    raw = os.getenv("BANNED_IDS", "")
    # Fallback: support BANNED_USER_IDS as env var for legacy deploys
    if not raw.strip():
        raw = os.getenv("BANNED_USER_IDS", "")
    raw = raw.strip()
    if not raw:
        # Blank / unset = no bans
        return set()
    ids: set = set()
    # Split on comma, semicolon, or whitespace (same format as ALLOWED_IDS)
    for part in _re_bridge.split(r'[\s,;]+', raw):
        part = part.strip()
        if not part:
            continue
        try:
            ids.add(int(part))
        except ValueError:
            # Ignore non-numeric junk
            continue
    return ids

BANNED_USER_IDS: set = _load_banned_ids_from_env()

# Log what mode we are in at startup (count only, not the IDs themselves).
try:
    if BANNED_USER_IDS:
        logging.getLogger(__name__).info(f"🚫 Ban list ACTIVE — {len(BANNED_USER_IDS)} ID(s) banned (from BANNED_IDS env) — ban wins over allowlist")
    else:
        logging.getLogger(__name__).info("🚫 Ban list EMPTY — BANNED_IDS blank/unset, no users banned")
except Exception:
    pass

def _is_banned_user(user_id) -> bool:
    """Return True if user_id is on the BANNED_IDS denylist."""
    if not BANNED_USER_IDS:
        return False
    try:
        return int(user_id) in BANNED_USER_IDS
    except (TypeError, ValueError):
        return False

# ============================================================================
# SYMBOL MAP — EXPANDED UNIVERSE
# ============================================================================
SYMBOL_MAP = {
    "BTC-USD": "BTC-USD", "ETH-USD": "ETH-USD", "XRP-USD": "XRP-USD",
    "ADA-USD": "ADA-USD", "SOL-USD": "SOL-USD", "DOGE-USD": "DOGE-USD",
    "LTC-USD": "LTC-USD", "LINK-USD": "LINK-USD", "DOT-USD": "DOT-USD",
    "AVAX-USD": "AVAX-USD", "MATIC-USD": "MATIC-USD", "UNI-USD": "UNI-USD",
    "ATOM-USD": "ATOM-USD", "NEAR-USD": "NEAR-USD", "FIL-USD": "FIL-USD",
    "ETC-USD": "ETC-USD", "ICP-USD": "ICP-USD", "XLM-USD": "XLM-USD",
    "HBAR-USD": "HBAR-USD", "QNT-USD": "QNT-USD",
    "GRAM-USD": "GRAM-USD", "TON-USD": "TON-USD",
    "ARB-USD": "ARB-USD", "OP-USD": "OP-USD", "SUI-USD": "SUI-USD",
    "APT-USD": "APT-USD", "INJ-USD": "INJ-USD", "TIA-USD": "TIA-USD",
    "SEI-USD": "SEI-USD", "STX-USD": "STX-USD", "IMX-USD": "IMX-USD",
    "MINA-USD": "MINA-USD", "FLOW-USD": "FLOW-USD", "EGLD-USD": "EGLD-USD",
    "XTZ-USD": "XTZ-USD", "ALGO-USD": "ALGO-USD", "VET-USD": "VET-USD",
    "THETA-USD": "THETA-USD", "FTM-USD": "FTM-USD", "ONE-USD": "ONE-USD",
    "ZIL-USD": "ZIL-USD", "KSM-USD": "KSM-USD", "GLMR-USD": "GLMR-USD",
    "MOVR-USD": "MOVR-USD", "ASTR-USD": "ASTR-USD", "CFX-USD": "CFX-USD",
    "ROSE-USD": "ROSE-USD", "KAVA-USD": "KAVA-USD", "CELO-USD": "CELO-USD",
    "IOTX-USD": "IOTX-USD", "CKB-USD": "CKB-USD", "AR-USD": "AR-USD",
    "DYM-USD": "DYM-USD", "ALT-USD": "ALT-USD", "MANTA-USD": "MANTA-USD",
    "ZK-USD": "ZK-USD", "STRK-USD": "STRK-USD", "BLUR-USD": "BLUR-USD",
    "AAVE-USD": "AAVE-USD", "MKR-USD": "MKR-USD", "COMP-USD": "COMP-USD",
    "CRV-USD": "CRV-USD", "SNX-USD": "SNX-USD", "SUSHI-USD": "SUSHI-USD",
    "YFI-USD": "YFI-USD", "BAL-USD": "BAL-USD", "KNC-USD": "KNC-USD",
    "ZRX-USD": "ZRX-USD", "BAT-USD": "BAT-USD", "ENJ-USD": "ENJ-USD",
    "MANA-USD": "MANA-USD", "SAND-USD": "SAND-USD", "AXS-USD": "AXS-USD",
    "GALA-USD": "GALA-USD", "CHZ-USD": "CHZ-USD", "APE-USD": "APE-USD",
    "GMT-USD": "GMT-USD", "LRC-USD": "LRC-USD", "STORJ-USD": "STORJ-USD",
    "ANKR-USD": "ANKR-USD", "CVC-USD": "CVC-USD", "OMG-USD": "OMG-USD",
    "REN-USD": "REN-USD", "LDO-USD": "LDO-USD", "RPL-USD": "RPL-USD",
    "GMX-USD": "GMX-USD", "DYDX-USD": "DYDX-USD", "PENDLE-USD": "PENDLE-USD",
    "LQTY-USD": "LQTY-USD", "ENS-USD": "ENS-USD", "1INCH-USD": "1INCH-USD",
    "FET-USD": "FET-USD", "GRT-USD": "GRT-USD",
    "PEPE-USD": "PEPE-USD", "SHIB-USD": "SHIB-USD", "WIF-USD": "WIF-USD",
    "BONK-USD": "BONK-USD", "FLOKI-USD": "FLOKI-USD",
    "BOME-USD": "BOME-USD", "MOG-USD": "MOG-USD",
    "JUP-USD": "JUP-USD", "PYTH-USD": "PYTH-USD", "JTO-USD": "JTO-USD",
    "RNDR-USD": "RNDR-USD",
    "WLD-USD": "WLD-USD", "ARKM-USD": "ARKM-USD", "AI-USD": "AI-USD",
    "TAO-USD": "TAO-USD",
    "BCH-USD": "BCH-USD", "XMR-USD": "XMR-USD",
    "DASH-USD": "DASH-USD", "ZEC-USD": "ZEC-USD", "EOS-USD": "EOS-USD",
    "TRX-USD": "TRX-USD", "NEO-USD": "NEO-USD",
    "IOTA-USD": "IOTA-USD", "QTUM-USD": "QTUM-USD", "DGB-USD": "DGB-USD",
    "SC-USD": "SC-USD", "RVN-USD": "RVN-USD", "KAS-USD": "KAS-USD",
    "USDT-USD": "USDT-USD", "USDC-USD": "USDC-USD", "DAI-USD": "DAI-USD",
    "BNB-USD": "BNB-USD", "OKB-USD": "OKB-USD", "HT-USD": "HT-USD",
    "KCS-USD": "KCS-USD",
    "W-USD": "W-USD", "OMNI-USD": "OMNI-USD", "REZ-USD": "REZ-USD",
    "ETHFI-USD": "ETHFI-USD", "ENA-USD": "ENA-USD", "EIGEN-USD": "EIGEN-USD",
    "MOVE-USD": "MOVE-USD", "ME-USD": "ME-USD", "PNUT-USD": "PNUT-USD",
    "ACT-USD": "ACT-USD", "GOAT-USD": "GOAT-USD", "MOODENG-USD": "MOODENG-USD",
    "POPCAT-USD": "POPCAT-USD", "NEIRO-USD": "NEIRO-USD", "TURBO-USD": "TURBO-USD",
    "MEW-USD": "MEW-USD", "BRETT-USD": "BRETT-USD", "TOSHI-USD": "TOSHI-USD",
    "DEGEN-USD": "DEGEN-USD", "HIGH-USD": "HIGH-USD", "ID-USD": "ID-USD",
    "EDU-USD": "EDU-USD", "HOOK-USD": "HOOK-USD", "MAGIC-USD": "MAGIC-USD",
    "PIXEL-USD": "PIXEL-USD", "PORTAL-USD": "PORTAL-USD", "AEVO-USD": "AEVO-USD",
    "MASK-USD": "MASK-USD", "CYBER-USD": "CYBER-USD", "RDNT-USD": "RDNT-USD",
    "MUBI-USD": "MUBI-USD", "BIGTIME-USD": "BIGTIME-USD", "NTRN-USD": "NTRN-USD",
    "SXP-USD": "SXP-USD", "TRB-USD": "TRB-USD", "UMA-USD": "UMA-USD",
    "API3-USD": "API3-USD", "BAND-USD": "BAND-USD", "CTSI-USD": "CTSI-USD",
    "NMR-USD": "NMR-USD", "REQ-USD": "REQ-USD", "POWR-USD": "POWR-USD",
    "RLC-USD": "RLC-USD", "OGN-USD": "OGN-USD", "SNT-USD": "SNT-USD",
    "MLN-USD": "MLN-USD", "KEEP-USD": "KEEP-USD", "TBTC-USD": "TBTC-USD",
    "WAXL-USD": "WAXL-USD", "OSMO-USD": "OSMO-USD", "JUNO-USD": "JUNO-USD",
    "AKT-USD": "AKT-USD", "SCRT-USD": "SCRT-USD", "DVPN-USD": "DVPN-USD",
    "IRIS-USD": "IRIS-USD", "CTK-USD": "CTK-USD", "STRAX-USD": "STRAX-USD",
    "PUNDIX-USD": "PUNDIX-USD", "FXS-USD": "FXS-USD", "FRAX-USD": "FRAX-USD",
    "CFG-USD": "CFG-USD", "POLYX-USD": "POLYX-USD", "NODL-USD": "NODL-USD",
    "ACH-USD": "ACH-USD", "KEY-USD": "KEY-USD", "DENT-USD": "DENT-USD",
    "HOT-USD": "HOT-USD", "COTI-USD": "COTI-USD", "DUSK-USD": "DUSK-USD",
    "OXT-USD": "OXT-USD", "RARI-USD": "RARI-USD", "SUPER-USD": "SUPER-USD",
    "TRIBE-USD": "TRIBE-USD", "TRU-USD": "TRU-USD", "TVK-USD": "TVK-USD",
    "UNFI-USD": "UNFI-USD", "VANRY-USD": "VANRY-USD", "VTHO-USD": "VTHO-USD",
    "WOO-USD": "WOO-USD", "XAI-USD": "XAI-USD", "XEC-USD": "XEC-USD",
    "XNO-USD": "XNO-USD", "YGG-USD": "YGG-USD", "ZEN-USD": "ZEN-USD",
    "AMP-USD": "AMP-USD", "ANT-USD": "ANT-USD", "ARPA-USD": "ARPA-USD",
    "AUDIO-USD": "AUDIO-USD", "BADGER-USD": "BADGER-USD", "BLZ-USD": "BLZ-USD",
    "BNT-USD": "BNT-USD", "CELR-USD": "CELR-USD", "CHR-USD": "CHR-USD",
    "COCOS-USD": "COCOS-USD", "CQT-USD": "CQT-USD", "CTXC-USD": "CTXC-USD",
    "DATA-USD": "DATA-USD", "DCR-USD": "DCR-USD", "DIA-USD": "DIA-USD",
    "DOCK-USD": "DOCK-USD", "DODO-USD": "DODO-USD", "DREP-USD": "DREP-USD",
    "ELF-USD": "ELF-USD", "ENG-USD": "ENG-USD", "FIDA-USD": "FIDA-USD",
    "FLM-USD": "FLM-USD", "FORTH-USD": "FORTH-USD", "FRONT-USD": "FRONT-USD",
    "FTT-USD": "FTT-USD", "GAS-USD": "GAS-USD", "GLM-USD": "GLM-USD",
    "HIVE-USD": "HIVE-USD", "ICX-USD": "ICX-USD", "ILV-USD": "ILV-USD",
    "IOST-USD": "IOST-USD", "JASMY-USD": "JASMY-USD", "LIT-USD": "LIT-USD",
    "LOOM-USD": "LOOM-USD", "LPT-USD": "LPT-USD", "MBOX-USD": "MBOX-USD",
    "NKN-USD": "NKN-USD", "OG-USD": "OG-USD", "ONT-USD": "ONT-USD",
    "PAXG-USD": "PAXG-USD", "PERP-USD": "PERP-USD", "POLS-USD": "POLS-USD",
    "POLY-USD": "POLY-USD", "POND-USD": "POND-USD", "PROM-USD": "PROM-USD",
    "QKC-USD": "QKC-USD", "RAD-USD": "RAD-USD", "RARE-USD": "RARE-USD",
    "REP-USD": "REP-USD", "RIF-USD": "RIF-USD", "RSR-USD": "RSR-USD",
    "RUNE-USD": "RUNE-USD", "SFP-USD": "SFP-USD", "SKL-USD": "SKL-USD",
    "SLP-USD": "SLP-USD", "SRM-USD": "SRM-USD", "STMX-USD": "STMX-USD",
    "TFUEL-USD": "TFUEL-USD", "TWT-USD": "TWT-USD", "WAN-USD": "WAN-USD",
    "WNXM-USD": "WNXM-USD", "WRX-USD": "WRX-USD", "XEM-USD": "XEM-USD",
    "XVG-USD": "XVG-USD", "XVS-USD": "XVS-USD", "YFII-USD": "YFII-USD",
    "BTCUSDT": "BTC-USD", "ETHUSDT": "ETH-USD", "XRPUSDT": "XRP-USD",
    "ADAUSDT": "ADA-USD", "SOLUSDT": "SOL-USD", "DOGEUSDT": "DOGE-USD",
    "LTCUSDT": "LTC-USD", "LINKUSDT": "LINK-USD", "DOTUSDT": "DOT-USD",
    "AVAXUSDT": "AVAX-USD", "MATICUSDT": "MATIC-USD", "UNIUSDT": "UNI-USD",
    "ATOMUSDT": "ATOM-USD", "NEARUSDT": "NEAR-USD", "FILUSDT": "FIL-USD",
    "ETCUSDT": "ETC-USD", "ICPUSDT": "ICP-USD", "XLMUSDT": "XLM-USD",
    "HBARUSDT": "HBAR-USD", "QNTUSDT": "QNT-USD",
    "TONUSDT": "GRAM-USD", "GRAMUSDT": "GRAM-USD",
    "ARBUSDT": "ARB-USD", "OPUSDT": "OP-USD", "SUIUSDT": "SUI-USD",
    "APTUSDT": "APT-USD", "INJUSDT": "INJ-USD", "TIAUSDT": "TIA-USD",
    "SEIUSDT": "SEI-USD", "STXUSDT": "STX-USD",
    "PEPEUSDT": "PEPE-USD", "SHIBUSDT": "SHIB-USD", "WIFUSDT": "WIF-USD",
    "BONKUSDT": "BONK-USD", "FLOKIUSDT": "FLOKI-USD",
    "JUPUSDT": "JUP-USD", "PYTHUSDT": "PYTH-USD", "JTOUSDT": "JTO-USD",
    "RNDRUSDT": "RNDR-USD", "FETUSDT": "FET-USD", "GRTUSDT": "GRT-USD",
    "IMXUSDT": "IMX-USD", "LDOUSDT": "LDO-USD", "CRVUSDT": "CRV-USD",
    "SNXUSDT": "SNX-USD", "COMPUSDT": "COMP-USD", "MKRUSDT": "MKR-USD",
    "AAVEUSDT": "AAVE-USD", "SUSHIUSDT": "SUSHI-USD", "YFIUSDT": "YFI-USD",
    "BALUSDT": "BAL-USD", "KNCUSDT": "KNC-USD", "ZRXUSDT": "ZRX-USD",
    "BATUSDT": "BAT-USD", "ENJUSDT": "ENJ-USD", "MANAUSDT": "MANA-USD",
    "SANDUSDT": "SAND-USD", "AXSUSDT": "AXS-USD", "GALAUSDT": "GALA-USD",
    "CHZUSDT": "CHZ-USD", "APEUSDT": "APE-USD", "GMTUSDT": "GMT-USD",
    "LRCUSDT": "LRC-USD", "STORJUSDT": "STORJ-USD", "ANKRUSDT": "ANKR-USD",
    "CVCUSDT": "CVC-USD", "OMGUSDT": "OMG-USD", "RENUSDT": "REN-USD",
    "ZILUSDT": "ZIL-USD", "KSMUSDT": "KSM-USD", "GLMRUSDT": "GLMR-USD",
    "MOVRUSDT": "MOVR-USD", "ASTRUSDT": "ASTR-USD", "CFXUSDT": "CFX-USD",
    "MASKUSDT": "MASK-USD", "DYDXUSDT": "DYDX-USD", "GMXUSDT": "GMX-USD",
    "RPLUSDT": "RPL-USD", "BLURUSDT": "BLUR-USD", "ENSUSDT": "ENS-USD",
    "LQTYUSDT": "LQTY-USD", "PENDLEUSDT": "PENDLE-USD",
    "MAGICUSDT": "MAGIC-USD", "HIGHUSDT": "HIGH-USD", "IDUSDT": "ID-USD",
    "ARKMUSDT": "ARKM-USD", "WLDUSDT": "WLD-USD", "EDUUSDT": "EDU-USD",
    "HOOKUSDT": "HOOK-USD", "BOMEUSDT": "BOME-USD", "ETHFIUSDT": "ETHFI-USD",
    "ENAUSDT": "ENA-USD", "WUSDT": "W-USD", "OMNIUSDT": "OMNI-USD",
    "REZUSDT": "REZ-USD", "ZKUSDT": "ZK-USD", "STRKUSDT": "STRK-USD",
    "DYMUSDT": "DYM-USD", "ALTUSDT": "ALT-USD", "MANTAUSDT": "MANTA-USD",
    "PIXELUSDT": "PIXEL-USD", "PORTALUSDT": "PORTAL-USD", "AEVOUSDT": "AEVO-USD",
    "GC=F": "GC=F", "SI=F": "SI=F", "CL=F": "CL=F", "NG=F": "NG=F",
    "ZB=F": "ZB=F", "ZN=F": "ZN=F", "ZS=F": "ZS=F", "ZM=F": "ZM=F",
    "ZW=F": "ZW=F", "KE=F": "KE=F", "HG=F": "HG=F", "PL=F": "PL=F",
    "PA=F": "PA=F", "RB=F": "RB=F", "HO=F": "HO=F", "CC=F": "CC=F",
    "KC=F": "KC=F", "SB=F": "SB=F", "CT=F": "CT=F", "LH=F": "LH=F",
    "LE=F": "LE=F", "GF=F": "GF=F", "ZO=F": "ZO=F", "ZR=F": "ZR=F",
    "ZL=F": "ZL=F", "ES=F": "ES=F", "NQ=F": "NQ=F", "YM=F": "YM=F",
    "RTY=F": "RTY=F",
    "ALI=F": "ALI=F", "BZ=F": "BZ=F", "QM=F": "QM=F", "QA=F": "QA=F",
    "ZC=F": "ZC=F", "ZP=F": "ZP=F", "OJ=F": "OJ=F", "LBS=F": "LBS=F",
    "HE=F": "HE=F", "ZF=F": "ZF=F", "ZT=F": "ZT=F", "ZQ=F": "ZQ=F",
    "GE=F": "GE=F", "SR3=F": "SR3=F", "TN=F": "TN=F", "NKD=F": "NKD=F",
    "VX=F": "VX=F", "MES=F": "MES=F", "MNQ=F": "MNQ=F", "MYM=F": "MYM=F",
    "M2K=F": "M2K=F", "BTC=F": "BTC=F", "ETH=F": "ETH=F", "MBT=F": "MBT=F",
    "MET=F": "MET=F", "DX=F": "DX=F", "6E=F": "6E=F", "6J=F": "6J=F",
    "6B=F": "6B=F", "6A=F": "6A=F", "6C=F": "6C=F", "6S=F": "6S=F",
    "6N=F": "6N=F", "6M=F": "6M=F", "6Z=F": "6Z=F",
    "AD=F": "AD=F", "CD=F": "CD=F", "NE=F": "NE=F", "SS=F": "SS=F",
    "NI=F": "NI=F", "PB=F": "PB=F", "SN=F": "SN=F",
    "AAPL": "AAPL", "MSFT": "MSFT", "GOOGL": "GOOGL", "GOOG": "GOOG",
    "AMZN": "AMZN", "META": "META", "NVDA": "NVDA", "TSLA": "TSLA",
    "AVGO": "AVGO", "ORCL": "ORCL", "CRM": "CRM", "ADBE": "ADBE",
    "AMD": "AMD", "INTC": "INTC", "CSCO": "CSCO", "QCOM": "QCOM",
    "TXN": "TXN", "MU": "MU", "AMAT": "AMAT", "LRCX": "LRCX",
    "KLAC": "KLAC", "MRVL": "MRVL", "SNPS": "SNPS", "CDNS": "CDNS",
    "INTU": "INTU", "NOW": "NOW", "PANW": "PANW", "CRWD": "CRWD",
    "ZS": "ZS", "DDOG": "DDOG", "SNOW": "SNOW", "PLTR": "PLTR",
    "AI": "AI", "SMCI": "SMCI", "ARM": "ARM", "DELL": "DELL",
    "HPQ": "HPQ", "HPE": "HPE", "WDC": "WDC", "STX": "STX",
    "IBM": "IBM", "ACN": "ACN", "UBER": "UBER", "LYFT": "LYFT",
    "ABNB": "ABNB", "DASH": "DASH", "SHOP": "SHOP", "SQ": "SQ",
    "PYPL": "PYPL", "COIN": "COIN", "HOOD": "HOOD", "SOFI": "SOFI",
    "AFRM": "AFRM", "UPST": "UPST", "LC": "LC",
    "NFLX": "NFLX", "DIS": "DIS", "CMCSA": "CMCSA", "T": "T",
    "VZ": "VZ", "TMUS": "TMUS", "WBD": "WBD", "PARA": "PARA",
    "SPOT": "SPOT", "RBLX": "RBLX", "U": "U", "EA": "EA",
    "TTWO": "TTWO", "ATVI": "ATVI", "NTES": "NTES", "BIDU": "BIDU",
    "JD": "JD", "PDD": "PDD", "BABA": "BABA", "TCEHY": "TCEHY",
    "NTDOY": "NTDOY", "SONY": "SONY",
    "WMT": "WMT", "COST": "COST", "TGT": "TGT", "HD": "HD",
    "LOW": "LOW", "NKE": "NKE", "SBUX": "SBUX", "MCD": "MCD",
    "KO": "KO", "PEP": "PEP", "PG": "PG", "CL": "CL",
    "KMB": "KMB", "GIS": "GIS", "K": "K", "HSY": "HSY",
    "MDLZ": "MDLZ", "STZ": "STZ", "TAP": "TAP", "SAM": "SAM",
    "BUD": "BUD", "DEO": "DEO", "MO": "MO", "PM": "PM",
    "EL": "EL", "ULTA": "ULTA", "ROST": "ROST", "TJX": "TJX",
    "BBY": "BBY", "DG": "DG", "DLTR": "DLTR", "LULU": "LULU",
    "GPS": "GPS", "ANF": "ANF", "M": "M", "KSS": "KSS",
    "JWN": "JWN",
    "JPM": "JPM", "BAC": "BAC", "WFC": "WFC", "C": "C",
    "GS": "GS", "MS": "MS", "BLK": "BLK", "SCHW": "SCHW",
    "AXP": "AXP", "V": "V", "MA": "MA", "USB": "USB",
    "PNC": "PNC", "TFC": "TFC", "COF": "COF", "DFS": "DFS",
    "BK": "BK", "STT": "STT", "NTRS": "NTRS", "FITB": "FITB",
    "HBAN": "HBAN", "RF": "RF", "KEY": "KEY", "CFG": "CFG",
    "BRK-B": "BRK-B", "BRK-A": "BRK-A", "AIG": "AIG", "MET": "MET",
    "PRU": "PRU", "AFL": "AFL", "ALL": "ALL", "TRV": "TRV",
    "PGR": "PGR", "CB": "CB", "MMC": "MMC", "AON": "AON",
    "AJG": "AJG", "WLTW": "WLTW", "BRO": "BRO",
    "JNJ": "JNJ", "PFE": "PFE", "MRK": "MRK", "ABBV": "ABBV",
    "LLY": "LLY", "BMY": "BMY", "AMGN": "AMGN", "GILD": "GILD",
    "BIIB": "BIIB", "REGN": "REGN", "VRTX": "VRTX", "MRNA": "MRNA",
    "BNTX": "BNTX", "AZN": "AZN", "GSK": "GSK", "SNY": "SNY",
    "NVS": "NVS", "UNH": "UNH", "CVS": "CVS", "CI": "CI",
    "HUM": "HUM", "ELV": "ELV", "ANTM": "ANTM", "CNC": "CNC",
    "MOH": "MOH", "HCA": "HCA", "UHS": "UHS", "THC": "THC",
    "MCK": "MCK", "ABC": "ABC", "CAH": "CAH",
    "MDT": "MDT", "SYK": "SYK", "BSX": "BSX", "ZBH": "ZBH",
    "BDX": "BDX", "BAX": "BAX", "ISRG": "ISRG", "EW": "EW",
    "DXCM": "DXCM", "PODD": "PODD", "ILMN": "ILMN", "CRL": "CRL",
    "IQV": "IQV", "A": "A", "WAT": "WAT", "MTD": "MTD",
    "BA": "BA", "CAT": "CAT", "DE": "DE", "HON": "HON",
    "GE": "GE", "MMM": "MMM", "LMT": "LMT", "RTX": "RTX",
    "NOC": "NOC", "GD": "GD", "LHX": "LHX", "HII": "HII",
    "TDG": "TDG", "HWM": "HWM", "TXT": "TXT", "CARR": "CARR",
    "OTIS": "OTIS", "CMI": "CMI", "PCAR": "PCAR", "NAV": "NAV",
    "URI": "URI", "FAST": "FAST", "GWW": "GWW", "ITW": "ITW",
    "EMR": "EMR", "ETN": "ETN", "PH": "PH", "ROK": "ROK",
    "DOV": "DOV", "AME": "AME", "IR": "IR", "XYL": "XYL",
    "UPS": "UPS", "FDX": "FDX", "DAL": "DAL", "UAL": "UAL",
    "AAL": "AAL", "LUV": "LUV", "ALK": "ALK", "JBLU": "JBLU",
    "XOM": "XOM", "CVX": "CVX", "COP": "COP", "EOG": "EOG",
    "PXD": "PXD", "OXY": "OXY", "PSX": "PSX", "VLO": "VLO",
    "MPC": "MPC", "SLB": "SLB", "HAL": "HAL", "BKR": "BKR",
    "NOV": "NOV", "FTI": "FTI", "KMI": "KMI", "WMB": "WMB",
    "OKE": "OKE", "ET": "ET", "EPD": "EPD", "MMP": "MMP",
    "PAA": "PAA", "TRGP": "TRGP", "LNG": "LNG", "EQT": "EQT",
    "RRC": "RRC", "AR": "AR", "CNX": "CNX", "SWN": "SWN",
    "CHK": "CHK", "DVN": "DVN", "FANG": "FANG", "HES": "HES",
    "MRO": "MRO", "APA": "APA", "CTRA": "CTRA",
    "LIN": "LIN", "APD": "APD", "SHW": "SHW", "ECL": "ECL",
    "DD": "DD", "DOW": "DOW", "LYB": "LYB", "PPG": "PPG",
    "NEM": "NEM", "FCX": "FCX", "NUE": "NUE", "STLD": "STLD",
    "CLF": "CLF", "X": "X", "AA": "AA", "MP": "MP",
    "ALB": "ALB", "SQM": "SQM", "LAC": "LAC", "VALE": "VALE",
    "RIO": "RIO", "BHP": "BHP", "MT": "MT", "GOLD": "GOLD",
    "NEE": "NEE", "DUK": "DUK", "SO": "SO", "D": "D",
    "AEP": "AEP", "EXC": "EXC", "XEL": "XEL", "ED": "ED",
    "WEC": "WEC", "ES": "ES", "AWK": "AWK", "SRE": "SRE",
    "PCG": "PCG", "EIX": "EIX", "PEG": "PEG", "FE": "FE",
    "PPL": "PPL", "CMS": "CMS", "DTE": "DTE", "AEE": "AEE",
    "CNP": "CNP", "NI": "NI", "LNT": "LNT", "EVRG": "EVRG",
    "PLD": "PLD", "AMT": "AMT", "CCI": "CCI", "EQIX": "EQIX",
    "DLR": "DLR", "SPG": "SPG", "O": "O", "PSA": "PSA",
    "EXR": "EXR", "AVB": "AVB", "EQR": "EQR", "MAA": "MAA",
    "ESS": "ESS", "UDR": "UDR", "CPT": "CPT", "AIV": "AIV",
    "VTR": "VTR", "WELL": "WELL", "PEAK": "PEAK", "HST": "HST",
    "RHP": "RHP", "IRM": "IRM", "SBAC": "SBAC",
    "SPY": "SPY", "QQQ": "QQQ", "DIA": "DIA", "IWM": "IWM",
    "VTI": "VTI", "VOO": "VOO", "VEA": "VEA", "VWO": "VWO",
    "IVV": "IVV", "VTV": "VTV", "VUG": "VUG", "IWF": "IWF",
    "IWD": "IWD", "IWB": "IWB", "IWV": "IWV", "RSP": "RSP",
    "MDY": "MDY", "IJH": "IJH", "IJR": "IJR", "IJS": "IJS",
    "IJJ": "IJJ", "IJK": "IJK", "IJT": "IJT",
    "XLK": "XLK", "XLF": "XLF", "XLV": "XLV", "XLE": "XLE",
    "XLI": "XLI", "XLP": "XLP", "XLY": "XLY", "XLU": "XLU",
    "XLB": "XLB", "XLRE": "XLRE", "XLC": "XLC", "SMH": "SMH",
    "SOXX": "SOXX", "IGV": "IGV", "VGT": "VGT", "FTEC": "FTEC",
    "VHT": "VHT", "VFH": "VFH", "VIS": "VIS", "VPU": "VPU",
    "VDC": "VDC", "VCR": "VCR", "VAW": "VAW", "VNQ": "VNQ",
    "KRE": "KRE", "KBE": "KBE", "XBI": "XBI", "IBB": "IBB",
    "IHI": "IHI", "IHF": "IHF", "ITA": "ITA", "XAR": "XAR",
    "XOP": "XOP", "OIH": "OIH", "XME": "XME", "GDX": "GDX",
    "GDXJ": "GDXJ", "SIL": "SIL", "URA": "URA", "LIT": "LIT",
    "TAN": "TAN", "ICLN": "ICLN", "PBW": "PBW", "FAN": "FAN",
    "JETS": "JETS", "PEJ": "PEJ", "XRT": "XRT", "ITB": "ITB",
    "XHB": "XHB", "HACK": "HACK", "BOTZ": "BOTZ", "ROBO": "ROBO",
    "ARKK": "ARKK", "ARKG": "ARKG", "ARKW": "ARKW", "ARKF": "ARKF",
    "ARKQ": "ARKQ", "ARKX": "ARKX",
    "EFA": "EFA", "EEM": "EEM", "IEFA": "IEFA", "IEMG": "IEMG",
    "FXI": "FXI", "MCHI": "MCHI", "KWEB": "KWEB", "CQQQ": "CQQQ",
    "EWJ": "EWJ", "EWZ": "EWZ", "EWW": "EWW", "EWY": "EWY",
    "EWT": "EWT", "EWU": "EWU", "EWG": "EWG", "EWQ": "EWQ",
    "EWI": "EWI", "EWP": "EWP", "EWN": "EWN", "EWD": "EWD",
    "EWL": "EWL", "EWC": "EWC", "EWA": "EWA", "EWH": "EWH",
    "EWS": "EWS", "EWM": "EWM", "EPI": "EPI", "INDA": "INDA",
    "SMIN": "SMIN", "EPHE": "EPHE", "EZA": "EZA", "TUR": "TUR",
    "EIS": "EIS", "KSA": "KSA", "UAE": "UAE",
    "IAU": "IAU", "SLV": "SLV", "SIVR": "SIVR", "PPLT": "PPLT",
    "PALL": "PALL", "USO": "USO", "BNO": "BNO", "UNG": "UNG",
    "UNL": "UNL", "DBA": "DBA", "DBC": "DBC", "GSG": "GSG",
    "PDBC": "PDBC", "CPER": "CPER", "COPX": "COPX", "REMX": "REMX",
    "WOOD": "WOOD",
    "TLT": "TLT", "IEF": "IEF", "SHY": "SHY", "AGG": "AGG",
    "BND": "BND", "LQD": "LQD", "HYG": "HYG", "JNK": "JNK",
    "TIP": "TIP", "VTIP": "VTIP", "MUB": "MUB", "EMB": "EMB",
    "BNDX": "BNDX", "IGSB": "IGSB", "IGIB": "IGIB", "SCHO": "SCHO",
    "SCHR": "SCHR", "SCHZ": "SCHZ", "VCIT": "VCIT", "VCSH": "VCSH",
    "BSV": "BSV", "BIV": "BIV", "BLV": "BLV", "GOVT": "GOVT",
    "SPTL": "SPTL", "SPTI": "SPTI", "SPTS": "SPTS",
    "TQQQ": "TQQQ", "SQQQ": "SQQQ", "SPXL": "SPXL", "SPXS": "SPXS",
    "UPRO": "UPRO", "SPXU": "SPXU", "TNA": "TNA", "TZA": "TZA",
    "FAS": "FAS", "FAZ": "FAZ", "LABU": "LABU", "LABD": "LABD",
    "YINN": "YINN", "YANG": "YANG", "SOXL": "SOXL", "SOXS": "SOXS",
    "TECL": "TECL", "TECS": "TECS", "UDOW": "UDOW", "SDOW": "SDOW",
    "SCHD": "SCHD", "VYM": "VYM", "DVY": "DVY", "HDV": "HDV",
    "SPHD": "SPHD", "SDY": "SDY", "VIG": "VIG", "DGRO": "DGRO",
    "NOBL": "NOBL", "QUAL": "QUAL", "MTUM": "MTUM", "VLUE": "VLUE",
    "SIZE": "SIZE", "USMV": "USMV", "SPLV": "SPLV", "SPHQ": "SPHQ",
    "RPG": "RPG", "RPV": "RPV", "EQWL": "EQWL",
    "QCLN": "QCLN", "ACES": "ACES", "DRIV": "DRIV", "IDRV": "IDRV",
    "ESPO": "ESPO", "NERD": "NERD", "HERO": "HERO", "GAMR": "GAMR",
    "BITO": "BITO", "BITQ": "BITQ", "WGMI": "WGMI", "DAPP": "DAPP",
    "BLOK": "BLOK", "LEGR": "LEGR", "MOAT": "MOAT", "SCHG": "SCHG",
    "SCHV": "SCHV", "VONG": "VONG", "VONV": "VONV", "IUSG": "IUSG",
    "IUSV": "IUSV",
    "RIVN": "RIVN", "LCID": "LCID", "NIO": "NIO", "XPEV": "XPEV",
    "LI": "LI", "FSR": "FSR", "GOEV": "GOEV", "PLUG": "PLUG",
    "FCEL": "FCEL", "BLDP": "BLDP", "BE": "BE", "ENPH": "ENPH",
    "SEDG": "SEDG", "RUN": "RUN", "NOVA": "NOVA", "SPWR": "SPWR",
    "CSIQ": "CSIQ", "JKS": "JKS", "DQ": "DQ", "MAXN": "MAXN",
    "ARRY": "ARRY", "MSTR": "MSTR", "MARA": "MARA", "RIOT": "RIOT",
    "HUT": "HUT", "BITF": "BITF", "CLSK": "CLSK", "CIFR": "CIFR",
    "IREN": "IREN", "WULF": "WULF", "CORZ": "CORZ", "BTBT": "BTBT",
    "CAN": "CAN", "EBON": "EBON", "SOS": "SOS",
    "GME": "GME", "AMC": "AMC", "BB": "BB", "NOK": "NOK",
    "KOSS": "KOSS", "EXPR": "EXPR", "BBBY": "BBBY", "CVNA": "CVNA",
    "CHWY": "CHWY", "W": "W", "ETSY": "ETSY", "EBAY": "EBAY",
    "OSTK": "OSTK", "WISH": "WISH", "PTON": "PTON", "ZM": "ZM",
    "DOCU": "DOCU", "TWLO": "TWLO", "OKTA": "OKTA", "NET": "NET",
    "FSLY": "FSLY", "ESTC": "ESTC", "MDB": "MDB", "TEAM": "TEAM",
    "WORK": "WORK", "SPLK": "SPLK", "NEWR": "NEWR", "SUMO": "SUMO",
    "PD": "PD", "APPF": "APPF", "BL": "BL", "ZI": "ZI",
    "MGNI": "MGNI", "TTD": "TTD", "PUBM": "PUBM", "ROKU": "ROKU",
    "FUBO": "FUBO", "ASAN": "ASAN", "MNDY": "MNDY", "HUBS": "HUBS",
    "BILL": "BILL", "TOST": "TOST",
    "EURUSD=X": "EURUSD=X", "GBPUSD=X": "GBPUSD=X", "USDJPY=X": "USDJPY=X",
    "USDCHF=X": "USDCHF=X", "USDCAD=X": "USDCAD=X", "AUDUSD=X": "AUDUSD=X",
    "NZDUSD=X": "NZDUSD=X", "EURGBP=X": "EURGBP=X", "EURJPY=X": "EURJPY=X",
    "EURCHF=X": "EURCHF=X", "EURCAD=X": "EURCAD=X", "EURAUD=X": "EURAUD=X",
    "EURNZD=X": "EURNZD=X", "GBPJPY=X": "GBPJPY=X", "GBPCHF=X": "GBPCHF=X",
    "GBPCAD=X": "GBPCAD=X", "GBPAUD=X": "GBPAUD=X", "GBPNZD=X": "GBPNZD=X",
    "AUDJPY=X": "AUDJPY=X", "AUDCHF=X": "AUDCHF=X", "AUDCAD=X": "AUDCAD=X",
    "AUDNZD=X": "AUDNZD=X", "NZDJPY=X": "NZDJPY=X", "NZDCHF=X": "NZDCHF=X",
    "NZDCAD=X": "NZDCAD=X", "CADJPY=X": "CADJPY=X", "CADCHF=X": "CADCHF=X",
    "CHFJPY=X": "CHFJPY=X", "USDSEK=X": "USDSEK=X", "USDNOK=X": "USDNOK=X",
    "USDDKK=X": "USDDKK=X", "USDPLN=X": "USDPLN=X", "USDHUF=X": "USDHUF=X",
    "USDCZK=X": "USDCZK=X", "USDTRY=X": "USDTRY=X", "USDMXN=X": "USDMXN=X",
    "USDZAR=X": "USDZAR=X", "USDSGD=X": "USDSGD=X", "USDHKD=X": "USDHKD=X",
    "USDCNH=X": "USDCNH=X", "USDINR=X": "USDINR=X", "USDKRW=X": "USDKRW=X",
    "USDTWD=X": "USDTWD=X", "USDTHB=X": "USDTHB=X", "USDMYR=X": "USDMYR=X",
    "USDPHP=X": "USDPHP=X", "USDIDR=X": "USDIDR=X", "USDBRL=X": "USDBRL=X",
    "USDARS=X": "USDARS=X", "USDCLP=X": "USDCLP=X",
    "EURUSD": "EURUSD=X", "GBPUSD": "GBPUSD=X", "USDJPY": "USDJPY=X",
    "USDCHF": "USDCHF=X", "USDCAD": "USDCAD=X", "AUDUSD": "AUDUSD=X",
    "NZDUSD": "NZDUSD=X", "EURGBP": "EURGBP=X", "EURJPY": "EURJPY=X",
    "GBPJPY": "GBPJPY=X", "AUDJPY": "AUDJPY=X", "CADJPY": "CADJPY=X",
    "CHFJPY": "CHFJPY=X", "NZDJPY": "NZDJPY=X",
    "^GSPC": "^GSPC", "^DJI": "^DJI", "^IXIC": "^IXIC", "^RUT": "^RUT",
    "^VIX": "^VIX", "^FTSE": "^FTSE", "^GDAXI": "^GDAXI", "^FCHI": "^FCHI",
    "^STOXX50E": "^STOXX50E", "^N225": "^N225", "^HSI": "^HSI",
    "^KS11": "^KS11", "^AXJO": "^AXJO", "^BSESN": "^BSESN",
    "^BVSP": "^BVSP", "^MXX": "^MXX", "^TWII": "^TWII", "^STI": "^STI",
}

def _crypto_fallback(sym: str) -> List[str]:
    if sym.endswith("-USD"):
        base = sym[:-4]
        return [sym, f"{base}USD=X"]
    return [sym]

SYMBOL_FALLBACKS: Dict[str, List[str]] = {}
for _sym in SYMBOL_MAP:
    if _sym.endswith("-USD") and _sym != "USDT-USD" and _sym != "USDC-USD":
        SYMBOL_FALLBACKS[_sym] = _crypto_fallback(_sym)
    else:
        SYMBOL_FALLBACKS[_sym] = [_sym]

from telegram import (
    Update,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    WebAppInfo,
    MenuButtonWebApp,
)
from telegram.ext import (
    Application,
    CommandHandler,
    CallbackQueryHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# ============================================================================
# LOG RING BUFFER
# ============================================================================
_LOG_BUFFER: deque = deque(maxlen=LOG_BUFFER_SIZE)
_LOG_LOCK = threading.Lock()

# ============================================================================
# TOAST RING BUFFER
# ============================================================================
_TOAST_BUFFER_MAXLEN: int = TOAST_BUFFER_SIZE if TOAST_BUFFER_SIZE > 0 else 1
_TOAST_BUFFER: deque = deque(maxlen=_TOAST_BUFFER_MAXLEN)
_TOAST_LOCK = threading.Lock()
_TOAST_SEQ: int = 0
_TOAST_FIRST_AVAILABLE_SEQ: int = 0

_PUSH_DEDUP_LOCK = threading.Lock()
_PUSH_DEDUP: Dict[str, float] = {}

# ============================================================================
# ENGINE LOCK
# ============================================================================
_ENGINE_LOCK = threading.RLock()

# ============================================================================
# : BOUNDED PUSH DISPATCH QUEUE
# ============================================================================
_PUSH_QUEUE: "queue.Queue[Optional[Tuple[str, Dict[str, Any]]]]" = queue.Queue(maxsize=512)
_PUSH_WORKER_STARTED: bool = False
_PUSH_WORKER_LOCK = threading.Lock()

def _push_dedup_key(kind: str, payload: Dict[str, Any]) -> str:
    if kind == "signal":
        return "signal:%s:%s:%s" % (payload.get("type"), payload.get("h"), payload.get("tick"))
    if kind == "execution":
        return "execution:%s:%s:%s:%s" % (payload.get("event"), payload.get("side"), payload.get("ticket"), payload.get("tick"))
    if kind == "fvg":
        return "fvg:%s:%s:%s" % (payload.get("action"), payload.get("type"), payload.get("idx"))
    if kind == "alert":
        # alert sub-kind keys the dedup. A Sin. at tick N and a
        # Sine. at tick N are distinct logical events (different branch
        # of the edge-case resolution), so the sub-kind is part of the key.
        return "alert:%s:%s:%s:%s" % (payload.get("sub"), payload.get("price"), payload.get("h"), payload.get("tick"))
    return kind + ":" + str(payload.get("tick", ""))

def _push_dedup_allow(key: str) -> bool:
    now = time.monotonic() * 1000.0
    with _PUSH_DEDUP_LOCK:
        last = _PUSH_DEDUP.get(key)
        if last is not None and (now - last) < PUSH_DEDUP_WINDOW_MS:
            return False
        _PUSH_DEDUP[key] = now
        cutoff = now - 60000.0
        for k in list(_PUSH_DEDUP.keys()):
            if _PUSH_DEDUP[k] < cutoff:
                del _PUSH_DEDUP[k]
    return True

class _RingHandler(logging.Handler):
    def emit(self, record):
        try:
            msg = self.format(record)
            with _LOG_LOCK:
                _LOG_BUFFER.append({
                    "ts": datetime.fromtimestamp(record.created).isoformat(),
                    "level": record.levelname.lower(),
                    "msg": msg,
                })
        except Exception:
            pass

logging.basicConfig(
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    level=logging.INFO
)
logger = logging.getLogger(__name__)
_ring_handler = _RingHandler()
logger.addHandler(_ring_handler)
logger.propagate = False

_telegram_ext_logger = logging.getLogger("telegram.ext")
_telegram_ext_logger.addHandler(_ring_handler)
_telegram_ext_logger.setLevel(logging.INFO)
_telegram_ext_logger.propagate = False

# ============================================================================
# TOAST EMISSION + TELEGRAM PUSH (THREADED AS REPLY)
# ============================================================================
def format_aea(kind: str, payload: Dict[str, Any]) -> Optional[str]:
    """Single formatter for bot and TWA messages. All call sites use this."""
    if kind == "state":
        try:
            seed = payload.get("seed") or {}
            aeea = payload.get("aeea") or {}
            return (
                f"AE TWA \u00b7 seed tick {seed.get('tick', '—')} "
                f"\u00b7 gen {seed.get('generation', '—')} "
                f"\u00b7 s2 {seed.get('s2', '—')} r2 {seed.get('r2', '—')} "
                f"\u00b7 regime {aeea.get('regime', '—')} "
                f"\u00b7 m {aeea.get('m', '—')} / n {aeea.get('n', '—')}"
            )
        except Exception:
            return "AE TWA \u00b7 WAITING"
    return _format_push_message(kind, payload)

def _format_push_message(kind: str, payload: Dict[str, Any]) -> Optional[str]:
    if kind == "signal" and not PUSH_ON_SIGNAL:
        return None
    if kind == "execution" and not PUSH_ON_EXECUTION:
        return None
    if kind == "fvg" and not PUSH_ON_FVG:
        return None
    if kind == "close" and not PUSH_ON_CLOSE:
        return None
    # alerts are signal-class events (they fire on the same signal
    # path as the Long/Short/Sin./Sine. Alerts in the FF's OnTick), so
    # they reuse the PUSH_ON_SIGNAL gate.
    if kind == "alert" and not PUSH_ON_SIGNAL:
        return None
    if kind == "signal":
        direction = payload.get("type", "NEUTRAL")
        arrow = "📈" if direction == "BUY" else ("📉" if direction == "SELL" else "⚪")
        dir_cs = _cs(direction)
        return (
            f"🎯 *ÆEA 𝒮_signal* {arrow}\n"
            f"*Type:* {_md_escape(dir_cs)}\n"
            f"*Price:* `{_md_escape(payload.get('price'))}`\n"
            f"*m/n:* {_md_escape(payload.get('m'))}/{_md_escape(payload.get('n'))} @ h={_md_escape(payload.get('h'))}\n"
            f"*ℛ_regime:* {_md_escape(payload.get('regime', '—'))}\n"
            f"*Tick:* {_md_escape(payload.get('tick', '—'))}\n"
            f"💎 Natalia Tanyatia"
        )
    if kind == "execution":
        event = payload.get("event", "EXEC")
        emoji_map = {
            "Bull": "🐂", "Bear": "🐻", "Whisky": "🥃", "Wine": "🍷",
            "Watter": "💧", "Blood": "🩸", "Hawk": "🦅", "Dove": "🕊️",
            "Diamond": "🔷", "Ruby": "🔻", "Top": "▲", "Bott": "▼",
            "A": "🅰️", "B": "🅱️", "ManualOrder": "📝", "ManualClose": "✂️",
            "ManualOpen": "➕", "Pending": "⏳",
        }
        emoji = emoji_map.get(event, "⚡")
        cs_event = _cs_exec(event)
        side = payload.get("side", "NONE")
        ticket = payload.get("ticket", -1)
        ticket_str = f"#{ticket}" if ticket != -1 else "—"
        reason = payload.get("reason", "")
        reason_str = f"\n*Reason:* {_md_escape(reason)}" if reason else ""
        return (
            f"{emoji} *ÆEA ℰ_exec: {_md_escape(cs_event)}*\n"
            f"*Side:* {_md_escape(_cs(side))}\n"
            f"*Ticket:* {_md_escape(ticket_str)}\n"
            f"*Price:* `{_md_escape(payload.get('price'))}`\n"
            f"*Tick:* {_md_escape(payload.get('tick', '—'))}{reason_str}\n"
            f"💎 Natalia Tanyatia"
        )
    if kind == "fvg":
        action = payload.get("action", "commit")
        fvg_type = payload.get("type", "top")
        arrow = "▲" if fvg_type == "top" else "▼"
        return (
            f"📐 *ÆEA ℱ_VG {_md_escape(action.upper())}*\n"
            f"*Type:* {arrow} {_md_escape(fvg_type)}\n"
            f"*Price:* `{_md_escape(payload.get('price'))}`\n"
            f"*Idx:* {_md_escape(payload.get('idx', '—'))}\n"
            f"💎 Natalia Tanyatia"
        )
    if kind == "alert":
        sub = payload.get("sub", "alert")
        cs_sub = _cs_alert(sub)
        emoji = "🔵" if sub == "long" else ("🔴" if sub == "short" else "🎯")
        body_lines = []
        body_lines.append(f"*Kind:* {_md_escape(cs_sub)}")
        if payload.get("price") is not None:
            body_lines.append(f"*Price:* `{_md_escape(payload.get('price'))}`")
        if sub in ("sin", "sine"):
            body_lines.append(f"*O:* {_md_escape(payload.get('O', payload.get('o', '—')))}")
            body_lines.append(f"*𝒞:* {_md_escape(_cs(payload.get('C')))}")
            body_lines.append(f"*𝒸:* {_md_escape(_cs(payload.get('c')))}")
        body_lines.append(f"*Tick:* {_md_escape(payload.get('tick', '—'))}")
        return (
            f"{emoji} *ÆEA {_md_escape(cs_sub)}*\n"
            + "\n".join(body_lines)
            + "\n💎 Natalia Tanyatia"
        )
    return None

def _telegram_push(kind: str, payload: Dict[str, Any]) -> None:
    key = _push_dedup_key(kind, payload)
    if not _push_dedup_allow(key):
        return
    msg = format_aea(kind, payload)
    if msg is None:
        return
    engine = BRIDGE_ENGINE_REF.get("engine")
    if engine is None:
        return
    bot = BRIDGE_ENGINE_REF.get("bot")
    if bot is None:
        return
    st = engine.state
    target_chat = st.chat_id
    if target_chat is None:
        target_chat = st.webapp_user_id
    if not target_chat:
        return
    reply_to = st.last_inbound_message_id if isinstance(st.last_inbound_message_id, int) else None
    if not hasattr(bot, "_send_message_sync"):
        logger.warning("📲 Push skipped: bot has no _send_message_sync")
        return
    ok = bot._send_message_sync(
        chat_id=target_chat,
        text=msg,
        parse_mode="Markdown",
        reply_to_message_id=reply_to,
    )
    if ok:
        logger.info(f"📲 Push sent ({kind}) to {target_chat} reply_to={reply_to} (tick={st.tick})")
    else:
        logger.warning(f"📲 Push failed ({kind}) to {target_chat} reply_to={reply_to} (tick={st.tick})")

def _push_worker_loop() -> None:
    while True:
        item = _PUSH_QUEUE.get()
        try:
            if item is None:
                break
            kind, payload = item
            _telegram_push(kind, payload)
        except Exception as e:
            logger.warning(f"📲 Push worker error: {e}")
        finally:
            try:
                _PUSH_QUEUE.task_done()
            except Exception:
                pass

def _ensure_push_worker() -> None:
    global _PUSH_WORKER_STARTED
    if _PUSH_WORKER_STARTED:
        return
    with _PUSH_WORKER_LOCK:
        if _PUSH_WORKER_STARTED:
            return
        t = threading.Thread(target=_push_worker_loop, name="aei-push-worker", daemon=True)
        t.start()
        _PUSH_WORKER_STARTED = True

def _emit_toast(kind: str, payload: Dict[str, Any]) -> int:
    global _TOAST_SEQ, _TOAST_FIRST_AVAILABLE_SEQ, _TOAST_BUFFER
    with _TOAST_LOCK:
        maxlen = _TOAST_BUFFER.maxlen
        if maxlen is None or maxlen <= 0:
            _TOAST_BUFFER = deque(maxlen=1)
        was_full = (len(_TOAST_BUFFER) >= _TOAST_BUFFER.maxlen)
        _TOAST_SEQ += 1
        seq = _TOAST_SEQ
        entry = dict(payload)
        entry["kind"] = kind
        entry["seq"] = seq
        if "ts" not in entry:
            entry["ts"] = datetime.now().isoformat()
        _TOAST_BUFFER.append(entry)
        if was_full and len(_TOAST_BUFFER) > 0:
            _TOAST_FIRST_AVAILABLE_SEQ = _TOAST_BUFFER[0].get("seq", _TOAST_SEQ)
        elif _TOAST_FIRST_AVAILABLE_SEQ == 0 and len(_TOAST_BUFFER) > 0:
            _TOAST_FIRST_AVAILABLE_SEQ = _TOAST_BUFFER[0].get("seq", seq)
    try:
        _ensure_push_worker()
        try:
            _PUSH_QUEUE.put_nowait((kind, entry))
        except queue.Full:
            dropped = False
            try:
                _PUSH_QUEUE.get_nowait()
                _PUSH_QUEUE.task_done()
                dropped = True
            except Exception:
                pass
            try:
                _PUSH_QUEUE.put_nowait((kind, entry))
            except Exception as e:
                logger.warning(f"📲 Push queue full; dropped toast kind={kind} seq={seq} (evicted_oldest={dropped}): {e}")
    except Exception as e:
        logger.warning(f"📲 Push dispatch failed: {e}")
    return seq

# ============================================================================
# ALERT EMISSION
# ============================================================================
# The FF emits Alert(...) at every execution subblock and at every edge
# case. The three families are:
#   (a) The Long/Short alerts inside the `if(signal != 0)` block:
#       Alert("Long:", price) and Alert("Short:", price).
#   (b) The Diamond/Ruby header alerts at the top of each toll/count
#       subblock: Alert("🔷", "Diamond", fg) and Alert("🔻", "Ruby", fg).
#   (c) The Sin./Sine. edge-case alerts inside the OnGaurd(-1) block.
#
# Family (a) is emitted as a "long" or "short" alert toast.
# Family (b) is already emitted as an execution toast; the CS glyph is
# 𝒟_Diamond / ℛ_Ruby. The header fires BEFORE the body's own execution
# toast so the user sees the branch label, then the body event.
# Family (c) is emitted as a "sin" or "sine" alert toast.
#
# All three reuse the PUSH_ON_SIGNAL gate (they are signal-path events).
# The CS glyphs are 𝒮_Long / 𝒮_Short / 𝒮_sin / 𝒮_sine.
# ============================================================================
def _emit_alert(sub: str, payload: Dict[str, Any]) -> int:
    body = dict(payload)
    body["sub"] = sub
    return _emit_toast("alert", body)

# ============================================================================
# DATACLASSES
# ============================================================================
@dataclass
class PriceData:
    bid: Decimal = Decimal('0.0')
    ask: Decimal = Decimal('0.0')
    close: Decimal = Decimal('0.0')
    open: Decimal = Decimal('0.0')
    high: Decimal = Decimal('0.0')
    low: Decimal = Decimal('0.0')
    volume: Decimal = Decimal('0.0')
    timestamp: datetime = field(default_factory=datetime.now)
    provider: str = ""

    @property
    def spread(self) -> Decimal:
        return self.ask - self.bid

@dataclass
class IndicatorState:
    adx: Decimal = Decimal('50.0')
    stochastic: Decimal = Decimal('50.0')
    rvi: Decimal = Decimal('50.0')
    ac: Decimal = Decimal('50.0')
    force: Decimal = Decimal('50.0')
    obv: Decimal = Decimal('50.0')
    ad: Decimal = Decimal('50.0')
    mfi: Decimal = Decimal('50.0')
    momentum: Decimal = Decimal('50.0')
    dem: Decimal = Decimal('50.0')
    wpr: Decimal = Decimal('50.0')
    cci: Decimal = Decimal('50.0')
    rsi: Decimal = Decimal('50.0')
    ihk_kijun: Decimal = Decimal('50.0')
    ihk_tenkan: Decimal = Decimal('50.0')

@dataclass
class Order:
    ticket: int
    side: str
    entry: Decimal
    sl: Decimal = Decimal('0.0')
    tp: Decimal = Decimal('0.0')
    lot: Decimal = Decimal('0.01')
    opened_at: datetime = field(default_factory=datetime.now)
    closed_at: Optional[datetime] = None
    close_price: Optional[Decimal] = None

    def pnl(self, current_price: Decimal) -> Decimal:
        if self.side == 'BUY':
            return (current_price - self.entry) * self.lot * Decimal('100000')
        else:
            return (self.entry - current_price) * self.lot * Decimal('100000')

@dataclass
class AEI_CoreState:
    KC: bool = True
    invert: bool = True
    tag: int = -1
    prime: int = -1
    dime: int = -1
    mem: int = -1
    tick: int = 0
    y: int = Y_START
    signal: Decimal = Decimal('0.0')
    signature: bool = False
    tick_tock: bool = False
    FG: bool = False
    GF: bool = False
    Buy: int = -1
    Sell: int = -1
    A: bool = True
    B: bool = True
    a: bool = True
    b: bool = True
    ab: bool = False
    ba: bool = True
    u: bool = False
    v: bool = False
    lOrder_id: int = -1
    kOrder_id: int = -1
    D: Decimal = Decimal('0.0')
    E: Decimal = Decimal('0.0')
    p: Decimal = Decimal('0.0')
    q: Decimal = Decimal('0.0')
    K: bool = False
    C: bool = True
    c: bool = True
    iC: bool = True
    jC: bool = True
    Cc: bool = True
    cC: bool = True
    safety: bool = False
    Z: int = Y_START + 1
    z: int = Y_START + 1
    O: int = Y_START + 1
    o: int = Y_START + 1
    r: int = 0
    W: int = Y_START + 1
    w: int = Y_START + 1
    I: int = 0
    iI: int = 0
    J: int = 0
    iJ: int = 0
    ij: int = 0
    h: int = 0
    iZ: int = Y_START + 1
    iz: int = Y_START + 1
    iW: int = Y_START + 1
    iw: int = Y_START + 1
    iO: int = Y_START + 1
    io: int = Y_START + 1
    ir: int = 0
    count: int = 0
    toll: int = 0
    tally: str = "   "
    m: int = 0
    n: int = 0
    authoritative_m: int = 0
    authoritative_n: int = 0
    authoritative_h: int = -1
    m_now: int = 0
    n_now: int = 0
    lPass: Decimal = Decimal('0.0')
    ilPass: Decimal = Decimal('0.0')
    kPass: Decimal = Decimal('0.0')
    ikPass: Decimal = Decimal('0.0')
    Premium: List[Decimal] = field(default_factory=lambda: [Decimal('0.0')] * (X_PERIOD - Y_START))
    Discount: List[Decimal] = field(default_factory=lambda: [Decimal('0.0')] * (X_PERIOD - Y_START))
    HH: List[Decimal] = field(default_factory=lambda: [Decimal('0.0')] * (X_PERIOD - Y_START))
    LL: List[Decimal] = field(default_factory=lambda: [Decimal('0.0')] * (X_PERIOD - Y_START))
    k: List[bool] = field(default_factory=lambda: [False] * (X_PERIOD - Y_START))
    l: List[bool] = field(default_factory=lambda: [False] * (X_PERIOD - Y_START))
    U: List[bool] = field(default_factory=list)
    R: bool = True
    Regime: List[str] = field(default_factory=lambda: ["sRange"] * (X_PERIOD - Y_START))
    iA: List[List[Decimal]] = field(default_factory=lambda: [[Decimal('50.0')] * (X_PERIOD - Y_START) for _ in range(13)])
    cA: List[List[Decimal]] = field(default_factory=lambda: [[Decimal('50.0')] * (X_PERIOD - Y_START) for _ in range(13)])
    kA: List[List[Decimal]] = field(default_factory=lambda: [[Decimal('50.0')] * (X_PERIOD - Y_START) for _ in range(13)])
    lA: List[List[Decimal]] = field(default_factory=lambda: [[Decimal('50.0')] * (X_PERIOD - Y_START) for _ in range(13)])
    IHKk: List[Decimal] = field(default_factory=list)
    IHKt: List[Decimal] = field(default_factory=list)
    RSI: List[Decimal] = field(default_factory=list)
    CCI: List[Decimal] = field(default_factory=list)
    MOM: List[Decimal] = field(default_factory=list)
    AD: List[Decimal] = field(default_factory=list)
    OBV: List[Decimal] = field(default_factory=list)
    Force: List[Decimal] = field(default_factory=list)
    MFI: List[Decimal] = field(default_factory=list)
    DeM: List[Decimal] = field(default_factory=list)
    RVIm: List[Decimal] = field(default_factory=list)
    AC: List[Decimal] = field(default_factory=list)
    StdDev: List[Decimal] = field(default_factory=list)
    ATR: List[Decimal] = field(default_factory=list)
    ADX: List[Decimal] = field(default_factory=list)
    Suply: Decimal = Decimal('0.0')
    iSuply: Decimal = Decimal('0.0')
    Demand: Decimal = Decimal('0.0')
    iDemand: Decimal = Decimal('0.0')
    Sale: Decimal = Decimal('0.0')
    iSale: Decimal = Decimal('0.0')
    Stock: Decimal = Decimal('0.0')
    iStock: Decimal = Decimal('0.0')
    iStdDev: Decimal = Decimal('50.0')
    iATR: Decimal = Decimal('50.0')
    iIHKk: Decimal = Decimal('50.0')
    iIHKt: Decimal = Decimal('50.0')
    FVG: int = -1
    BL: List[Decimal] = field(default_factory=list)
    BL_type: List[str] = field(default_factory=list)
    bottomLine: str = "   "
    bL: str = "   "
    S: int = X_PERIOD
    T: int = X_PERIOD
    X_scan: int = Y_START
    Y_scan: int = Y_START
    t: Optional[datetime] = None
    iopen: Decimal = Decimal('0.0')
    iPrice: Decimal = Decimal('0.0')
    iH: Decimal = Decimal('0.0')
    iL: Decimal = Decimal('0.0')
    price: Decimal = Decimal('0.0')
    Price: Decimal = Decimal('0.0')
    open: Decimal = Decimal('0.0')
    chat_id: Optional[int] = None
    webapp_user_id: Optional[int] = None
    webapp_username: Optional[str] = None
    webapp_verified: bool = False
    webapp_last_seen: Optional[datetime] = None

    trailing_stop_active: bool = False
    trailing_stop_price: Decimal = Decimal('0.0')
    trailing_take_profit: Decimal = Decimal('0.0')
    on_track_runs: int = 0
    on_stand_runs: int = 0
    has_open_long: bool = False
    has_open_short: bool = False
    trailing_stop_entry: Decimal = Decimal('0.0')
    trailing_stop_side: str = ""

    last_kronecker_m: int = 0
    last_kronecker_n: int = 0
    last_kronecker_h: int = -1
    fvg_anchor_map: Dict[int, Dict[str, Any]] = field(default_factory=dict)
    _raw_price_missing: bool = False

    signal_history: List[Dict[str, Any]] = field(default_factory=list)
    max_signal_history: int = 100
    last_signal_at: Optional[str] = None
    bar_close_count: int = 0

    execution_fired: bool = False

    projection_path: List[Dict[str, Any]] = field(default_factory=list)
    projection_meta: Dict[str, Any] = field(default_factory=dict)
    projection_computed_at: Optional[str] = None
    projection_trigger: str = ""

    last_provider: str = ""
    last_volume: Decimal = Decimal('0.0')

    last_inbound_message_id: Optional[int] = None

# ============================================================================
# INDICATOR NAME CONSTANT (CS-translated for user-facing display)
# ============================================================================
INDICATOR_NAMES = [
    "ADX", "Stochastic", "RVI", "AC", "Force", "OBV", "AD",
    "MFI", "Momentum", "DeMarker", "WPR", "CCI", "RSI"
]
INDICATOR_NAMES_CS = [
    "𝒜[0]", "𝒜[1]", "𝒜[2]", "𝒜[3]", "𝒜[4]", "𝒜[5]", "𝒜[6]",
    "𝒜[7]", "𝒜[8]", "𝒜[9]", "𝒜[10]", "𝒜[11]", "𝒜[12]",
]

# ============================================================================
# MODULE-LEVEL INDICATOR HELPERS — MQL4 PARITY
# ============================================================================
def sma(data: List[Decimal], period: int) -> Decimal:
    if len(data) < period or period <= 0:
        return Decimal('0.0')
    total = sum(data[-period:], Decimal('0.0'))
    return total / Decimal(period)

def ema(data: List[Decimal], period: int) -> Decimal:
    if len(data) < period or period <= 0:
        return sma(data, period)
    alpha = Decimal('2.0') / (Decimal(period) + Decimal('1.0'))
    if len(data) > 1:
        return alpha * data[-1] + (Decimal('1.0') - alpha) * ema(data[:-1], period)
    return data[-1]

def rsi(data: List[Decimal], period: int = 14) -> Decimal:
    if len(data) < period + 1 or period <= 0:
        return Decimal('50.0')
    gains = Decimal('0.0')
    losses = Decimal('0.0')
    for i in range(period):
        diff = data[i + 1] - data[i]
        if diff >= Decimal('0.0'):
            gains += diff
        else:
            losses -= diff
    avg_gain = gains / Decimal(period)
    avg_loss = losses / Decimal(period)
    for i in range(period + 1, len(data)):
        diff = data[i] - data[i - 1]
        gain = diff if diff > Decimal('0.0') else Decimal('0.0')
        loss = -diff if diff < Decimal('0.0') else Decimal('0.0')
        avg_gain = (avg_gain * Decimal(period - 1) + gain) / Decimal(period)
        avg_loss = (avg_loss * Decimal(period - 1) + loss) / Decimal(period)
    if avg_loss == Decimal('0.0'):
        return Decimal('100.0')
    rs = avg_gain / avg_loss
    return Decimal('100.0') - (Decimal('100.0') / (Decimal('1.0') + rs))

def stochastic(high, low, close, k_period=14, d_period=3, slowing=1):
    if slowing < 1:
        slowing = 1
    if len(close) < k_period + slowing - 1 or k_period <= 0:
        return Decimal('50.0'), Decimal('50.0')
    raw_k_series = []
    for i in range(slowing):
        if len(close) < k_period + i:
            continue
        h_i = max(high[-(k_period + i):-i]) if i > 0 else max(high[-k_period:])
        l_i = min(low[-(k_period + i):-i]) if i > 0 else min(low[-k_period:])
        r_i = h_i - l_i
        if r_i == Decimal('0.0'):
            raw_k_series.append(Decimal('50.0'))
        else:
            c_i = close[-1 - i]
            raw_k_series.append(Decimal('100.0') * (c_i - l_i) / r_i)
    if not raw_k_series:
        return Decimal('50.0'), Decimal('50.0')
    fast_k = sum(raw_k_series) / Decimal(len(raw_k_series))
    d_series = []
    for i in range(d_period):
        if i == 0:
            d_series.append(fast_k)
        else:
            if len(close) < k_period + slowing - 1 + i:
                d_series.append(fast_k)
                continue
            raw_k_i = []
            for j in range(slowing):
                idx = -1 - i - j
                if abs(idx) > len(close) - k_period:
                    continue
                h_i = max(high[idx - k_period + 1:idx + 1]) if idx < -1 else max(high[-k_period:])
                l_i = min(low[idx - k_period + 1:idx + 1]) if idx < -1 else min(low[-k_period:])
                r_i = h_i - l_i
                if r_i == Decimal('0.0'):
                    raw_k_i.append(Decimal('50.0'))
                else:
                    raw_k_i.append(Decimal('100.0') * (close[idx] - l_i) / r_i)
            if raw_k_i:
                d_series.append(sum(raw_k_i) / Decimal(len(raw_k_i)))
            else:
                d_series.append(fast_k)
    d = sum(d_series) / Decimal(len(d_series)) if d_series else fast_k
    return fast_k, d

def bollinger_bands(close, period=20, dev=Decimal('2.0')):
    if len(close) < period or period <= 0:
        return Decimal('0.0'), Decimal('0.0'), Decimal('0.0')
    mid = sma(close, period)
    variance = sum((x - mid) ** 2 for x in close[-period:]) / Decimal(period)
    std = variance.sqrt() if variance > Decimal('0.0') else Decimal('0.0')
    upper = mid + dev * std
    lower = mid - dev * std
    return upper, mid, lower

def true_range(high, low, close, i):
    if i + 1 >= len(close):
        return high[i] - low[i]
    tr1 = high[i] - low[i]
    tr2 = abs(high[i] - close[i + 1])
    tr3 = abs(low[i] - close[i + 1])
    return max(tr1, tr2, tr3)

def atr(high, low, close, period=14):
    if len(close) < period + 1 or period <= 0:
        return Decimal('0.0')
    trs = []
    for i in range(period):
        trs.append(true_range(high, low, close, i))
    return sum(trs) / Decimal(period)

def stddev(data, period):
    if len(data) < period or period <= 0:
        return Decimal('0.0')
    mean = sum(data[-period:]) / Decimal(period)
    variance = sum((x - mean) ** 2 for x in data[-period:]) / Decimal(period)
    return variance.sqrt() if variance > Decimal('0.0') else Decimal('0.0')

def ichimoku(high, low, close, t_period: int, k_period: int, j_period: int):
    if len(close) < j_period or j_period <= 0 or k_period <= 0 or t_period <= 0:
        return {"tenkan": Decimal('50.0'), "kijun": Decimal('50.0'),
                "senkou_a": Decimal('50.0'), "senkou_b": Decimal('50.0')}
    tenkan = (max(high[-t_period:]) + min(low[-t_period:])) / Decimal('2.0')
    kijun = (max(high[-k_period:]) + min(low[-k_period:])) / Decimal('2.0')
    senkou_a = (tenkan + kijun) / Decimal('2.0')
    senkou_b = (max(high[-j_period:]) + min(low[-j_period:])) / Decimal('2.0')
    return {"tenkan": tenkan, "kijun": kijun, "senkou_a": senkou_a, "senkou_b": senkou_b}

def to_decimal(value):
    try:
        if isinstance(value, Decimal):
            return value
        return Decimal(str(value))
    except Exception:
        return Decimal('0.0')

# ============================================================================
# : SYMBOL POINT-SIZE
# ============================================================================
def symbol_point(symbol: str) -> Decimal:
    digits = _symbol_digits(symbol)
    return Decimal(10) ** Decimal(-digits)

def _symbol_digits(symbol: str) -> int:
    try:
        import MetaTrader5 as _mt5  # type: ignore
        info = _mt5.symbol_info(symbol)
        if info is not None and hasattr(info, "digits"):
            return int(info.digits)
    except Exception:
        pass
    if symbol in SYMBOL_DIGITS:
        return SYMBOL_DIGITS[symbol]
    for canonical, chain in SYMBOL_FALLBACKS.items():
        if symbol in chain:
            return SYMBOL_DIGITS.get(canonical, SYMBOL_DIGITS_DEFAULT)
    return SYMBOL_DIGITS_DEFAULT

# ============================================================================
# TELEGRAM WEB APP AUTHENTICATION
# ============================================================================
def verify_telegram_init_data(init_data: str, bot_token: str, max_age_seconds: int = 86400) -> Optional[Dict[str, Any]]:
    if not init_data or not bot_token:
        return None
    try:
        parsed = dict(parse_qsl(init_data, keep_blank_values=True))
    except Exception:
        return None
    received_hash = parsed.pop("hash", None)
    if not received_hash:
        return None
    data_check_string = "\n".join(f"{k}={v}" for k, v in sorted(parsed.items()))
    secret_key = hmac.new(b"WebAppData", bot_token.encode("utf-8"), hashlib.sha256).digest()
    expected_hash = hmac.new(secret_key, data_check_string.encode("utf-8"), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(expected_hash, received_hash):
        return None
    auth_date_raw = parsed.get("auth_date")
    if auth_date_raw is not None:
        try:
            auth_age = time.time() - int(auth_date_raw)
            if auth_age > max_age_seconds or auth_age < -300:
                return None
        except (ValueError, TypeError):
            return None
    user_json = parsed.get("user")
    user_obj: Optional[Dict[str, Any]] = None
    if user_json:
        try:
            user_obj = json.loads(user_json)
        except Exception:
            user_obj = None
    return {
        "user": user_obj,
        "auth_date": int(auth_date_raw) if auth_date_raw else None,
        "raw": parsed,
    }

def _extract_auth_headers(handler: "BridgeHandler") -> Tuple[Optional[int], Optional[str], bool]:
    raw_init = handler.headers.get("X-Telegram-Init-Data", "").strip()
    if not raw_init:
        return (None, None, False)
    verified = verify_telegram_init_data(raw_init, TELEGRAM_BOT_TOKEN_ENV)
    if not verified or not verified.get("user"):
        return (None, None, False)
    u = verified["user"] or {}
    return (u.get("id"), u.get("username"), True)

# ============================================================================
# FEED CLIENT — CLOUDFLARE WORKER RELAY
# ============================================================================
class FeedClient:
    def __init__(self, symbol: str = "BTC-USD"):
        self.symbol = symbol
        chain = SYMBOL_FALLBACKS.get(symbol)
        if chain is None:
            if symbol.endswith("-USD"):
                base = symbol[:-4]
                chain = [symbol, f"{base}USD=X"]
            else:
                chain = [symbol]
        self._chain: List[str] = list(chain)
        self._chain_index: int = 0
        self._last_update: Optional[datetime] = None
        self._failure_count: int = 0
        self._fallback_count: int = 0
        self._last_provider: str = ""
        self._last_volume: Decimal = Decimal('0.0')

    def active_symbol(self) -> str:
        return self._chain[self._chain_index]

    def failure_count(self) -> int:
        return self._failure_count

    def last_update(self) -> Optional[datetime]:
        return self._last_update

    def last_provider(self) -> str:
        return self._last_provider

    def last_volume(self) -> Decimal:
        return self._last_volume

    def _advance_symbol_chain(self) -> None:
        if len(self._chain) <= 1:
            return
        self._chain_index = (self._chain_index + 1) % len(self._chain)
        logger.warning(f"🔄 FeedClient: rotating symbol chain to '{self.active_symbol()}'")
        self._fallback_count = 0
        self._failure_count = 0

    def _rebuild_ticker(self) -> None:
        logger.info("🔄 FeedClient: rebuild requested (no-op; Worker handles upstream)")

    def _get(self, kind: str, **params) -> Optional[Any]:
        if not RELAY_URL:
            logger.error("❌ RELAY_URL not set — cannot fetch price")
            return None
        params["symbol"] = self.active_symbol()
        params["kind"] = kind
        qs = urllib.parse.urlencode(params)
        url = f"{RELAY_URL}/?{qs}"
        last_error = None
        for attempt in range(RELAY_MAX_RETRIES):
            try:
                req_headers = {
                    "Accept": "application/json",
                    "User-Agent": "AEI-Bridge/final",
                    "Cache-Control": "no-cache",
                }
                if RELAY_KEY:
                    req_headers["X-Relay-Key"] = RELAY_KEY
                req = urllib.request.Request(url, headers=req_headers)
                with urllib.request.urlopen(req, timeout=RELAY_TIMEOUT) as r:
                    raw = r.read().decode("utf-8")
                    payload = json.loads(raw)
                    if isinstance(payload, dict) and payload.get("error"):
                        detail_raw = str(payload.get("detail", ""))
                        detail_short = detail_raw[:200] + ("…" if len(detail_raw) > 200 else "")
                        logger.warning(
                            f"Relay returned error for {self.active_symbol()} "
                            f"(kind={kind}): {payload.get('error')} ({detail_short})"
                        )
                        self._failure_count += 1
                        self._fallback_count += 1
                        if self._fallback_count >= 5:
                            self._advance_symbol_chain()
                        return None
                    self._failure_count = 0
                    self._fallback_count = 0
                    self._last_update = datetime.now()
                    if isinstance(payload, dict):
                        if payload.get("provider"):
                            self._last_provider = str(payload["provider"])
                        if payload.get("volume") is not None:
                            try:
                                self._last_volume = Decimal(str(payload["volume"]))
                            except Exception:
                                pass
                    elif isinstance(payload, list) and payload:
                        last = payload[-1]
                        if isinstance(last, dict):
                            if last.get("provider"):
                                self._last_provider = str(last["provider"])
                            if last.get("volume") is not None:
                                try:
                                    self._last_volume = Decimal(str(last["volume"]))
                                except Exception:
                                    pass
                    return payload
            except urllib.error.HTTPError as e:
                try:
                    error_body = e.read().decode('utf-8', errors='ignore')
                except Exception:
                    error_body = '<unreadable>'
                last_error = f"HTTP {e.code}: {error_body[:200]}"
                logger.warning(f"Relay HTTP Error {e.code} for {self.active_symbol()} kind={kind} (attempt {attempt+1}/{RELAY_MAX_RETRIES}): {error_body[:200]}")
                if e.code == 429 and attempt < RELAY_MAX_RETRIES - 1:
                    time.sleep(1 + attempt * 2)
                    continue
                break
            except urllib.error.URLError as e:
                last_error = f"URLError: {e.reason}"
                logger.warning(f"Relay URLError for {self.active_symbol()} kind={kind} (attempt {attempt+1}/{RELAY_MAX_RETRIES}): {e.reason}")
                if attempt < RELAY_MAX_RETRIES - 1:
                    time.sleep(1 + attempt * 2)
                    continue
                break
            except json.JSONDecodeError as e:
                last_error = f"JSONDecodeError: {e}"
                logger.warning(f"Relay returned invalid JSON for {self.active_symbol()} kind={kind}: {e}")
                break
            except Exception as e:
                last_error = f"{type(e).__name__}: {e}"
                logger.warning(f"Relay error ({kind}) for {self.active_symbol()} (attempt {attempt+1}/{RELAY_MAX_RETRIES}): {e}")
                if attempt < RELAY_MAX_RETRIES - 1:
                    time.sleep(1 + attempt * 2)
                    continue
                break
        self._failure_count += 1
        self._fallback_count += 1
        if self._fallback_count >= 5:
            self._advance_symbol_chain()
        if last_error:
            logger.warning(f"Relay exhausted retries for {kind}: {last_error}")
        return None

    def get_current_price(self) -> Tuple[Decimal, Decimal]:
        d = self._get("price")
        if not d or "close" not in d or d.get("close") is None:
            return Decimal('0.0'), Decimal('0.0')
        try:
            c = Decimal(str(d["close"]))
            if c <= Decimal('0.0'):
                logger.warning(f"Relay returned non-positive price: {c}")
                return Decimal('0.0'), Decimal('0.0')
            bid = Decimal(str(d.get("bid") or d["close"]))
            ask = Decimal(str(d.get("ask") or d["close"]))
            if d.get("volume") is not None:
                try:
                    self._last_volume = Decimal(str(d["volume"]))
                except Exception:
                    pass
            if d.get("provider"):
                self._last_provider = str(d["provider"])
            return bid, ask
        except Exception as e:
            logger.warning(f"Failed to parse relay price: {e}")
            return Decimal('0.0'), Decimal('0.0')

    def get_historical_klines(self, limit: int = 200, interval: str = "1m") -> List[Dict[str, Any]]:
        d = self._get("history", limit=limit, interval=interval)
        if not d or not isinstance(d, list):
            return []
        out = []
        for row in d:
            try:
                if not isinstance(row, dict):
                    continue
                o = row.get("open")
                h = row.get("high")
                l = row.get("low")
                c = row.get("close")
                # : every OHLC field must be a real positive price.
                # A bar with any zero/null OHLC field is not a bar.
                if o is None or h is None or l is None or c is None:
                    continue
                o_d = Decimal(str(o))
                h_d = Decimal(str(h))
                l_d = Decimal(str(l))
                c_d = Decimal(str(c))
                if o_d <= Decimal('0.0') or h_d <= Decimal('0.0') or l_d <= Decimal('0.0') or c_d <= Decimal('0.0'):
                    continue
                if h_d < l_d:
                    continue
                if not (o_d.is_finite() and h_d.is_finite() and l_d.is_finite() and c_d.is_finite()):
                    continue
                ts_raw = row.get("timestamp")
                ts = datetime.now()
                if ts_raw:
                    try:
                        ts = datetime.fromisoformat(ts_raw.replace("Z", "+00:00")).replace(tzinfo=None)
                    except Exception:
                        pass
                vol = Decimal(str(row.get("volume") or 0))
                if vol < Decimal('0.0'):
                    vol = Decimal('0.0')
                out.append({
                    "open": o_d,
                    "high": h_d,
                    "low": l_d,
                    "close": c_d,
                    "volume": vol,
                    "timestamp": ts,
                    "provider": str(row.get("provider", "")),
                })
            except Exception:
                continue
        if out:
            last = out[-1]
            self._last_volume = last.get("volume", Decimal('0.0'))
            if last.get("provider"):
                self._last_provider = last["provider"]
        return out

    def get_intraday(self, interval: str = "1m") -> Dict[str, Any]:
        d = self._get("intraday", interval=interval)
        if not d or d.get("close") is None:
            return {}
        try:
            c = Decimal(str(d["close"]))
            if c <= Decimal('0.0'):
                logger.warning(f"Relay returned non-positive intraday close: {c}")
                return {}
            ts_raw = d.get("timestamp")
            ts = datetime.now()
            if ts_raw:
                try:
                    ts = datetime.fromisoformat(ts_raw.replace("Z", "+00:00")).replace(tzinfo=None)
                except Exception:
                    pass
            vol = Decimal(str(d.get("volume") or 0))
            self._last_volume = vol
            if d.get("provider"):
                self._last_provider = str(d["provider"])
            return {
                "open": Decimal(str(d["open"])),
                "high": Decimal(str(d["high"])),
                "low": Decimal(str(d["low"])),
                "close": c,
                "volume": vol,
                "timestamp": ts,
                "provider": self._last_provider,
            }
        except Exception as e:
            logger.warning(f"Failed to parse intraday: {e}")
            return {}

    def get_volume(self) -> Dict[str, Any]:
        d = self._get("volume")
        if not d or not isinstance(d, dict):
            return {}
        try:
            vol = Decimal(str(d.get("volume") or 0))
            vol24 = Decimal(str(d.get("volume_24h") or 0))
            self._last_volume = vol
            if d.get("provider"):
                self._last_provider = str(d["provider"])
            return {
                "volume": vol,
                "volume_24h": vol24,
                "provider": self._last_provider,
            }
        except Exception as e:
            logger.warning(f"Failed to parse volume: {e}")
            return {}

    def get_info(self) -> Dict[str, Any]:
        return {"name": self.active_symbol(), "currency": "USD"}

    def probe(self) -> Dict[str, Any]:
        d = self._get("price")
        return {
            "active_symbol": self.active_symbol(),
            "primary_symbol": self.symbol,
            "chain": list(self._chain),
            "chain_index": self._chain_index,
            "empty": (d is None or d.get("close") is None),
            "failure_count": self._failure_count,
            "fallback_count": self._fallback_count,
            "last_update": self._last_update.isoformat() if self._last_update else None,
            "provider": self._last_provider,
            "last_volume": str(self._last_volume),
        }

# ============================================================================
# CORE ÆEA ENGINE — Faithful Port of ÆEA.mq4
# ============================================================================
class AEEA_Engine:
    def __init__(self):
        self.state = AEI_CoreState()
        self.seed = AEI_Seed()
        try:
            self.ordered_feed = OrderedFeed()
        except Exception:
            self.ordered_feed = None
        self.crawler = CrawlerState()
        self.cs_feedback = CSFeedbackStore()
        self.price_history: List[PriceData] = []
        self.ohlcv_history: List[Dict[str, Any]] = []
        self.feed = FeedClient(SYMBOL)
        self._last_price_update: Optional[datetime] = None
        self._bar_open: bool = True
        self._bar_index: int = 0
        self._running: bool = False
        self.chat_id: Optional[int] = None
        self.application = None
        self._last_signal_time: Optional[datetime] = None
        self._initialization_attempted: bool = False
        self._tick_log_counter: int = 0
        self._price_update_counter: int = 0
        self._bridge_publish_callback = None
        self._last_relay_warn: Optional[datetime] = None
        self._consecutive_zero_prices: int = 0
        self._indicator_populate_count: int = 0
        self._imbalance_fire_count: int = 0
        self._active_trailing_stop: Decimal = Decimal('0.0')
        self._active_trailing_tp: Decimal = Decimal('0.0')
        self._last_kronecker_bar: int = -1
        self._sSL: Decimal = Decimal('0.0')
        self._bSL: Decimal = Decimal('0.0')
        self._sTP: Decimal = Decimal('0.0')
        self._bTP: Decimal = Decimal('0.0')
        self._point_size: Decimal = symbol_point(SYMBOL)
        self._com_price_frozen: Decimal = COMMISSION * (self._point_size if self._point_size > Decimal('0.0') else Decimal('0.00001'))
        self.orders: List[Order] = []
        self._next_ticket: int = 1
        self._alert_delivery_enabled: bool = True
        self._last_telegram_toast_seq: int = 0
        self._last_dispatch_event: str = ""
        self._last_comment_line: str = ""

    def _com_price(self) -> Decimal:
        # : the FF computes `com = Commssion * Point` once at OnInit
        # and reuses the frozen value for the entire session. The port's
        # dynamic _com_price() is preserved for the probe/diagnostic path
        # (informational only). The signal-trigger and _S() paths use
        # self._com_price_frozen, which is set at init and re-frozen on
        # settings apply and on symbol change.
        point = self._point_size if self._point_size > Decimal('0.0') else Decimal('0.00001')
        return COMMISSION * point

    def OnInit(self) -> None:
        logger.info("⚡ OnInit(): EA engine lifecycle beginning")
        self.OnReInit()
        logger.info("🟢 OnInit(): state reset to baseline")
        try:
            self._project_arc_length(trigger="init")
        except Exception as e:
            logger.warning(f"Initial projection seed failed: {e}")

    def OnReInit(self) -> None:
        with _ENGINE_LOCK:
            self._OnReInit_locked()

    def _OnReInit_locked(self) -> None:
        st = self.state
        saved_ohlcv = self.ohlcv_history.copy()
        saved_price = st.price
        saved_Price = st.Price
        saved_iH = st.iH
        saved_iL = st.iL
        saved_tick = st.tick
        saved_on_track = st.on_track_runs
        saved_on_stand = st.on_stand_runs
        saved_signal_history = list(st.signal_history)
        saved_chat_id = st.chat_id
        saved_webapp_uid = st.webapp_user_id
        saved_webapp_uname = st.webapp_username
        saved_webapp_verified = st.webapp_verified
        saved_comment = self._last_comment_line
        saved_provider = st.last_provider
        saved_volume = st.last_volume
        saved_inbound_msg = st.last_inbound_message_id

        st.KC = st.invert
        size = X_PERIOD - Y_START
        for i in range(13):
            st.cA[i] = [Decimal('0.0')] * size
            st.iA[i] = [Decimal('0.0')] * size
            st.kA[i] = [Decimal('0.0')] * size
            st.lA[i] = [Decimal('0.0')] * size
        st.IHKk = []
        st.IHKt = []
        st.RSI = []
        st.CCI = []
        st.MOM = []
        st.AD = []
        st.OBV = []
        st.Force = []
        st.MFI = []
        st.DeM = []
        st.RVIm = []
        st.AC = []
        st.StdDev = []
        st.ATR = []
        st.ADX = []
        st.Regime = ["sRange"] * size
        st.Premium = [Decimal('0.0')] * size
        st.Discount = [Decimal('0.0')] * size
        st.HH = [Decimal('0.0')] * size
        st.LL = [Decimal('0.0')] * size
        st.k = [False] * size
        st.l = [False] * size
        st.U = []
        st.R = True
        st.D = Decimal('0.0')
        st.E = Decimal('0.0')
        st.K = False
        st.Z = Y_START + 1
        st.z = Y_START + 1
        st.O = Y_START + 1
        st.o = Y_START + 1
        st.r = 0
        st.W = Y_START + 1
        st.w = Y_START + 1
        st.I = 0
        st.iI = 0
        st.J = 0
        st.iJ = 0
        st.ij = 0
        st.toll = 0
        st.tally = "   "
        st.tick_tock = False
        st.iZ = Y_START + 1
        st.iz = Y_START + 1
        st.iW = Y_START + 1
        st.iw = Y_START + 1
        st.iO = Y_START + 1
        st.io = Y_START + 1
        st.ir = 0
        st.S = X_PERIOD
        st.T = X_PERIOD
        st.X_scan = Y_START
        st.Y_scan = Y_START
        st.FG = False
        st.signature = False
        st.signal = Decimal('0.0')
        st.FVG = -1
        st.BL = []
        st.BL_type = []
        st.bottomLine = "   "
        st.bL = "   "
        st.count = 0
        st.fvg_anchor_map = {}
        st.lPass = Decimal('0.0')
        st.ilPass = Decimal('0.0')
        st.kPass = Decimal('0.0')
        st.ikPass = Decimal('0.0')
        st.execution_fired = False
        st.projection_path = []
        st.projection_meta = {}
        st.projection_computed_at = None
        st.projection_trigger = ""

        self.ohlcv_history = saved_ohlcv
        st.price = saved_price
        st.Price = saved_Price
        st.iH = saved_iH
        st.iL = saved_iL
        st.tick = saved_tick
        st.on_track_runs = saved_on_track
        st.on_stand_runs = saved_on_stand
        st.signal_history = saved_signal_history
        st.chat_id = saved_chat_id
        st.webapp_user_id = saved_webapp_uid
        st.webapp_username = saved_webapp_uname
        st.webapp_verified = saved_webapp_verified
        st.authoritative_m = 0
        st.authoritative_n = 0
        st.authoritative_h = -1
        st.m_now = 0
        st.n_now = 0
        st.last_kronecker_m = 0
        st.last_kronecker_n = 0
        st.last_kronecker_h = -1
        st.last_provider = saved_provider
        st.last_volume = saved_volume
        st.last_inbound_message_id = saved_inbound_msg
        self._last_kronecker_bar = -1
        self._last_comment_line = saved_comment

        logger.info("ReSet   ")

    def _unify(self, j: int) -> Tuple[Decimal, Decimal]:
        st = self.state
        if j < 1 or len(self.ohlcv_history) < j + 1:
            st.iATR = Decimal('50.0')
            st.iStdDev = Decimal('50.0')
            return st.iATR, st.iStdDev
        end = len(self.ohlcv_history)
        start = end - (j + 1)
        window = self.ohlcv_history[start:end]
        high_prices = [d["high"] for d in window]
        low_prices = [d["low"] for d in window]
        close_prices = [d["close"] for d in window]

        atr_list: List[Decimal] = []
        for i in range(j + 1):
            sub_high = high_prices[:len(high_prices) - i] if i > 0 else high_prices
            sub_low = low_prices[:len(low_prices) - i] if i > 0 else low_prices
            sub_close = close_prices[:len(close_prices) - i] if i > 0 else close_prices
            atr_list.append(atr(sub_high, sub_low, sub_close, j))
        maxATR = max(atr_list) if atr_list else Decimal('0.0')
        minATR = min(atr_list) if atr_list else Decimal('0.0')
        rangeATR = maxATR - minATR
        if rangeATR != Decimal('0.0'):
            st.iATR = Decimal('100.0') * ((atr_list[0] - minATR) / rangeATR)
        else:
            st.iATR = Decimal('50.0')
        if len(st.ATR) <= j:
            st.ATR.extend([Decimal('0.0')] * (j + 1 - len(st.ATR)))
        st.ATR[j] = atr_list[0] if atr_list else Decimal('0.0')

        sd_list: List[Decimal] = []
        for i in range(j + 1):
            sub_close = close_prices[:len(close_prices) - i] if i > 0 else close_prices
            sd_list.append(stddev(sub_close, j))
        maxSD = max(sd_list) if sd_list else Decimal('0.0')
        minSD = min(sd_list) if sd_list else Decimal('0.0')
        rangeSD = maxSD - minSD
        if rangeSD != Decimal('0.0'):
            st.iStdDev = Decimal('100.0') * ((sd_list[0] - minSD) / rangeSD)
        else:
            st.iStdDev = Decimal('50.0')
        if len(st.StdDev) <= j:
            st.StdDev.extend([Decimal('0.0')] * (j + 1 - len(st.StdDev)))
        st.StdDev[j] = sd_list[0] if sd_list else Decimal('0.0')
        return st.iATR, st.iStdDev

    def _normalize(self, j: int) -> None:
        st = self.state
        y = st.y
        # : explicit out-of-bounds guard at the top of the function.
        if j < 1 or len(self.ohlcv_history) < j + 1:
            return
        if j < y + 1 or j > X_PERIOD - 1:
            return
        col_i = j - (y + 1)
        if col_i < 0 or col_i >= (X_PERIOD - Y_START):
            return
        if col_i >= len(st.iA[0]) or col_i >= len(st.cA[0]):
            return
        end = len(self.ohlcv_history)
        window = self.ohlcv_history[end - (j + 1):end]
        close_prices = [d["close"] for d in window]
        open_prices = [d["open"] for d in window]
        high_prices = [d["high"] for d in window]
        low_prices = [d["low"] for d in window]
        volume_data = [d.get("volume", Decimal('0.0')) for d in window]

        if len(close_prices) >= j:
            upper, _, lower = bollinger_bands(close_prices, j, Decimal('2.0'))
            st.Suply = upper
            st.Demand = lower
        if len(close_prices) >= 2:
            upper_prev, _, lower_prev = bollinger_bands(close_prices[:-1], j, Decimal('2.0'))
            st.iSuply = upper_prev
            st.iDemand = lower_prev

        col_c = col_i

        adx_main_list: List[Decimal] = []
        plus_di_list: List[Decimal] = []
        minus_di_list: List[Decimal] = []
        for i in range(j + 1):
            sub_high = high_prices[:len(high_prices) - i] if i > 0 else high_prices
            sub_low = low_prices[:len(low_prices) - i] if i > 0 else low_prices
            sub_close = close_prices[:len(close_prices) - i] if i > 0 else close_prices
            adx_main_list.append(self._compute_adx(sub_high, sub_low, sub_close, j))
            pd, md = self._compute_di(sub_high, sub_low, sub_close, j)
            plus_di_list.append(pd)
            minus_di_list.append(md)
        if adx_main_list:
            all_vals = adx_main_list + plus_di_list + minus_di_list
            maxADX = max(all_vals)
            minADX = min(all_vals)
            rangeADX = maxADX - minADX
            if rangeADX != Decimal('0.0'):
                iADX_val = abs(Decimal('100.0') * ((adx_main_list[0] - minADX) / rangeADX))
                cADX_val = abs(Decimal('100.0') * ((adx_main_list[1] - minADX) / rangeADX)) if len(adx_main_list) > 1 else iADX_val
                st.iA[0][col_i] = iADX_val
                st.cA[0][col_c] = cADX_val

        jSO = int(round(j * 3.0 / 5.0))
        if jSO < 1:
            jSO = 1
        k_stoch, d_stoch = stochastic(high_prices, low_prices, close_prices, j, 3, jSO)
        st.iA[1][col_i] = (k_stoch + d_stoch) / Decimal('2.0')
        if len(close_prices) > 1:
            k_p, d_p = stochastic(high_prices[:-1], low_prices[:-1], close_prices[:-1], j, 3, jSO)
            st.cA[1][col_c] = (k_p + d_p) / Decimal('2.0')

        rvi_list: List[Decimal] = []
        for i in range(j + 1):
            sub_open = open_prices[:len(open_prices) - i] if i > 0 else open_prices
            sub_close = close_prices[:len(close_prices) - i] if i > 0 else close_prices
            rvi_list.append(self._compute_rvi(sub_open, sub_close, j))
        if rvi_list:
            maxRVI = max(rvi_list)
            minRVI = min(rvi_list)
            rangeRVI = maxRVI - minRVI
            if rangeRVI != Decimal('0.0'):
                st.iA[2][col_i] = Decimal('100.0') * ((rvi_list[0] - minRVI) / rangeRVI)
                st.cA[2][col_c] = Decimal('100.0') * ((rvi_list[1] - minRVI) / rangeRVI) if len(rvi_list) > 1 else st.iA[2][col_i]

        ac_list: List[Decimal] = []
        for i in range(j + 1):
            sub_high = high_prices[:len(high_prices) - i] if i > 0 else high_prices
            sub_low = low_prices[:len(low_prices) - i] if i > 0 else low_prices
            sub_close = close_prices[:len(close_prices) - i] if i > 0 else close_prices
            ac_list.append(abs(self._compute_ac(sub_high, sub_low, sub_close, j)))
        if ac_list:
            maxAC = max(ac_list)
            minAC = min(ac_list)
            rangeAC = maxAC - minAC
            if rangeAC != Decimal('0.0'):
                st.iA[3][col_i] = abs(Decimal('100.0') * ((ac_list[0] - minAC) / rangeAC))
                st.cA[3][col_c] = abs(Decimal('100.0') * ((ac_list[1] - minAC) / rangeAC)) if len(ac_list) > 1 else st.iA[3][col_i]

        force_list: List[Decimal] = []
        for i in range(j + 1):
            sub_close = close_prices[:len(close_prices) - i] if i > 0 else close_prices
            sub_vol = volume_data[:len(volume_data) - i] if i > 0 else volume_data
            force_list.append(self._compute_force(sub_close, sub_vol, j))
        if force_list:
            maxForce = max(force_list)
            minForce = min(force_list)
            rangeForce = maxForce - minForce
            if rangeForce != Decimal('0.0'):
                st.iA[4][col_i] = Decimal('100.0') * ((force_list[0] - minForce) / rangeForce)
                st.cA[4][col_c] = Decimal('100.0') * ((force_list[1] - minForce) / rangeForce) if len(force_list) > 1 else st.iA[4][col_i]

        obv_list: List[Decimal] = []
        for i in range(j + 1):
            sub_close = close_prices[:len(close_prices) - i] if i > 0 else close_prices
            sub_vol = volume_data[:len(volume_data) - i] if i > 0 else volume_data
            obv_list.append(self._compute_obv(sub_close, sub_vol))
        if obv_list:
            maxOBV = max(obv_list)
            minOBV = min(obv_list)
            rangeOBV = maxOBV - minOBV
            if rangeOBV != Decimal('0.0'):
                st.iA[5][col_i] = Decimal('100.0') * ((obv_list[0] - minOBV) / rangeOBV)
                st.cA[5][col_c] = Decimal('100.0') * ((obv_list[1] - minOBV) / rangeOBV) if len(obv_list) > 1 else st.iA[5][col_i]

        ad_list: List[Decimal] = []
        for i in range(j + 1):
            sub_high = high_prices[:len(high_prices) - i] if i > 0 else high_prices
            sub_low = low_prices[:len(low_prices) - i] if i > 0 else low_prices
            sub_close = close_prices[:len(close_prices) - i] if i > 0 else close_prices
            sub_vol = volume_data[:len(volume_data) - i] if i > 0 else volume_data
            ad_list.append(self._compute_ad(sub_high, sub_low, sub_close, sub_vol))
        if ad_list:
            maxAD = max(ad_list)
            minAD = min(ad_list)
            rangeAD = maxAD - minAD
            if rangeAD != Decimal('0.0'):
                st.iA[6][col_i] = Decimal('100.0') * ((ad_list[0] - minAD) / rangeAD)
                st.cA[6][col_c] = Decimal('100.0') * ((ad_list[1] - minAD) / rangeAD) if len(ad_list) > 1 else st.iA[6][col_i]

        mfi_list: List[Decimal] = []
        for i in range(j + 1):
            sub_high = high_prices[:len(high_prices) - i] if i > 0 else high_prices
            sub_low = low_prices[:len(low_prices) - i] if i > 0 else low_prices
            sub_close = close_prices[:len(close_prices) - i] if i > 0 else close_prices
            sub_vol = volume_data[:len(volume_data) - i] if i > 0 else volume_data
            mfi_list.append(self._compute_mfi(sub_high, sub_low, sub_close, sub_vol, j))
        if mfi_list:
            maxMFI = max(mfi_list)
            minMFI = min(mfi_list)
            rangeMFI = maxMFI - minMFI
            if rangeMFI != Decimal('0.0'):
                st.iA[7][col_i] = Decimal('100.0') * ((mfi_list[0] - minMFI) / rangeMFI)
                st.cA[7][col_c] = Decimal('100.0') * ((mfi_list[1] - minMFI) / rangeMFI) if len(mfi_list) > 1 else st.iA[7][col_i]

        mom_list: List[Decimal] = []
        for i in range(j + 1):
            sub_close = close_prices[:len(close_prices) - i] if i > 0 else close_prices
            mom_list.append(self._compute_momentum(sub_close, j))
        if mom_list:
            maxMOM = max(mom_list)
            minMOM = min(mom_list)
            rangeMOM = maxMOM - minMOM
            if rangeMOM != Decimal('0.0'):
                st.iA[8][col_i] = Decimal('100.0') * ((mom_list[0] - minMOM) / rangeMOM)
                st.cA[8][col_c] = Decimal('100.0') * ((mom_list[1] - minMOM) / rangeMOM) if len(mom_list) > 1 else st.iA[8][col_i]

        dem_list: List[Decimal] = []
        for i in range(j + 1):
            sub_high = high_prices[:len(high_prices) - i] if i > 0 else high_prices
            sub_low = low_prices[:len(low_prices) - i] if i > 0 else low_prices
            dem_list.append(self._compute_demarker(sub_high, sub_low, j))
        if dem_list:
            maxDM = max(dem_list)
            minDM = min(dem_list)
            rangeDM = maxDM - minDM
            if rangeDM != Decimal('0.0'):
                st.iA[9][col_i] = Decimal('100.0') * ((dem_list[0] - minDM) / rangeDM)
                st.cA[9][col_c] = Decimal('100.0') * ((dem_list[1] - minDM) / rangeDM) if len(dem_list) > 1 else st.iA[9][col_i]

        wpr_now = self._compute_wpr(high_prices, low_prices, close_prices, j) + Decimal('100.0')
        st.iA[10][col_i] = wpr_now
        if len(close_prices) > 1:
            wpr_prev = self._compute_wpr(high_prices[:-1], low_prices[:-1], close_prices[:-1], j) + Decimal('100.0')
            st.cA[10][col_c] = wpr_prev

        cci_list: List[Decimal] = []
        for i in range(j + 1):
            sub_high = high_prices[:len(high_prices) - i] if i > 0 else high_prices
            sub_low = low_prices[:len(low_prices) - i] if i > 0 else low_prices
            sub_close = close_prices[:len(close_prices) - i] if i > 0 else close_prices
            cci_list.append(self._compute_cci(sub_high, sub_low, sub_close, j))
        if cci_list:
            maxCCI = max(cci_list)
            minCCI = min(cci_list)
            rangeCCI = maxCCI - minCCI
            if rangeCCI != Decimal('0.0'):
                st.iA[11][col_i] = Decimal('100.0') * ((cci_list[0] - minCCI) / rangeCCI)
                st.cA[11][col_c] = Decimal('100.0') * ((cci_list[1] - minCCI) / rangeCCI) if len(cci_list) > 1 else st.iA[11][col_i]

        rsi_list: List[Decimal] = []
        for i in range(j + 1):
            sub_close = close_prices[:len(close_prices) - i] if i > 0 else close_prices
            rsi_list.append(rsi(sub_close, j))
        if rsi_list:
            maxRSI = max(rsi_list)
            minRSI = min(rsi_list)
            rangeRSI = maxRSI - minRSI
            if rangeRSI != Decimal('0.0'):
                st.iA[12][col_i] = Decimal('100.0') * ((rsi_list[0] - minRSI) / rangeRSI)
                st.cA[12][col_c] = Decimal('100.0') * ((rsi_list[1] - minRSI) / rangeRSI) if len(rsi_list) > 1 else st.iA[12][col_i]

        kIHK = int(round(j / 2.0))
        tIHK = int(round((kIHK + 1.0) / 3.0))
        if kIHK < 1:
            kIHK = 1
        if tIHK < 1:
            tIHK = 1
        ihk_curr = ichimoku(high_prices, low_prices, close_prices, tIHK, kIHK, j)
        ssa: List[Decimal] = []
        ssb: List[Decimal] = []
        chikou: List[Decimal] = []
        tenkan_list: List[Decimal] = []
        kijun_list: List[Decimal] = []
        for i in range(j + 1):
            sub_high = high_prices[:len(high_prices) - i] if i > 0 else high_prices
            sub_low = low_prices[:len(low_prices) - i] if i > 0 else low_prices
            sub_close = close_prices[:len(close_prices) - i] if i > 0 else close_prices
            if len(sub_close) < j:
                continue
            ihk_i = ichimoku(sub_high, sub_low, sub_close, tIHK, kIHK, j)
            ssa.append(ihk_i["senkou_a"])
            ssb.append(ihk_i["senkou_b"])
            tenkan_list.append(ihk_i["tenkan"])
            kijun_list.append(ihk_i["kijun"])
            c_idx = len(sub_close) - 1 - 26
            if c_idx >= 0:
                chikou.append(sub_close[c_idx])
        all_ihk: List[Decimal] = []
        all_ihk.extend(ssa)
        all_ihk.extend(ssb)
        all_ihk.extend(chikou)
        all_ihk.extend(tenkan_list)
        all_ihk.extend(kijun_list)
        if all_ihk:
            maxIHK = max(all_ihk)
            minIHK = min(all_ihk)
            rangeIHK = maxIHK - minIHK
            if rangeIHK != Decimal('0.0'):
                st.iIHKk = Decimal('100.0') * ((ihk_curr["kijun"] - minIHK) / rangeIHK)
                st.iIHKt = Decimal('100.0') * ((ihk_curr["tenkan"] - minIHK) / rangeIHK)
        else:
            st.iIHKk = ihk_curr["kijun"]
            st.iIHKt = ihk_curr["tenkan"]

    def _compute_adx(self, high, low, close, period: int) -> Decimal:
        if len(close) < 2 * period + 1 or period <= 0:
            return Decimal('50.0')
        n = len(close)
        trs_fwd: List[Decimal] = []
        pdm_fwd: List[Decimal] = []
        mdm_fwd: List[Decimal] = []
        start = n - 2 * period
        if start < 1:
            start = 1
        for i in range(start, n):
            tr = max(
                high[i] - low[i],
                abs(high[i] - close[i - 1]),
                abs(low[i] - close[i - 1])
            )
            trs_fwd.append(tr)
            up_move = high[i] - high[i - 1]
            dn_move = low[i - 1] - low[i]
            pdm_fwd.append(up_move if up_move > dn_move and up_move > 0 else Decimal('0.0'))
            mdm_fwd.append(dn_move if dn_move > up_move and dn_move > 0 else Decimal('0.0'))
        if len(trs_fwd) < 2 * period:
            return Decimal('50.0')
        atr_k = sum(trs_fwd[:period]) / Decimal(period)
        plus_dm_k = sum(pdm_fwd[:period]) / Decimal(period)
        minus_dm_k = sum(mdm_fwd[:period]) / Decimal(period)
        dx_series: List[Decimal] = []
        plus_di = (Decimal('100.0') * plus_dm_k / atr_k) if atr_k != Decimal('0.0') else Decimal('0.0')
        minus_di = (Decimal('100.0') * minus_dm_k / atr_k) if atr_k != Decimal('0.0') else Decimal('0.0')
        di_sum = plus_di + minus_di
        if di_sum == Decimal('0.0'):
            dx_series.append(Decimal('0.0'))
        else:
            dx_series.append(Decimal('100.0') * abs(plus_di - minus_di) / di_sum)
        for k in range(period, len(trs_fwd)):
            atr_k = (atr_k * Decimal(period - 1) + trs_fwd[k]) / Decimal(period)
            plus_dm_k = (plus_dm_k * Decimal(period - 1) + pdm_fwd[k]) / Decimal(period)
            minus_dm_k = (minus_dm_k * Decimal(period - 1) + mdm_fwd[k]) / Decimal(period)
            plus_di = (Decimal('100.0') * plus_dm_k / atr_k) if atr_k != Decimal('0.0') else Decimal('0.0')
            minus_di = (Decimal('100.0') * minus_dm_k / atr_k) if atr_k != Decimal('0.0') else Decimal('0.0')
            di_sum = plus_di + minus_di
            if di_sum == Decimal('0.0'):
                dx_series.append(Decimal('0.0'))
            else:
                dx_series.append(Decimal('100.0') * abs(plus_di - minus_di) / di_sum)
        if len(dx_series) < period:
            return dx_series[-1] if dx_series else Decimal('50.0')
        adx_val = sum(dx_series[:period]) / Decimal(period)
        for k in range(period, len(dx_series)):
            adx_val = (adx_val * Decimal(period - 1) + dx_series[k]) / Decimal(period)
        return adx_val

    def _compute_di(self, high, low, close, period: int) -> Tuple[Decimal, Decimal]:
        if len(close) < period + 1 or period <= 0:
            return Decimal('50.0'), Decimal('50.0')
        trs: List[Decimal] = []
        plus_dm: List[Decimal] = []
        minus_dm: List[Decimal] = []
        for i in range(1, period + 1):
            tr = max(
                high[-i] - low[-i],
                abs(high[-i] - close[-i - 1]),
                abs(low[-i] - close[-i - 1])
            )
            trs.append(tr)
            up_move = high[-i] - high[-i - 1]
            dn_move = low[-i - 1] - low[-i]
            plus_dm.append(up_move if up_move > dn_move and up_move > 0 else Decimal('0.0'))
            minus_dm.append(dn_move if dn_move > up_move and dn_move > 0 else Decimal('0.0'))
        if len(trs) < period:
            return Decimal('50.0'), Decimal('50.0')
        atr_k = sum(trs[:period]) / Decimal(period)
        plus_dm_k = sum(plus_dm[:period]) / Decimal(period)
        minus_dm_k = sum(minus_dm[:period]) / Decimal(period)
        plus_di = (Decimal('100.0') * plus_dm_k / atr_k) if atr_k != Decimal('0.0') else Decimal('0.0')
        minus_di = (Decimal('100.0') * minus_dm_k / atr_k) if atr_k != Decimal('0.0') else Decimal('0.0')
        return plus_di, minus_di

    def _compute_rvi(self, open_prices, close_prices, period: int) -> Decimal:
        if len(close_prices) < period + 3 or period <= 0:
            return Decimal('50.0')
        n = len(close_prices)
        num_series: List[Decimal] = []
        den_series: List[Decimal] = []
        for i in range(3, n):
            num_i = (
                (close_prices[i] - open_prices[i])
                + Decimal('2.0') * (close_prices[i - 1] - open_prices[i - 1])
                + Decimal('2.0') * (close_prices[i - 2] - open_prices[i - 2])
                + (close_prices[i - 3] - open_prices[i - 3])
            )
            den_i = (
                abs(close_prices[i] - open_prices[i])
                + Decimal('2.0') * abs(close_prices[i - 1] - open_prices[i - 1])
                + Decimal('2.0') * abs(close_prices[i - 2] - open_prices[i - 2])
                + abs(close_prices[i - 3] - open_prices[i - 3])
            )
            num_series.append(num_i)
            den_series.append(den_i)
        if len(num_series) < period:
            return Decimal('50.0')
        num_sma = sum(num_series[-period:]) / Decimal(period)
        den_sma = sum(den_series[-period:]) / Decimal(period)
        if den_sma == Decimal('0.0'):
            return Decimal('50.0')
        return num_sma / den_sma

    def _compute_ac(self, high, low, close, period: int) -> Decimal:
        if len(close) < 40 or period <= 0:
            return Decimal('0.0')
        window = len(close)
        if window < 40:
            return Decimal('0.0')
        median = [(high[i] + low[i]) / Decimal('2.0') for i in range(window)]
        def sma_local(data, p):
            if len(data) < p or p <= 0:
                return Decimal('0.0')
            return sum(data[-p:]) / Decimal(p)
        ao_now = sma_local(median, 5) - sma_local(median, 34)
        ao_series: List[Decimal] = []
        for i in range(min(5, len(median))):
            sub = median[:len(median) - i] if i > 0 else median
            ao_series.append(sma_local(sub, 5) - sma_local(sub, 34))
        return ao_now - sma_local(ao_series, 5)

    def _compute_force(self, close, volume, period: int) -> Decimal:
        if len(close) < period + 1 or period <= 0:
            return Decimal('0.0')
        forces = []
        for i in range(1, period + 1):
            forces.append(volume[-i] * (close[-i] - close[-i - 1]))
        return sum(forces) / Decimal(period)

    def _compute_obv(self, close, volume) -> Decimal:
        if len(close) < 2:
            return Decimal('0.0')
        obv = Decimal('0.0')
        for i in range(1, len(close)):
            if close[i] > close[i - 1]:
                obv += volume[i] if i < len(volume) else Decimal('0.0')
            elif close[i] < close[i - 1]:
                obv -= volume[i] if i < len(volume) else Decimal('0.0')
        return obv

    def _compute_ad(self, high, low, close, volume) -> Decimal:
        if len(close) < 2:
            return Decimal('0.0')
        ad = Decimal('0.0')
        for i in range(len(close)):
            hl = high[i] - low[i]
            if hl > Decimal('0.0'):
                mfv = ((close[i] - low[i]) - (high[i] - close[i])) / hl * (volume[i] if i < len(volume) else Decimal('0.0'))
                ad += mfv
        return ad

    def _compute_mfi(self, high, low, close, volume, period: int) -> Decimal:
        if len(close) < period + 1 or period <= 0:
            return Decimal('50.0')
        pos_flow, neg_flow = Decimal('0.0'), Decimal('0.0')
        for i in range(1, period + 1):
            tp = (high[-i] + low[-i] + close[-i]) / Decimal('3.0')
            tp_prev = (high[-i - 1] + low[-i - 1] + close[-i - 1]) / Decimal('3.0')
            mf = tp * volume[-i]
            if tp > tp_prev:
                pos_flow += mf
            elif tp < tp_prev:
                neg_flow += mf
        if neg_flow == Decimal('0.0'):
            if pos_flow == Decimal('0.0'):
                return Decimal('50.0')
            return Decimal('100.0')
        mr = pos_flow / neg_flow
        return Decimal('100.0') - (Decimal('100.0') / (Decimal('1.0') + mr))

    def _compute_momentum(self, close, period: int) -> Decimal:
        if len(close) < period + 1 or period <= 0:
            return Decimal('0.0')
        return close[-1] - close[-period - 1]

    def _compute_demarker(self, high, low, period: int) -> Decimal:
        if len(high) < period + 1 or period <= 0:
            return Decimal('50.0')
        demax, demin = Decimal('0.0'), Decimal('0.0')
        for i in range(1, period + 1):
            if high[-i] > high[-i - 1]:
                demax += high[-i] - high[-i - 1]
            if low[-i] < low[-i - 1]:
                demin += low[-i - 1] - low[-i]
        total = demax + demin
        if total == Decimal('0.0'):
            return Decimal('50.0')
        return Decimal('100.0') * demax / total

    def _compute_wpr(self, high, low, close, period: int) -> Decimal:
        if len(close) < period or period <= 0:
            return Decimal('0.0')
        hh = max(high[-period:])
        ll = min(low[-period:])
        rng = hh - ll
        if rng == Decimal('0.0'):
            return Decimal('0.0')
        return Decimal('-100.0') * (hh - close[-1]) / rng

    def _compute_cci(self, high, low, close, period: int) -> Decimal:
        if len(close) < period or period <= 0:
            return Decimal('0.0')
        tp = [(high[-i] + low[-i] + close[-i]) / Decimal('3.0') for i in range(1, period + 1)]
        sma_tp = sum(tp) / Decimal(period)
        mad = sum(abs(x - sma_tp) for x in tp) / Decimal(period)
        if mad == Decimal('0.0'):
            return Decimal('0.0')
        return (tp[0] - sma_tp) / (Decimal('0.015') * mad)

    # ========================================================================
    # _M() and _N() — ADX COUNTED EXACTLY ONCE
    # ========================================================================
    # M()/N() count ADX (iA[0]) exactly once: inside the
    # `for i in range(13)` loop. m and n
    # can reach at most 14 (13 loop votes plus one Ichimoku vote),
    # and the δ(m−n−2)=1 gate fires when m - n - 2 equals 0.
    # ========================================================================
    # m/n: 13 loop votes plus one Ichimoku vote. Max is 14.
    # Effective thresholds: m on > 208/3 (69.333...), n on < 92/3 (30.666...).
    def _M(self, j: int) -> int:
        st = self.state
        y = st.y
        m = 0
        idx_i = j - (y + 1)
        idx_c = idx_i
        if idx_i < 0 or idx_i >= len(st.iA[0]):
            return 0
        if idx_c < 0 or idx_c >= len(st.cA[0]):
            idx_c = idx_i
        hh_val = st.HH[idx_i] if idx_i < len(st.HH) else Decimal('0.0')
        for i in range(13):
            iA_val = st.iA[i][idx_i]
            cA_val = st.cA[i][idx_c]
            kA_val = st.kA[i][idx_c]
            # : ULP-safe comparison via _cmp_frac (exact rational).
            if st.Price > hh_val:
                if (_cmp_frac(iA_val, F_PLUS_GF_FRAC) > 0) or (cA_val < kA_val):
                    m += 1
            elif st.price > hh_val:
                if (_cmp_frac(iA_val, F_PLUS_GF_FRAC) > 0) or (iA_val < kA_val):
                    m += 1
            elif _cmp_frac(iA_val, F_PLUS_GF_FRAC) > 0:
                m += 1
        if (_cmp_frac(st.iIHKt, F_PLUS_GF_FRAC) > 0) and (_cmp_frac(st.iIHKk, F_PLUS_GF_FRAC) > 0):
            m += 1
        if st.Price > hh_val:
            for i in range(13):
                if idx_c < len(st.kA[i]) and idx_c < len(st.cA[i]):
                    st.kA[i][idx_c] = st.cA[i][idx_c]
            if idx_i < len(st.HH):
                st.HH[idx_i] = st.Price
        return m

    def _N(self, j: int) -> int:
        st = self.state
        y = st.y
        n = 0
        idx_i = j - (y + 1)
        idx_c = idx_i
        if idx_i < 0 or idx_i >= len(st.iA[0]):
            return 0
        if idx_c < 0 or idx_c >= len(st.cA[0]):
            idx_c = idx_i
        ll_val = st.LL[idx_i] if idx_i < len(st.LL) else Decimal('0.0')
        for i in range(13):
            iA_val = st.iA[i][idx_i]
            cA_val = st.cA[i][idx_c]
            lA_val = st.lA[i][idx_c]
            # : ULP-safe comparison via _cmp_frac (exact rational).
            if st.Price < ll_val:
                if (_cmp_frac(iA_val, G_MINUS_GF_FRAC) < 0) or (cA_val > lA_val):
                    n += 1
            elif st.price < ll_val:
                if (_cmp_frac(iA_val, G_MINUS_GF_FRAC) < 0) or (iA_val > lA_val):
                    n += 1
            elif _cmp_frac(iA_val, G_MINUS_GF_FRAC) < 0:
                n += 1
        if (_cmp_frac(st.iIHKt, G_MINUS_GF_FRAC) < 0) and (_cmp_frac(st.iIHKk, G_MINUS_GF_FRAC) < 0):
            n += 1
        if st.Price < ll_val:
            for i in range(13):
                if idx_c < len(st.lA[i]) and idx_c < len(st.cA[i]):
                    st.lA[i][idx_c] = st.cA[i][idx_c]
            if idx_i < len(st.LL):
                st.LL[idx_i] = st.Price
        return n

    def _H(self, j: int) -> None:
        st = self.state
        idx = j - (st.y + 1)
        if idx < 0 or idx >= len(st.k):
            return
        m = self._M(j)
        st.m = m
        st.k[idx] = (m >= 12)
        st.authoritative_m = m
        st.authoritative_h = j
        st.last_kronecker_m = m
        st.last_kronecker_h = j
        st.m_now = m
        st.m = 0
        if st.k[idx]:
            logger.info(f"🔺 H() set k[{idx}] = True (m={m} >= 12) at bar j={j}")

    def _L(self, j: int) -> None:
        st = self.state
        idx = j - (st.y + 1)
        if idx < 0 or idx >= len(st.l):
            return
        n = self._N(j)
        st.n = n
        st.l[idx] = (n >= 12)
        st.authoritative_n = n
        st.authoritative_h = j
        st.last_kronecker_n = n
        st.last_kronecker_h = j
        st.n_now = n
        st.n = 0
        if st.l[idx]:
            logger.info(f"🔻 L() set l[{idx}] = True (n={n} >= 12) at bar j={j}")

    def _F(self, j: int, iH: Decimal, iL: Decimal) -> None:
        st = self.state
        y = st.y
        idx = j - (y + 1)
        if idx < 0 or idx >= len(st.k):
            return
        self._normalize(j)
        st.k[idx] = False
        st.l[idx] = False
        st.HH[idx] = iH
        st.LL[idx] = iL
        st.Premium[idx] = iH
        st.Discount[idx] = iL
        idx_c = idx
        if idx_c < 0 or idx_c >= len(st.cA[0]):
            idx_c = idx
        for i in range(13):
            if idx_c < len(st.kA[i]) and idx_c < len(st.cA[i]):
                st.kA[i][idx_c] = st.cA[i][idx_c]
                st.lA[i][idx_c] = st.cA[i][idx_c]
        if st.R and st.FG:
            target_size = X_PERIOD - Y_START
            while len(st.U) < target_size:
                st.U.append(False)
            if idx < len(st.U):
                st.U[idx] = True
            V = 0
            for i in range(y + 1, X_PERIOD):
                ui = i - (y + 1)
                if 0 <= ui < len(st.U) and st.U[ui]:
                    V += 1
            if V == target_size:
                st.R = False

    def _G(self) -> None:
        st = self.state
        y = st.y
        if len(self.ohlcv_history) < 2:
            return
        H = self.ohlcv_history[-2]["high"]
        L = self.ohlcv_history[-2]["low"]
        for j in range(y + 1, st.h + 1):
            if j == X_PERIOD:
                break
            idx = j - (y + 1)
            if idx < 0 or idx >= len(st.k):
                continue
            st.k[idx] = False
            st.l[idx] = False
            st.HH[idx] = H
            st.LL[idx] = L
            st.Premium[idx] = H
            st.Discount[idx] = L
            idx_c = idx
            if idx_c < 0 or idx_c >= len(st.cA[0]):
                idx_c = idx
            for i in range(13):
                if idx_c < len(st.kA[i]) and idx_c < len(st.cA[i]):
                    st.kA[i][idx_c] = st.cA[i][idx_c]
                    st.lA[i][idx_c] = st.cA[i][idx_c]

    def _J(self) -> None:
        st = self.state
        if st.I == st.iZ:
            st.J = st.iW
        elif st.I == st.iW:
            st.J = st.iZ
        if st.iI == st.iz:
            st.iJ = st.iw
        elif st.iI == st.iw:
            st.iJ = st.iz

    def _O(self, inp: int, inp0: int, inp1: int, inp2: bool, inp3: bool) -> bool:
        st = self.state
        y = st.y
        idx = inp0 - (y + 1)
        if idx < 0 or idx >= len(st.Regime):
            return inp3
        regime = st.Regime[idx]
        is_range = (regime == "sRange" or regime == "tRange")
        if (inp < inp1) and is_range:
            return inp3
        if (regime != "sRange") and (regime != "tRange"):
            return not inp3
        return not inp3

    def _R(self, j: int) -> None:
        st = self.state
        if j <= st.J:
            st.O = j
            st.iO = j
        if (j > st.J) and (j < st.r):
            st.O = j
            st.iO = j
            st.r = j
        elif j > st.J:
            st.r = j
        if j <= st.iJ:
            st.o = j
            st.io = j
        if (j > st.iJ) and (j < st.ir):
            st.o = j
            st.io = j
            st.ir = j
        elif j > st.iJ:
            st.ir = j

    def _KC(self) -> None:
        st = self.state
        if st.E != Decimal('0.0') and (not st.A) and (not st.B) and st.v and st.signal < st.E:
            st.invert = not st.KC
        if st.D != Decimal('0.0') and (not st.B) and (not st.A) and st.u and st.signal > st.D:
            st.invert = not st.KC

    def _on_hold(self, inp: int, inp0: str, inp1: str) -> bool:
        st = self.state
        idx = inp - (st.y + 1)
        if idx < 0 or idx >= len(st.Regime):
            return False
        return st.Regime[idx] == inp0 or st.Regime[idx] == inp1

    def _on_fire(self, inp: int, inp0: str, inp1: str) -> bool:
        st = self.state
        idx = inp - (st.y + 1)
        if idx < 0 or idx >= len(st.Regime):
            return False
        return st.Regime[idx] != inp0 and st.Regime[idx] != inp1

    def _on_point(self) -> None:
        st = self.state
        y = st.y
        for j in range(y + 1, X_PERIOD):
            idx = j - (y + 1)
            if idx < 0 or idx >= len(st.Regime):
                break
            self._unify(j)
            self._normalize(j)
            if st.iStdDev < Decimal('50.0') and st.iATR > Decimal('50.0'):
                if st.Regime[idx] != "Stable":
                    self._H(j)
                    self._L(j)
                    if self._on_fire(j, "sVolatile", "tVolatile"):
                        st.Regime[idx] = "sVolatile"
            elif st.iStdDev < Decimal('50.0') and st.iATR < Decimal('50.0'):
                if st.Regime[idx] != "Stable":
                    self._R(j)
                    self._H(j)
                    self._L(j)
                    if self._on_fire(j, "sRange", "tRange"):
                        st.Regime[idx] = "sRange"
            elif self._on_fire(j, "sTrend", "tTrend"):
                st.Regime[idx] = "sTrend"

    def _on_bar(self) -> None:
        st = self.state
        y = st.y
        for j in range(y + 1, X_PERIOD):
            idx = j - (y + 1)
            if idx < 0 or idx >= len(st.Regime):
                break
            self._unify(j)
            self._normalize(j)
            if st.iStdDev < Decimal('50.0') and st.iATR > Decimal('50.0'):
                if st.Regime[idx] != "Stable":
                    if st.Regime[idx] != "tVolatile":
                        self._F(j, st.iH, st.iL)
                        self._H(j)
                        self._L(j)
                        st.Regime[idx] = "tVolatile"
            elif st.iStdDev < Decimal('50.0') and st.iATR < Decimal('50.0'):
                if st.Regime[idx] != "Stable":
                    self._R(j)
                    self._H(j)
                    self._L(j)
                    if st.Regime[idx] != "tRange":
                        self._F(j, st.iH, st.iL)
                        st.Regime[idx] = "tRange"
            elif (st.Regime[idx] != "tTrend" and st.Regime[idx] != "sTrend"
                  and st.LL[idx] < st.Discount[idx]
                  and st.HH[idx] > st.Premium[idx]):
                st.Regime[idx] = "Stable"
            else:
                if st.Regime[idx] != "tTrend":
                    self._F(j, st.iH, st.iL)
                    st.Regime[idx] = "tTrend"

        if len(self.ohlcv_history) >= y + 1:
            close_prices = [d["close"] for d in self.ohlcv_history[-y - 1:]]
            st.Stock, _, st.Sale = bollinger_bands(close_prices, y)
            if len(close_prices) > 1:
                st.iStock, _, st.iSale = bollinger_bands(close_prices[:-1], y)
            else:
                st.iStock = st.Stock
                st.iSale = st.Sale

        if len(self.ohlcv_history) >= 3:
            st.iopen = self.ohlcv_history[-3]["open"]
            st.iPrice = self.ohlcv_history[-3]["close"]
        elif len(self.ohlcv_history) >= 2:
            st.iopen = self.ohlcv_history[-2]["open"]
            st.iPrice = self.ohlcv_history[-2]["close"]
        elif len(self.ohlcv_history) >= 1:
            st.iopen = self.ohlcv_history[-1]["open"]
            st.iPrice = self.ohlcv_history[-1]["close"]

        st.lPass = st.Price if st.Price < st.open else st.open
        st.ilPass = st.iPrice if st.iPrice < st.iopen else st.iopen
        st.kPass = st.Price if st.Price > st.open else st.open
        st.ikPass = st.iPrice if st.iPrice > st.iopen else st.iopen

        self._execute_kronecker_block()

    # ========================================================================
    # THE EXECUTION LAYER — FF-EXACT
    # ========================================================================
    # The FF's execution layer is the toll-gate and the count-gate in
    # OnTick(), each running its own independent `if` chain. The port
    # preserves:
    #
    #   (a) The FF's `dime = mem;` pre-stamp at the top of each subblock.
    #       The pre-stamp. The `else if((mem==1)||(dime==1))` and
    #       `else if((mem==0)||(dime==0))` branches READ the pre-stamp.
    #       Without it,  read a stale `dime` left over from the
    #       previous tick's _on_gaurd(0) — which may not have run at all
    #       if the previous tick was still in tick_tock.
    #
    #   (b) The independence of the toll block and the count block. This
    #       In the FF both are `if` statements in the same tick;
    #       both fire if both counters are 1.  short-circuited
    #       after the toll block, skipping the count block. The port no
    #       longer returns early.
    #
    #   (c) The FF's reset placement. The FF's
    #       `toll = 0; tally = ""; count = 0; tally = ""; signal = 0;
    #       GF = true; signature = true;` are on the `signal = 0;` line
    #       at the end of each subblock. The helpers own the reset. The
    #       caller does not touch st.toll / st.count / st.signal /
    #       st.tally / st.GF / st.signature.
    #
    #   (d) The frozen commission. The FF computes
    #       `com = Commssion * Point` once at OnInit. The trigger
    #       `price >= signal + com` and `price <= signal - com` use the
    #       frozen value, not a dynamic recomputation.
    # ========================================================================
    def _execute_kronecker_block(self) -> None:
        st = self.state
        fg = ""
        if st.signal == Decimal('0.0'):
            return
        if st.price <= Decimal('0.0') or st.Price <= Decimal('0.0'):
            return

        # : frozen commission (FF's `com` constant).
        com_price = self._com_price_frozen

        if st.price >= st.signal + com_price:
            # FF's Alert("Long:", price) emitted as a UI toast + push.
            logger.info(f"🔵 Long: {st.price}")
            _emit_alert("long", {
                "price": str(st.price),
                "tick": int(st.tick),
                "h": int(st.h),
            })
            if st.count == 0 and st.tally == "Sell":
                st.count += 1
            st.tally = "Buy"
        if st.price <= st.signal - com_price:
            # FF's Alert("Short:", price) emitted as a UI toast + push.
            logger.info(f"🔴 Short: {st.price}")
            _emit_alert("short", {
                "price": str(st.price),
                "tick": int(st.tick),
                "h": int(st.h),
            })
            if st.count == 0 and st.tally == "Buy":
                st.count += 1
            st.tally = "Sell"

        if st.tick_tock:
            return

        hh_idx = MIN_PERIOD - (st.y + 1)
        ll_idx = MIN_PERIOD - (st.y + 1)
        hh_anchor = st.HH[hh_idx] if 0 <= hh_idx < len(st.HH) else Decimal('0.0')
        ll_anchor = st.LL[ll_idx] if 0 <= ll_idx < len(st.LL) else Decimal('0.0')

        bullish_coherence = (
            (
                (st.Price > st.signal)
                or (st.Price > st.ikPass)
                or (st.price > st.kPass)
            )
            and (
                (
                    st.iC == st.Cc
                    and st.Price > hh_anchor
                )
                or (
                    st.jC == st.Cc
                    and st.Price >= ll_anchor
                    and (
                        (st.open >= st.Stock)
                        or (st.Price >= st.Stock)
                        or (st.open >= st.iStock)
                        or (st.Price >= st.iStock)
                    )
                )
            )
        )
        if bullish_coherence:
            logger.info(f"🟢 Buy: {st.price}")
            if st.toll == 0 and st.tally == "Sell":
                st.toll += 1
            if st.Price > st.signal:
                fg = "Up"
            st.tally = "Buy"

        bearish_coherence = (
            (
                (st.Price < st.signal)
                or (st.Price < st.ilPass)
                or (st.price < st.lPass)
            )
            and (
                (
                    st.jC == st.Cc
                    and st.Price < ll_anchor
                )
                or (
                    st.iC == st.Cc
                    and st.Price <= hh_anchor
                    and (
                        (st.open <= st.Sale)
                        or (st.Price <= st.Sale)
                        or (st.open <= st.iSale)
                        or (st.Price <= st.iSale)
                    )
                )
            )
        )
        if bearish_coherence:
            logger.info(f"🔴 Sell: {st.price}")
            if st.toll == 0 and st.tally == "Buy":
                st.toll += 1
            if st.Price < st.signal:
                fg = "Down"
            st.tally = "Sell"

        # : both the toll block and the count block are evaluated in
        # the same tick. No early return. The FF's `if` order is:
        #   toll-buy, toll-sell, count-buy, count-sell.
        # The helpers own the reset of st.toll, st.count,
        # st.signal, st.tally, st.GF, st.signature, and the subblock body's
        # own `signal = 0;` line is reproduced inside each helper.

        # Toll and count are evaluated in the same tick, in order:
        # toll-buy, toll-sell, count-buy, count-sell. No early return.
        # Snapshot toll/count/tally/fg at entry: each helper resets
        # toll, count, signal, tally, and GF at its end, so the later
        # branches must be decided from the snapshot, not from the
        # post-dispatch state.
        snap_toll = st.toll
        snap_count = st.count
        snap_tally = st.tally
        snap_fg = fg
        if snap_toll == 1 and (snap_tally == "Buy" or snap_fg == "Up"):
            self._last_dispatch_event = "Diamond"
            self._emit_execution_toast("Diamond", st.price, "NONE", -1, snap_fg)
            self._dispatch_diamond_subblock(snap_fg)
            return
        elif snap_toll == 1 and (snap_tally == "Sell" or snap_fg == "Down"):
            self._last_dispatch_event = "Ruby"
            self._emit_execution_toast("Ruby", st.price, "NONE", -1, snap_fg)
            self._dispatch_ruby_subblock(snap_fg)
            return
        elif snap_count == 1 and (snap_tally == "Buy" or snap_fg == "Up"):
            self._last_dispatch_event = "Hawk"
            self._emit_execution_toast("Hawk", st.price, "NONE", -1, snap_fg)
            self._dispatch_hawk_subblock(snap_fg)
            return
        elif snap_count == 1 and (snap_tally == "Sell" or snap_fg == "Down"):
            self._last_dispatch_event = "Dove"
            self._emit_execution_toast("Dove", st.price, "NONE", -1, snap_fg)
            self._dispatch_dove_subblock(snap_fg)
            return

    #
    # : the FF's `dime = mem;` pre-stamp is the first statement of the
    # subblock body. The `else if((mem==1)||(dime==1))` and
    # `else if((mem==0)||(dime==0))` branches read the pre-stamp.
    #
    # : the `signal = 0; toll = 0; tally = ""; GF = true;
    # signature = true;` reset is at the end of the subblock, not in the
    # caller. The subblock body reads `signal` at its pre-dispatch value
    # during the branch chain.
    def _dispatch_diamond_subblock(self, fg: str) -> None:
        st = self.state
        # : FF's `dime = mem;` pre-stamp.
        st.dime = st.mem
        if (st.prime == 0 and st.dime == 0) and fg == "Up":
            st.dime = 0; st.mem = 0
            self._B(st.price)
            if st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🐂 Bull")
            self._emit_execution_toast("Bull", st.price, "BUY", st.lOrder_id, fg)
            self._Top(emit_toast=False)
            st.E = st.price
        elif ((st.mem == 0 and st.dime == 0) or st.prime == 0) and fg == "" and st.price > st.signal:
            st.dime = 0; st.mem = 0
            self._B(st.price)
            if st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🐂 Bull")
            self._emit_execution_toast("Bull", st.price, "BUY", st.lOrder_id, fg)
            self._Top(emit_toast=False)
            st.E = st.price
        elif (st.prime == 1 or (st.mem == 0 and st.dime == 0)) and fg == "Up" and st.price > st.signal:
            st.dime = 0; st.mem = 0
            self._B(st.price)
            if st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🐂 Bull")
            self._emit_execution_toast("Bull", st.price, "BUY", st.lOrder_id, fg)
            self._Top(emit_toast=False)
            st.E = st.price
        elif ((st.mem == 0 and st.dime == 0) or st.prime == 1) and fg == "" and st.price > st.signal:
            st.dime = 0; st.mem = 0
            self._B(st.price)
            if st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🐂 Bull")
            self._emit_execution_toast("Bull", st.price, "BUY", st.lOrder_id, fg)
            self._Top(emit_toast=False)
            st.E = st.price
        elif st.Price > st.signal and (st.mem == 0 and st.dime == 0):
            if st.safety:
                self._B(st.price)
                if st.C: self._P(st.price)
                else: self._Q(st.price)
                logger.info("🥃 Whisky")
                self._emit_execution_toast("Whisky", st.price, "BUY", st.lOrder_id, fg)
                self._Top(emit_toast=False)
                st.E = st.price
            else:
                logger.info("🥃 Whisky")
                self._emit_execution_toast("Whisky", st.price, "NONE", -1, fg)
                self._Top(emit_toast=False)
                st.E = st.price
                if not st.safety: st.safety = True
        elif st.mem == 1 or st.dime == 1:
            self._on_log()
            if st.safety:
                self._A(st.price)
                if not st.C: self._P(st.price)
                else: self._Q(st.price)
                logger.info("🍷 Wine")
                self._emit_execution_toast("Wine", st.price, "SELL", st.kOrder_id, fg)
                self._Bott(emit_toast=False)
                st.D = st.price
            else:
                logger.info("🍷 Wine")
                self._emit_execution_toast("Wine", st.price, "NONE", -1, fg)
                self._Bott(emit_toast=False)
                st.D = st.price
                if not st.safety: st.safety = True
        else:
            logger.info("🍷 Wine")
            self._emit_execution_toast("Wine", st.price, "NONE", -1, fg)
            self._Bott(emit_toast=False)
            st.D = st.price
            if not st.safety: st.safety = True
        # : FF's `signal = 0; toll = 0; tally = ""; GF = true;
        # signature = true;` at the end of the subblock.
        st.signal = Decimal('0.0')
        st.toll = 0
        st.tally = ""
        st.GF = True
        st.signature = True
        st.execution_fired = True
        try:
            self._project_arc_length(trigger="execution")
        except Exception as e:
            logger.warning(f"Projection refresh (diamond) failed: {e}")

    def _dispatch_ruby_subblock(self, fg: str) -> None:
        st = self.state
        # : FF's `dime = mem;` pre-stamp.
        st.dime = st.mem
        if fg == "Down" and (st.prime == 1 and st.dime == 1):
            st.dime = 1; st.mem = 1
            self._A(st.price)
            if not st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🐻 Bear")
            self._emit_execution_toast("Bear", st.price, "SELL", st.kOrder_id, fg)
            self._Bott(emit_toast=False)
            st.D = st.price
        elif ((st.mem == 1 and st.dime == 1) or st.prime == 1) and fg == "" and st.price < st.signal:
            st.dime = 1; st.mem = 1
            self._A(st.price)
            if not st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🐻 Bear")
            self._emit_execution_toast("Bear", st.price, "SELL", st.kOrder_id, fg)
            self._Bott(emit_toast=False)
            st.D = st.price
        elif st.price < st.signal and fg == "Down" and (st.prime == 0 or (st.mem == 1 and st.dime == 1)):
            st.dime = 1; st.mem = 1
            self._A(st.price)
            if not st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🐻 Bear")
            self._emit_execution_toast("Bear", st.price, "SELL", st.kOrder_id, fg)
            self._Bott(emit_toast=False)
            st.D = st.price
        elif ((st.mem == 1 and st.dime == 1) or st.prime == 0) and fg == "" and st.price < st.signal:
            st.dime = 1; st.mem = 1
            self._A(st.price)
            if not st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🐻 Bear")
            self._emit_execution_toast("Bear", st.price, "SELL", st.kOrder_id, fg)
            self._Bott(emit_toast=False)
            st.D = st.price
        elif st.Price < st.signal and (st.mem == 1 and st.dime == 1):
            if st.safety:
                self._A(st.price)
                if not st.C: self._P(st.price)
                else: self._Q(st.price)
                logger.info("🍷 Wine")
                self._emit_execution_toast("Wine", st.price, "SELL", st.kOrder_id, fg)
                self._Bott(emit_toast=False)
                st.D = st.price
            else:
                logger.info("🍷 Wine")
                self._emit_execution_toast("Wine", st.price, "NONE", -1, fg)
                self._Bott(emit_toast=False)
                st.D = st.price
                if not st.safety: st.safety = True
        elif st.mem == 0 or st.dime == 0:
            self._on_log()
            if st.safety:
                self._B(st.price)
                if st.C: self._P(st.price)
                else: self._Q(st.price)
                logger.info("🥃 Whisky")
                self._emit_execution_toast("Whisky", st.price, "BUY", st.lOrder_id, fg)
                self._Top(emit_toast=False)
                st.E = st.price
            else:
                logger.info("🥃 Whisky")
                self._emit_execution_toast("Whisky", st.price, "NONE", -1, fg)
                self._Top(emit_toast=False)
                st.E = st.price
                if not st.safety: st.safety = True
        else:
            logger.info("🥃 Whisky")
            self._emit_execution_toast("Whisky", st.price, "NONE", -1, fg)
            self._Top(emit_toast=False)
            st.E = st.price
            if not st.safety: st.safety = True
        # : FF's reset at the end of the subblock.
        st.signal = Decimal('0.0')
        st.toll = 0
        st.tally = ""
        st.GF = True
        st.signature = True
        st.execution_fired = True
        try:
            self._project_arc_length(trigger="execution")
        except Exception as e:
            logger.warning(f"Projection refresh (ruby) failed: {e}")

    def _dispatch_hawk_subblock(self, fg: str) -> None:
        st = self.state
        # : FF's `dime = mem;` pre-stamp.
        st.dime = st.mem
        if (st.prime == 0 and st.dime == 0) and fg == "Up":
            st.dime = 0; st.mem = 0
            self._B(st.price)
            if st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🦅 Hawk")
            self._emit_execution_toast("Hawk", st.price, "BUY", st.lOrder_id, fg)
            self._Top(emit_toast=False)
            st.E = st.price
        elif ((st.mem == 0 and st.dime == 0) or st.prime == 0) and fg == "" and st.price > st.signal:
            st.dime = 0; st.mem = 0
            self._B(st.price)
            if st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🦅 Hawk")
            self._emit_execution_toast("Hawk", st.price, "BUY", st.lOrder_id, fg)
            self._Top(emit_toast=False)
            st.E = st.price
        elif (st.prime == 1 or (st.mem == 0 and st.dime == 0)) and fg == "Up" and st.price > st.signal:
            st.dime = 0; st.mem = 0
            self._B(st.price)
            if st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🦅 Hawk")
            self._emit_execution_toast("Hawk", st.price, "BUY", st.lOrder_id, fg)
            self._Top(emit_toast=False)
            st.E = st.price
        elif ((st.mem == 0 and st.dime == 0) or st.prime == 1) and fg == "" and st.price > st.signal:
            st.dime = 0; st.mem = 0
            self._B(st.price)
            if st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🦅 Hawk")
            self._emit_execution_toast("Hawk", st.price, "BUY", st.lOrder_id, fg)
            self._Top(emit_toast=False)
            st.E = st.price
        elif st.Price > st.signal and (st.mem == 0 and st.dime == 0):
            if st.safety:
                self._B(st.price)
                if st.C: self._P(st.price)
                else: self._Q(st.price)
                logger.info("💧 Watter")
                self._emit_execution_toast("Watter", st.price, "BUY", st.lOrder_id, fg)
                self._Top(emit_toast=False)
                st.E = st.price
            else:
                logger.info("💧 Watter")
                self._emit_execution_toast("Watter", st.price, "NONE", -1, fg)
                self._Top(emit_toast=False)
                st.E = st.price
                if not st.safety: st.safety = True
        elif st.mem == 1 or st.dime == 1:
            self._on_log()
            if st.safety:
                self._A(st.price)
                if not st.C: self._P(st.price)
                else: self._Q(st.price)
                logger.info("🩸 Blood")
                self._emit_execution_toast("Blood", st.price, "SELL", st.kOrder_id, fg)
                self._Bott(emit_toast=False)
                st.D = st.price
            else:
                logger.info("🩸 Blood")
                self._emit_execution_toast("Blood", st.price, "NONE", -1, fg)
                self._Bott(emit_toast=False)
                st.D = st.price
                if not st.safety: st.safety = True
        else:
            logger.info("🩸 Blood")
            self._emit_execution_toast("Blood", st.price, "NONE", -1, fg)
            self._Bott(emit_toast=False)
            st.D = st.price
            if not st.safety: st.safety = True
        # : FF's reset at the end of the subblock.
        st.signal = Decimal('0.0')
        st.count = 0
        st.tally = ""
        st.GF = True
        st.signature = True
        st.execution_fired = True
        try:
            self._project_arc_length(trigger="execution")
        except Exception as e:
            logger.warning(f"Projection refresh (hawk) failed: {e}")

    def _dispatch_dove_subblock(self, fg: str) -> None:
        st = self.state
        # : FF's `dime = mem;` pre-stamp.
        st.dime = st.mem
        if fg == "Down" and (st.prime == 1 and st.dime == 1):
            st.dime = 1; st.mem = 1
            self._A(st.price)
            if not st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🕊️ Dove")
            self._emit_execution_toast("Dove", st.price, "SELL", st.kOrder_id, fg)
            self._Bott(emit_toast=False)
            st.D = st.price
        elif ((st.mem == 1 and st.dime == 1) or st.prime == 1) and fg == "" and st.price < st.signal:
            st.dime = 1; st.mem = 1
            self._A(st.price)
            if not st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🕊️ Dove")
            self._emit_execution_toast("Dove", st.price, "SELL", st.kOrder_id, fg)
            self._Bott(emit_toast=False)
            st.D = st.price
        elif st.price < st.signal and fg == "Down" and (st.prime == 0 or (st.mem == 1 and st.dime == 1)):
            st.dime = 1; st.mem = 1
            self._A(st.price)
            if not st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🕊️ Dove")
            self._emit_execution_toast("Dove", st.price, "SELL", st.kOrder_id, fg)
            self._Bott(emit_toast=False)
            st.D = st.price
        elif ((st.mem == 1 and st.dime == 1) or st.prime == 0) and fg == "" and st.price < st.signal:
            st.dime = 1; st.mem = 1
            self._A(st.price)
            if not st.C: self._P(st.price)
            else: self._Q(st.price)
            logger.info("🕊️ Dove")
            self._emit_execution_toast("Dove", st.price, "SELL", st.kOrder_id, fg)
            self._Bott(emit_toast=False)
            st.D = st.price
        elif st.Price < st.signal and (st.mem == 1 and st.dime == 1):
            if st.safety:
                self._A(st.price)
                if not st.C: self._P(st.price)
                else: self._Q(st.price)
                logger.info("🩸 Blood")
                self._emit_execution_toast("Blood", st.price, "SELL", st.kOrder_id, fg)
                self._Bott(emit_toast=False)
                st.D = st.price
            else:
                logger.info("🩸 Blood")
                self._emit_execution_toast("Blood", st.price, "NONE", -1, fg)
                self._Bott(emit_toast=False)
                st.D = st.price
                if not st.safety: st.safety = True
        elif st.mem == 0 or st.dime == 0:
            self._on_log()
            if st.safety:
                self._B(st.price)
                if st.C: self._P(st.price)
                else: self._Q(st.price)
                logger.info("💧 Watter")
                self._emit_execution_toast("Watter", st.price, "BUY", st.lOrder_id, fg)
                self._Top(emit_toast=False)
                st.E = st.price
            else:
                logger.info("💧 Watter")
                self._emit_execution_toast("Watter", st.price, "NONE", -1, fg)
                self._Top(emit_toast=False)
                st.E = st.price
                if not st.safety: st.safety = True
        else:
            logger.info("💧 Watter")
            self._emit_execution_toast("Watter", st.price, "NONE", -1, fg)
            self._Top(emit_toast=False)
            st.E = st.price
            if not st.safety: st.safety = True
        # : FF's reset at the end of the subblock.
        st.signal = Decimal('0.0')
        st.count = 0
        st.tally = ""
        st.GF = True
        st.signature = True
        st.execution_fired = True
        try:
            self._project_arc_length(trigger="execution")
        except Exception as e:
            logger.warning(f"Projection refresh (dove) failed: {e}")

    def _on_call(self) -> None:
        st = self.state
        y = st.y
        j = y + 1
        while j < st.X_scan + 2:
            idx = j - (y + 1)
            if idx < 0 or idx >= len(st.Regime):
                break
            self._unify(j)
            self._normalize(j)
            if st.Suply <= st.price or st.iSuply <= st.price or st.iSuply <= st.iH:
                i = j
                st.I = st.iW
                st.iZ = i
                st.Z = i
                if st.iw != 0 and st.jC == st.Cc:
                    st.h = st.I
                st.iC = st.C
                st.jC = not st.C
                if self._on_hold(j, "sTrend", "tTrend"):
                    st.iz = i
                    st.z = i
                    st.iI = st.iw
                    self._H(j)
                if st.X_scan != X_PERIOD - 1:
                    st.X_scan += 1
            if st.Demand >= st.price or st.iDemand >= st.price or st.iDemand >= st.iL:
                i = j
                st.I = st.iZ
                st.iW = i
                st.W = i
                if st.iz != 0 and st.iC == st.Cc:
                    st.h = st.I
                st.jC = st.C
                st.iC = not st.C
                if self._on_hold(j, "sTrend", "tTrend"):
                    st.iw = i
                    st.w = i
                    st.iI = st.iz
                    self._L(j)
                if st.X_scan != X_PERIOD - 1:
                    st.X_scan += 1
            j += 1
        st.X_scan = y

    def _on_track(self) -> None:
        st = self.state
        st.on_track_runs += 1
        y = st.y
        st.S = X_PERIOD
        st.T = X_PERIOD
        st.X_scan = y
        st.Y_scan = y
        is_now = self.ohlcv_history[-1]["timestamp"] if self.ohlcv_history else datetime.now()
        scan_limit = 4 * MAX_PERIOD
        s = X_PERIOD - 1
        safety_counter = 0
        safety_max = scan_limit * 2
        while s < st.S:
            safety_counter += 1
            if safety_counter > safety_max:
                logger.warning(f"⚠️ OnTrack() safety cap hit at s={s}; aborting scan")
                break
            if s >= scan_limit:
                break
            if s < 0:
                s += 1
                continue
            idx = s - (y + 1)
            if idx < 0:
                s += 1
                continue
            if idx >= len(st.Regime):
                ext = idx - len(st.Regime) + 1
                st.Regime.extend(["sRange"] * ext)
                st.k.extend([False] * ext)
                st.l.extend([False] * ext)
                st.HH.extend([Decimal('0.0')] * ext)
                st.LL.extend([Decimal('0.0')] * ext)
                st.Premium.extend([Decimal('0.0')] * ext)
                st.Discount.extend([Decimal('0.0')] * ext)
            j = s
            self._normalize(j)
            self._unify(j)
            if st.Suply <= st.price or st.iSuply <= st.price or st.iSuply <= st.iH:
                i = s
                st.I = st.iW
                st.Z = MAX_PERIOD
                st.iZ = i
                st.T += 1
                st.iC = st.C
                if st.iw != 0 and st.jC == st.Cc:
                    st.h = st.I
                st.jC = not st.C
                if st.iStdDev > Decimal('50.0'):
                    st.S += 1
                    st.iz = i
                    st.iI = st.iw
                    self._H(j)
                elif st.iATR < Decimal('50.0'):
                    st.S += 1
                    st.iO = i
                    st.io = i
                    self._H(j)
                else:
                    self._H(j)
                    if is_now != st.t:
                        if self._on_fire(j, "Stable", "tVolatile"):
                            self._F(j, st.iH, st.iL)
                            st.Regime[idx] = "tVolatile"
                        else:
                            st.Regime[idx] = "sVolatile"
                    st.S += 1
            if st.Demand >= st.price or st.iDemand >= st.price or st.iDemand >= st.iL:
                i = s
                st.I = st.iZ
                st.W = MAX_PERIOD
                st.iW = i
                st.T += 1
                st.jC = st.C
                if st.iz != 0 and st.iC == st.Cc:
                    st.h = st.I
                st.iC = not st.C
                if st.iStdDev > Decimal('50.0'):
                    st.S += 1
                    st.iw = i
                    st.iI = st.iz
                    self._L(j)
                elif st.iATR < Decimal('50.0'):
                    st.S += 1
                    st.iO = i
                    st.io = i
                    self._L(j)
                else:
                    self._L(j)
                    if is_now != st.t:
                        if self._on_fire(j, "Stable", "tVolatile"):
                            self._F(j, st.iH, st.iL)
                            st.Regime[idx] = "tVolatile"
                        else:
                            st.Regime[idx] = "sVolatile"
                    st.S += 1
            s += 1
        second_scan_start = X_PERIOD - 1
        second_scan_end = st.S if st.S > X_PERIOD - 1 else X_PERIOD
        s = second_scan_start
        while s < second_scan_end:
            idx = s - (y + 1)
            if idx < 0:
                s += 1
                continue
            j = s
            self._normalize(j)
            self._unify(j)
            if st.iStdDev < Decimal('50.0') and st.iATR < Decimal('50.0'):
                self._R(j)
                self._L(j)
                self._H(j)
            s += 1
        st.S = X_PERIOD
        st.T = X_PERIOD
        if st.Z != scan_limit and st.Z >= st.z:
            j = MAX_PERIOD - 1
            st.z = j
            idx = j - (y + 1)
            if 0 <= idx < len(st.Regime):
                if is_now != st.t:
                    if st.Regime[idx] != "tTrend":
                        self._F(j, st.iH, st.iL)
                        st.Regime[idx] = "tTrend"
                    else:
                        st.Regime[idx] = "sTrend"
        elif st.Z != scan_limit and st.Z < st.z:
            j = MAX_PERIOD
            st.z = j
            idx = j - (y + 1)
            if 0 <= idx < len(st.Regime):
                if is_now != st.t:
                    if st.Regime[idx] != "tTrend":
                        self._F(j, st.iH, st.iL)
                        st.Regime[idx] = "tTrend"
                    else:
                        st.Regime[idx] = "sTrend"
        else:
            j = X_PERIOD - 1
            st.z = j
            idx = j - (y + 1)
            if 0 <= idx < len(st.Regime):
                if is_now != st.t:
                    if st.Regime[idx] != "tTrend":
                        self._F(j, st.iH, st.iL)
                        st.Regime[idx] = "tTrend"
                    else:
                        st.Regime[idx] = "sTrend"
        if st.W != scan_limit and st.W >= st.w:
            j = MAX_PERIOD - 1
            st.w = j
            idx = j - (y + 1)
            if 0 <= idx < len(st.Regime):
                if is_now != st.t:
                    if st.Regime[idx] != "tTrend":
                        self._F(j, st.iH, st.iL)
                        st.Regime[idx] = "tTrend"
                    else:
                        st.Regime[idx] = "sTrend"
        elif st.W != scan_limit and st.W < st.w:
            j = MAX_PERIOD
            st.w = j
            idx = j - (y + 1)
            if 0 <= idx < len(st.Regime):
                if is_now != st.t:
                    if st.Regime[idx] != "tTrend":
                        self._F(j, st.iH, st.iL)
                        st.Regime[idx] = "tTrend"
                    else:
                        st.Regime[idx] = "sTrend"
        else:
            j = X_PERIOD - 1
            st.w = j
            idx = j - (y + 1)
            if 0 <= idx < len(st.Regime):
                if is_now != st.t:
                    if st.Regime[idx] != "tTrend":
                        self._F(j, st.iH, st.iL)
                        st.Regime[idx] = "tTrend"
                    else:
                        st.Regime[idx] = "sTrend"

    def _on_stand(self) -> None:
        st = self.state
        st.on_stand_runs += 1
        y = st.y
        st.S = X_PERIOD
        st.T = X_PERIOD
        st.X_scan = y
        st.Y_scan = y
        is_now = self.ohlcv_history[-1]["timestamp"] if self.ohlcv_history else datetime.now()
        s = y + 1
        while s > st.Y_scan:
            if s == 1:
                break
            if s < 0:
                break
            idx = s - (y + 1)
            if idx < 0:
                s -= 1
                continue
            if idx >= len(st.Regime):
                ext = idx - len(st.Regime) + 1
                st.Regime.extend(["sRange"] * ext)
                st.k.extend([False] * ext)
                st.l.extend([False] * ext)
                st.HH.extend([Decimal('0.0')] * ext)
                st.LL.extend([Decimal('0.0')] * ext)
                st.Premium.extend([Decimal('0.0')] * ext)
                st.Discount.extend([Decimal('0.0')] * ext)
            j = s
            st.ir = 0
            st.ij = 0
            self._normalize(j)
            self._unify(j)
            if st.Suply <= st.price or st.iSuply <= st.price or st.iSuply <= st.iH:
                i = s
                st.I = st.iW
                st.Z = MIN_PERIOD + 1
                st.iZ = i
                st.T -= 1
                st.iC = st.C
                if st.iw != 0 and st.jC == st.Cc:
                    st.h = st.I
                st.jC = not st.C
                if st.X_scan != st.Y_scan and st.iz == 0 and st.iStdDev > Decimal('50.0'):
                    st.ij = i
                    st.iz = i
                    st.iI = st.iw
                    self._H(j)
                    if st.ir == 0 and st.Y_scan != 2:
                        st.Y_scan -= 1
                elif st.X_scan != st.Y_scan and st.iO == 0 and st.iATR < Decimal('50.0'):
                    st.iO = i
                    st.ir = i
                    self._H(j)
                    if st.ij == 0 and st.Y_scan != 2:
                        st.Y_scan -= 1
                elif st.X_scan == st.Y_scan:
                    self._H(j)
                    if is_now != st.t:
                        if self._on_fire(j, "Stable", "tVolatile"):
                            self._F(j, st.iH, st.iL)
                            st.Regime[idx] = "tVolatile"
                        else:
                            st.Regime[idx] = "sVolatile"
                    if st.Y_scan != 2 and st.X_scan != 2:
                        st.Y_scan -= 1
                        st.X_scan -= 1
            if st.Demand >= st.price or st.iDemand >= st.price or st.iDemand >= st.iL:
                i = s
                st.I = st.iZ
                st.W = MIN_PERIOD + 1
                st.iW = i
                st.T -= 1
                st.jC = st.C
                if st.iz != 0 and st.iC == st.Cc:
                    st.h = st.I
                st.iC = not st.C
                if st.X_scan != st.Y_scan and st.iw == 0 and st.iStdDev > Decimal('50.0'):
                    st.ij = i
                    st.iw = i
                    st.iI = st.iz
                    self._L(j)
                    if st.ir == 0 and st.Y_scan != 2:
                        st.Y_scan -= 1
                elif st.X_scan != st.Y_scan and st.iO == 0 and st.iATR < Decimal('50.0'):
                    st.iO = i
                    st.io = i
                    st.ir = 0
                    self._L(j)
                    if st.ij == 0 and st.Y_scan != 2:
                        st.Y_scan -= 1
                elif st.X_scan == st.Y_scan:
                    self._L(j)
                    if is_now != st.t:
                        if self._on_fire(j, "Stable", "tVolatile"):
                            self._F(j, st.iH, st.iL)
                            st.Regime[idx] = "tVolatile"
                        else:
                            st.Regime[idx] = "sVolatile"
                    if st.Y_scan != 2 and st.X_scan != 2:
                        st.Y_scan -= 1
                        st.X_scan -= 1
            else:
                if st.Y_scan != 2 and st.X_scan != 2:
                    st.Y_scan -= 1
                    st.X_scan -= 1
            s -= 1
        second_scan_start = st.Y_scan + 1
        second_scan_end = y + 1
        if second_scan_start < second_scan_end:
            s = second_scan_start
            while s < second_scan_end:
                idx = s - (y + 1)
                if idx < 0:
                    s += 1
                    continue
                j = s
                self._normalize(j)
                self._unify(j)
                if st.iStdDev < Decimal('50.0') and st.iATR < Decimal('50.0'):
                    self._R(j)
                    self._L(j)
                    self._H(j)
                s += 1
        st.X_scan = y
        st.Y_scan = y
        if st.Z != 2 and st.Z >= st.z:
            j = MIN_PERIOD
            st.z = j
            idx = j - (y + 1)
            if 0 <= idx < len(st.Regime):
                if is_now != st.t:
                    if st.Regime[idx] != "tTrend":
                        self._F(j, st.iH, st.iL)
                        st.Regime[idx] = "tTrend"
                    else:
                        st.Regime[idx] = "sTrend"
        elif st.Z != 2 and st.Z < st.z:
            j = MIN_PERIOD + 1
            st.z = j
            idx = j - (y + 1)
            if 0 <= idx < len(st.Regime):
                if is_now != st.t:
                    if st.Regime[idx] != "tTrend":
                        self._F(j, st.iH, st.iL)
                        st.Regime[idx] = "tTrend"
                    else:
                        st.Regime[idx] = "sTrend"
        else:
            j = y + 1
            st.z = j
            idx = j - (y + 1)
            if 0 <= idx < len(st.Regime):
                if is_now != st.t:
                    if st.Regime[idx] != "tTrend":
                        self._F(j, st.iH, st.iL)
                        st.Regime[idx] = "tTrend"
                    else:
                        st.Regime[idx] = "sTrend"
        if st.W != 2 and st.W >= st.w:
            j = MIN_PERIOD
            st.w = j
            idx = j - (y + 1)
            if 0 <= idx < len(st.Regime):
                if is_now != st.t:
                    if st.Regime[idx] != "tTrend":
                        self._F(j, st.iH, st.iL)
                        st.Regime[idx] = "tTrend"
                    else:
                        st.Regime[idx] = "sTrend"
        elif st.W != 2 and st.W < st.w:
            j = MIN_PERIOD + 1
            st.w = j
            idx = j - (y + 1)
            if 0 <= idx < len(st.Regime):
                if is_now != st.t:
                    if st.Regime[idx] != "tTrend":
                        self._F(j, st.iH, st.iL)
                        st.Regime[idx] = "tTrend"
                    else:
                        st.Regime[idx] = "sTrend"
        else:
            j = y + 1
            st.w = j
            idx = j - (y + 1)
            if 0 <= idx < len(st.Regime):
                if is_now != st.t:
                    if st.Regime[idx] != "tTrend":
                        self._F(j, st.iH, st.iL)
                        st.Regime[idx] = "tTrend"
                    else:
                        st.Regime[idx] = "sTrend"

    def _on_goe(self) -> None:
        st = self.state
        if st.signal != Decimal('0.0'):
            return
        if self._on_gaurd(0) and st.KC:
            if ((st.h == st.io and st.z > st.o) or (st.h == st.iO and st.Z > st.O) or (st.h == st.iz and st.Z > st.z) or (st.h == st.iZ and st.Z < st.z)):
                if (not st.C) and (not st.c):
                    st.prime = 1; self._G(); self._signal(); st.tick_tock = True; st.tag = 1
                    logger.info(f"🟥 Sign. (Goe) price={st.price} h={st.h} Z={st.iZ} z={st.iz} O={st.iO} o={st.io}")
                else:
                    st.prime = 1; self._G(); self._signal(); st.tick_tock = True; st.tag = 1
                    logger.info(f"🟥 Sig. (Goe) price={st.price} h={st.h} Z={st.iZ} z={st.iz} O={st.iO} o={st.io}")
            elif (st.h == st.io) or (st.h == st.iZ) or (st.h == st.iz) or (st.h == st.iO):
                if (not st.C) and (not st.c):
                    st.prime = 1; self._G(); self._signal(); st.tick_tock = True; st.tag = 1
                    logger.info(f"🟥 Sig. (Goe) price={st.price} h={st.h} Z={st.iZ} z={st.iz} O={st.iO} o={st.io}")
                else:
                    st.prime = 1; self._G(); self._signal(); st.tick_tock = True; st.tag = 1
                    logger.info(f"🟥 Sign. (Goe) price={st.price} h={st.h} Z={st.iZ} z={st.iz} O={st.iO} o={st.io}")
        elif self._on_gaurd(0) != st.KC:
            if ((st.h == st.io and st.z > st.o) or (st.h == st.iO and st.Z > st.O) or (st.h == st.iz and st.Z > st.z) or (st.h == st.iZ and st.Z < st.z)):
                if (not st.C) or (not st.c):
                    st.prime = 1; self._G(); self._signal(); st.tick_tock = True; st.tag = 1
                    logger.info(f"🟥 Sign. (Goe) price={st.price} h={st.h} Z={st.iZ} z={st.iz} O={st.iO} o={st.io}")
                else:
                    st.prime = 1; self._G(); self._signal(); st.tick_tock = True; st.tag = 1
                    logger.info(f"🟥 Sig. (Goe) price={st.price} h={st.h} Z={st.iZ} z={st.iz} O={st.iO} o={st.io}")
            elif (st.h == st.io) or (st.h == st.iZ) or (st.h == st.iz) or (st.h == st.iO):
                if (not st.C) or (not st.c):
                    st.prime = 1; self._G(); self._signal(); st.tick_tock = True; st.tag = 1
                    logger.info(f"🟥 Sig. (Goe) price={st.price} h={st.h} Z={st.iZ} z={st.iz} O={st.iO} o={st.io}")
                else:
                    st.prime = 1; self._G(); self._signal(); st.tick_tock = True; st.tag = 1
                    logger.info(f"🟥 Sign. (Goe) price={st.price} h={st.h} Z={st.iZ} z={st.iz} O={st.iO} o={st.io}")
            self._KC()

    def _on_toe(self) -> None:
        st = self.state
        if st.signal != Decimal('0.0'):
            return
        if self._on_gaurd(0) and st.KC:
            if ((st.h == st.io and st.w > st.o) or (st.h == st.iO and st.W > st.O) or (st.h == st.iw and st.W > st.w) or (st.h == st.iW and st.W < st.w)):
                if (not st.C) and (not st.c):
                    st.prime = 0; self._G(); self._signal(); st.tick_tock = True; st.tag = 0
                    logger.info(f"🟩 Sig. (Toe) price={st.price} h={st.h} W={st.iW} w={st.iw} O={st.iO} o={st.io}")
                else:
                    st.prime = 0; self._G(); self._signal(); st.tick_tock = True; st.tag = 0
                    logger.info(f"🟩 Sign. (Toe) price={st.price} h={st.h} W={st.iW} w={st.iw} O={st.iO} o={st.io}")
            elif (st.h == st.io) or (st.h == st.iW) or (st.h == st.iw) or (st.h == st.iO):
                if (not st.C) and (not st.c):
                    st.prime = 0; self._G(); self._signal(); st.tick_tock = True; st.tag = 0
                    logger.info(f"🟩 Sign. (Toe) price={st.price} h={st.h} W={st.iW} w={st.iw} O={st.iO} o={st.io}")
                else:
                    st.prime = 0; self._G(); self._signal(); st.tick_tock = True; st.tag = 0
                    logger.info(f"🟩 Sig. (Toe) price={st.price} h={st.h} W={st.iW} w={st.iw} O={st.iO} o={st.io}")
        elif self._on_gaurd(0) != st.KC:
            if ((st.h == st.io and st.w > st.o) or (st.h == st.iO and st.W > st.O) or (st.h == st.iw and st.W > st.w) or (st.h == st.iW and st.W < st.w)):
                if (not st.C) or (not st.c):
                    st.prime = 0; self._G(); self._signal(); st.tick_tock = True; st.tag = 0
                    logger.info(f"🟩 Sig. (Toe) price={st.price} h={st.h} W={st.iW} w={st.iw} O={st.iO} o={st.io}")
                else:
                    st.prime = 0; self._G(); self._signal(); st.tick_tock = True; st.tag = 0
                    logger.info(f"🟩 Sign. (Toe) price={st.price} h={st.h} W={st.iW} w={st.iw} O={st.iO} o={st.io}")
            elif (st.h == st.io) or (st.h == st.iW) or (st.h == st.iw) or (st.h == st.iO):
                if (not st.C) or (not st.c):
                    st.prime = 0; self._G(); self._signal(); st.tick_tock = True; st.tag = 0
                    logger.info(f"🟩 Sign. (Toe) price={st.price} h={st.h} W={st.iW} w={st.iw} O={st.iO} o={st.io}")
                else:
                    st.prime = 0; self._G(); self._signal(); st.tick_tock = True; st.tag = 0
                    logger.info(f"🟩 Sig. (Toe) price={st.price} h={st.h} W={st.iW} w={st.iw} O={st.iO} o={st.io}")
            self._KC()

    def _signal(self) -> None:
        st = self.state
        if st.price <= Decimal('0.0'):
            return
        if not (st.authoritative_m >= 12 or st.authoritative_n >= 12):
            return
        st.ab = not st.ba
        st.count = 0
        st.toll = 0
        st.tally = " "
        st.signal = st.price
        m_local = st.authoritative_m
        n_local = st.authoritative_n
        self._last_kronecker_bar = st.authoritative_h if st.authoritative_h >= 0 else st.h
        self._imbalance_fire_count += 1
        self._last_signal_time = datetime.now()
        if m_local >= 12:
            signal_type = "BUY"
        elif n_local >= 12:
            signal_type = "SELL"
        else:
            signal_type = "NEUTRAL"
        regime_idx = st.h - (st.y + 1)
        regime = st.Regime[regime_idx] if 0 <= regime_idx < len(st.Regime) else "Unknown"
        bar_timestamp = None
        if self.ohlcv_history:
            bar_timestamp = self.ohlcv_history[-1]["timestamp"]
            if isinstance(bar_timestamp, datetime):
                bar_timestamp = bar_timestamp.isoformat()
        signal_record = {
            "timestamp": datetime.now().isoformat(),
            "bar_timestamp": bar_timestamp,
            "type": signal_type,
            "price": str(st.price),
            "signal_level": str(st.signal),
            "regime": regime,
            "m_count": int(m_local),
            "n_count": int(n_local),
            "tick": int(st.tick),
            "h_bar": int(st.h),
            "source": "Goe" if st.prime == 1 else ("Toe" if st.prime == 0 else "phase"),  # phase label only; never implies Kronecker gate δ(m-n-2) fired
        }
        st.signal_history.append(signal_record)
        if len(st.signal_history) > st.max_signal_history:
            st.signal_history = st.signal_history[-st.max_signal_history:]
        st.last_signal_at = signal_record["timestamp"]
        logger.info(f"🎯 SIGNAL #{self._imbalance_fire_count}: type={signal_type} @ {st.price}, tick={st.tick}, h={st.h}, m={m_local}, n={n_local}, regime={regime}")
        _emit_toast("signal", {
            "type": signal_type,
            "price": str(st.price),
            "signal_level": str(st.signal),
            "m": int(m_local),
            "n": int(n_local),
            "h": int(st.h),
            "regime": regime,
            "tick": int(st.tick),
            "source": signal_record["source"],
        })
        if PUSH_ON_SIGNAL:
            self._send_signal_alert()

    def _on_gaurd(self, inp: int) -> bool:
        st = self.state
        if st.price > st.E and st.E != Decimal('0.0'):
            if st.signature and inp != -1:
                st.dime = 0
            return True
        if st.price < st.D and st.D != Decimal('0.0'):
            if st.signature and inp != -1:
                st.dime = 1
            return True
        if st.signature and inp != -1:
            st.dime = 1
        return False

    def _on_log(self) -> None:
        st = self.state
        if st.dime == 0:
            logger.info("🕊️ Flying")
        elif st.dime == 1:
            logger.info("🔻 Falling")
        else:
            logger.info("⏳ Wait/Decern")

    def _A(self, price: Decimal) -> None:
        st = self.state
        closed_any = False
        if st.v and st.lOrder_id != -1:
            logger.info(f"🔴 A(): Close long #{st.lOrder_id} at {price}")
            self._close_order(st.lOrder_id, price)
            st.lOrder_id = -1
            st.has_open_long = False
            closed_any = True
        elif st.v and st.kOrder_id != -1:
            logger.info(f"🔴 A(): Close short #{st.kOrder_id} at {price}")
            self._close_order(st.kOrder_id, price)
            st.kOrder_id = -1
            st.has_open_short = False
            closed_any = True
        st.E = Decimal('0.0')
        st.A = True
        st.B = False
        st.K = False
        st.Buy = -1
        st.trailing_stop_active = False
        st.trailing_stop_price = Decimal('0.0')
        st.trailing_take_profit = Decimal('0.0')
        self._emit_execution_toast("A", price, "CLOSE", -1, "A_close" if closed_any else "A_no_position")

    def _B(self, price: Decimal) -> None:
        st = self.state
        closed_any = False
        if st.u and st.kOrder_id != -1:
            logger.info(f"🔵 B(): Close short #{st.kOrder_id} at {price}")
            self._close_order(st.kOrder_id, price)
            st.kOrder_id = -1
            st.has_open_short = False
            closed_any = True
        elif st.u and st.lOrder_id != -1:
            logger.info(f"🔵 B(): Close long #{st.lOrder_id} at {price}")
            self._close_order(st.lOrder_id, price)
            st.lOrder_id = -1
            st.has_open_long = False
            closed_any = True
        st.D = Decimal('0.0')
        st.A = False
        st.B = True
        st.K = False
        st.Sell = -1
        st.trailing_stop_active = False
        st.trailing_stop_price = Decimal('0.0')
        st.trailing_take_profit = Decimal('0.0')
        self._emit_execution_toast("B", price, "CLOSE", -1, "B_close" if closed_any else "B_no_position")

    def _open_order(self, side: str, price: Decimal, sl: Decimal, tp: Decimal, lot: Decimal) -> int:
        ticket = self._next_ticket
        self._next_ticket += 1
        order = Order(ticket=ticket, side=side, entry=price, sl=sl, tp=tp, lot=lot)
        self.orders.append(order)
        return ticket

    def _close_order(self, ticket: int, price: Decimal) -> bool:
        for o in self.orders:
            if o.ticket == ticket and o.closed_at is None:
                o.closed_at = datetime.now()
                o.close_price = price
                return True
        return False

    def _P(self, price: Decimal) -> None:
        st = self.state
        if price <= Decimal('0.0'):
            return
        self._S()
        ask_price = self.price_history[-1].ask if self.price_history else price
        bid_price = self.price_history[-1].bid if self.price_history else price
        target = self._get_next_topological_target("BUY", ask_price)
        if target > Decimal('0.0') and self._will_pass_spread_in_pnl(ask_price, target, "BUY"):
            if st.Buy >= 0 and (st.A or not st.B) and (st.u or not st.v):
                if st.C:
                    ticket = self._open_order("BUY", ask_price, self._bSL, self._bTP, LOT_SIZE)
                    st.lOrder_id = ticket
                    st.has_open_long = True
                    st.trailing_stop_entry = ask_price
                    st.trailing_stop_side = "LONG"
                    st.Buy = 0 if st.Buy == -1 else st.Buy + 1
                    logger.info(f"🟢 P(): BUY executed #{ticket} at {ask_price}, target={target}")
        else:
            self._A(price)
            logger.info("⚠️ P(): BUY rejected — projected PnL <= spread friction")

        target = self._get_next_topological_target("SELL", bid_price)
        if target > Decimal('0.0') and self._will_pass_spread_in_pnl(bid_price, target, "SELL"):
            if st.Sell >= 0 and (not st.A or st.B) and (not st.u or st.v):
                if not st.C:
                    ticket = self._open_order("SELL", bid_price, self._sSL, self._sTP, LOT_SIZE)
                    st.kOrder_id = ticket
                    st.has_open_short = True
                    st.trailing_stop_entry = bid_price
                    st.trailing_stop_side = "SHORT"
                    st.Sell = 0 if st.Sell == -1 else st.Sell + 1
                    logger.info(f"🔴 P(): SELL executed #{ticket} at {bid_price}, target={target}")
        else:
            self._B(price)
            logger.info("⚠️ P(): SELL rejected — projected PnL <= spread friction")

    def _Q(self, price: Decimal) -> None:
        st = self.state
        if price <= Decimal('0.0'):
            return
        self._S()
        ask_price = self.price_history[-1].ask if self.price_history else price
        bid_price = self.price_history[-1].bid if self.price_history else price
        target = self._get_next_topological_target("SELL", bid_price)
        if target > Decimal('0.0') and self._will_pass_spread_in_pnl(bid_price, target, "SELL"):
            if st.Sell >= 0 and (not st.A or st.B) and (not st.u or st.v):
                if st.C:
                    ticket = self._open_order("SELL", bid_price, self._sSL, self._sTP, LOT_SIZE)
                    st.kOrder_id = ticket
                    st.has_open_short = True
                    st.trailing_stop_entry = bid_price
                    st.trailing_stop_side = "SHORT"
                    st.Sell = 0 if st.Sell == -1 else st.Sell + 1
                    logger.info(f"🔴 Q(): SELL executed #{ticket} at {bid_price}, target={target}")
        else:
            self._B(price)
            logger.info("⚠️ Q(): SELL rejected — projected PnL <= spread friction")

        target = self._get_next_topological_target("BUY", ask_price)
        if target > Decimal('0.0') and self._will_pass_spread_in_pnl(ask_price, target, "BUY"):
            if st.Buy >= 0 and (st.A or not st.B) and (st.u or not st.v):
                if not st.C:
                    ticket = self._open_order("BUY", ask_price, self._bSL, self._bTP, LOT_SIZE)
                    st.lOrder_id = ticket
                    st.has_open_long = True
                    st.trailing_stop_entry = ask_price
                    st.trailing_stop_side = "LONG"
                    st.Buy = 0 if st.Buy == -1 else st.Buy + 1
                    logger.info(f"🟢 Q(): BUY executed #{ticket} at {ask_price}, target={target}")
        else:
            self._A(price)
            logger.info("⚠️ Q(): BUY rejected — projected PnL <= spread friction")

    def _S(self) -> None:
        st = self.state
        point = self._point_size if self._point_size > Decimal('0.0') else Decimal('0.00001')
        # : use the frozen commission (FF's `com` constant).
        com_local = self._com_price_frozen
        sl_price = STOP_LOSS * point
        tp_price = TAKE_PROFIT * point
        bid = st.price
        ask = st.price
        if self.price_history:
            bid = self.price_history[-1].bid
            ask = self.price_history[-1].ask
        if STOP_LOSS != Decimal('0.0'):
            self._sSL = bid + sl_price - com_local
            self._bSL = ask - sl_price + com_local
        if TAKE_PROFIT != Decimal('0.0'):
            self._sTP = bid - tp_price
            self._bTP = ask + tp_price

    def _execute_trailing_stop(self) -> None:
        st = self.state
        has_long = st.has_open_long
        has_short = st.has_open_short
        if not (has_long or has_short):
            if st.trailing_stop_active:
                logger.info("📉 Trailing stop deactivated — no open orders")
                st.trailing_stop_active = False
                st.trailing_stop_price = Decimal('0.0')
                st.trailing_take_profit = Decimal('0.0')
                st.trailing_stop_entry = Decimal('0.0')
                st.trailing_stop_side = ""
            return
        regime_col = 0
        if 0 <= regime_col < len(st.Regime):
            regime = st.Regime[regime_col]
            if regime in ("tStable", "tCoherent"):
                return
        if st.price <= Decimal('0.0'):
            return
        if not st.trailing_stop_active:
            st.trailing_stop_active = True
            st.trailing_stop_entry = st.price
            st.trailing_stop_price = st.price
            st.trailing_stop_side = "LONG" if has_long else "SHORT"
            if has_long:
                st.trailing_take_profit = st.price * Decimal('1.02')
            else:
                st.trailing_take_profit = st.price * Decimal('0.98')
            logger.info(f"🎯 Trailing stop ACTIVATED at {st.trailing_stop_price}, TP={st.trailing_take_profit}, direction={st.trailing_stop_side}")
            return
        if len(self.price_history) > 0:
            last = self.price_history[-1]
            current_spread = last.ask - last.bid
        else:
            current_spread = Decimal('0.0')
        com_price = self._com_price_frozen
        point_size = self._point_size if self._point_size > Decimal('0.0') else Decimal('0.00001')
        friction_points = (current_spread + com_price) / point_size
        safety_buffer = Decimal('1.0')
        min_trail_threshold = (friction_points + safety_buffer) * point_size
        if has_long:
            pnl_points = (st.price - st.trailing_stop_entry) / point_size
        else:
            pnl_points = (st.trailing_stop_entry - st.price) / point_size
        if pnl_points <= (friction_points + safety_buffer):
            return
        trail_step = max(min_trail_threshold, pnl_points * point_size * Decimal('0.3'))
        new_sl = st.trailing_stop_price
        topological_target = Decimal('0.0')
        if has_long:
            for ji in range(st.y + 1, X_PERIOD):
                jidx = ji - (st.y + 1)
                if jidx < len(st.Premium) and st.Premium[jidx] > st.price and st.Premium[jidx] != Decimal('0.0'):
                    topological_target = st.Premium[jidx]
                    break
            slDistance = max(trail_step, STOP_LOSS * point_size)
            proposedSL = st.price - slDistance
            if ((proposedSL > st.trailing_stop_price or st.trailing_stop_price == Decimal('0.0')) and (topological_target == Decimal('0.0') or proposedSL < (topological_target - min_trail_threshold))):
                new_sl = proposedSL
            tpDistance = Decimal('0.0')
            if topological_target > Decimal('0.0'):
                tpDistance = max(topological_target - st.price, TAKE_PROFIT * point_size)
            else:
                tpDistance = max(trail_step * Decimal('2.0'), TAKE_PROFIT * point_size)
            proposedTP = st.price + tpDistance
            if proposedTP > (st.price + min_trail_threshold):
                st.trailing_take_profit = proposedTP
        else:
            for ji in range(st.y + 1, X_PERIOD):
                jidx = ji - (st.y + 1)
                if jidx < len(st.Discount) and st.Discount[jidx] < st.price and st.Discount[jidx] != Decimal('0.0'):
                    topological_target = st.Discount[jidx]
                    break
            slDistance = max(trail_step, STOP_LOSS * point_size)
            proposedSL = st.price + slDistance
            if ((st.trailing_stop_price == Decimal('0.0') or proposedSL < st.trailing_stop_price) and (topological_target == Decimal('0.0') or proposedSL > (topological_target + min_trail_threshold))):
                new_sl = proposedSL
            tpDistance = Decimal('0.0')
            if topological_target > Decimal('0.0'):
                tpDistance = max(st.price - topological_target, TAKE_PROFIT * point_size)
            else:
                tpDistance = max(trail_step * Decimal('2.0'), TAKE_PROFIT * point_size)
            proposedTP = st.price - tpDistance
            if proposedTP < (st.price - min_trail_threshold):
                st.trailing_take_profit = proposedTP
        if new_sl != st.trailing_stop_price:
            st.trailing_stop_price = new_sl
            logger.info(f"📈 Trailing stop updated to {st.trailing_stop_price} (PnL={pnl_points}pts, friction={friction_points}pts)")
        if has_long and st.price >= st.trailing_take_profit:
            logger.info(f"✅ TP hit (LONG) at {st.price} / TP={st.trailing_take_profit}")
            if st.lOrder_id != -1:
                self._close_order(st.lOrder_id, st.price)
            st.trailing_stop_active = False
            st.trailing_stop_price = Decimal('0.0')
            st.trailing_take_profit = Decimal('0.0')
            st.trailing_stop_entry = Decimal('0.0')
            st.trailing_stop_side = ""
            st.has_open_long = False
            st.lOrder_id = -1
        elif has_short and st.price <= st.trailing_take_profit:
            logger.info(f"✅ TP hit (SHORT) at {st.price} / TP={st.trailing_take_profit}")
            if st.kOrder_id != -1:
                self._close_order(st.kOrder_id, st.price)
            st.trailing_stop_active = False
            st.trailing_stop_price = Decimal('0.0')
            st.trailing_take_profit = Decimal('0.0')
            st.trailing_stop_entry = Decimal('0.0')
            st.trailing_stop_side = ""
            st.has_open_short = False
            st.kOrder_id = -1

    def _get_next_topological_target(self, side: str, current_price: Decimal) -> Decimal:
        st = self.state
        for ji in range(st.y + 1, X_PERIOD - 1):
            jidx = ji - (st.y + 1)
            if side == "BUY":
                if jidx < len(st.Premium) and st.Premium[jidx] > current_price and st.Premium[jidx] != Decimal('0.0'):
                    return st.Premium[jidx]
            elif side == "SELL":
                if jidx < len(st.Discount) and st.Discount[jidx] < current_price and st.Discount[jidx] != Decimal('0.0'):
                    return st.Discount[jidx]
        if side == "BUY" and st.Sale > current_price:
            return st.Sale
        if side == "SELL" and st.Stock < current_price:
            return st.Stock
        return Decimal('0.0')

    def _will_pass_spread_in_pnl(self, entry_price: Decimal, target_price: Decimal, side: str) -> bool:
        if len(self.price_history) > 0:
            last = self.price_history[-1]
            current_spread = last.ask - last.bid
        else:
            current_spread = Decimal('0.0')
        point_size = self._point_size if self._point_size > Decimal('0.0') else Decimal('0.00001')
        if point_size <= Decimal('0.0'):
            return False
        com_price = self._com_price_frozen
        if com_price < Decimal('0.0'):
            com_price = Decimal('0.0')
        friction_points = (current_spread + com_price) / point_size
        projected_distance = abs(target_price - entry_price)
        projected_pnl_points = projected_distance / point_size
        safety_buffer = Decimal('1.0')
        if side == "BUY":
            if target_price <= entry_price:
                return False
            return projected_pnl_points > (friction_points + safety_buffer)
        if side == "SELL":
            if target_price >= entry_price:
                return False
            return projected_pnl_points > (friction_points + safety_buffer)
        return False

    def _Top(self, emit_toast: bool = True) -> None:
        st = self.state
        _digits = SYMBOL_DIGITS.get(SYMBOL, SYMBOL_DIGITS_DEFAULT)
        price_str = f"{st.price:.{_digits}f}"
        created = False
        if not any(abs(p - st.price) < Decimal('0.00001') for p in st.BL):
            st.BL.append(st.price)
            st.BL_type.append("top")
            st.FVG += 1
            anchor_idx = len(st.BL) - 1
            st.bL = price_str
            logger.info(f"▲ Top(): Blue FVG line at {price_str}, FVG={st.FVG}, idx={anchor_idx}")
            created = True
            if self._bridge_publish_callback:
                try:
                    self._bridge_publish_callback("top", price_str)
                except Exception as e:
                    logger.warning(f"_bridge_publish_callback failed: {e}")
        _emit_toast("fvg", {
            "action": "commit" if created else "duplicate",
            "type": "top",
            "price": price_str,
            "idx": int(len(st.BL) - 1) if created else int(st.FVG),
            "tick": int(st.tick),
        })

    def _Bott(self, emit_toast: bool = True) -> None:
        st = self.state
        _digits = SYMBOL_DIGITS.get(SYMBOL, SYMBOL_DIGITS_DEFAULT)
        price_str = f"{st.price:.{_digits}f}"
        created = False
        if not any(abs(p - st.price) < Decimal('0.00001') for p in st.BL):
            st.BL.append(st.price)
            st.BL_type.append("bott")
            st.FVG += 1
            anchor_idx = len(st.BL) - 1
            st.bL = price_str
            logger.info(f"▼ Bott(): Red FVG line at {price_str}, FVG={st.FVG}, idx={anchor_idx}")
            created = True
            if self._bridge_publish_callback:
                try:
                    self._bridge_publish_callback("bott", price_str)
                except Exception as e:
                    logger.warning(f"_bridge_publish_callback failed: {e}")
        _emit_toast("fvg", {
            "action": "commit" if created else "duplicate",
            "type": "bott",
            "price": price_str,
            "idx": int(len(st.BL) - 1) if created else int(st.FVG),
            "tick": int(st.tick),
        })

    def _emit_execution_toast(self, event: str, price: Decimal, side: str, ticket: int, reason: str) -> None:
        st = self.state
        _emit_toast("execution", {
            "event": event,
            "price": str(price),
            "side": side,
            "ticket": int(ticket),
            "reason": reason,
            "tick": int(st.tick),
        })
        if not PUSH_ON_EXECUTION:
            self._send_execution_alert(event, price, side, ticket, reason)

    def _populate_indicator_matrix(self) -> None:
        with _ENGINE_LOCK:
            self._populate_indicator_matrix_locked()

    def _populate_indicator_matrix_locked(self) -> None:
        st = self.state
        if len(self.ohlcv_history) < MIN_HISTORY_WINDOW:
            return
        _X = X_PERIOD
        _y = st.y
        size = _X - _y
        if size <= 0:
            return
        end = len(self.ohlcv_history)
        for j in range(_y + 1, _X):
            idx = j - (_y + 1)
            if idx < 0 or idx >= size:
                continue
            col_i = j - (_y + 1)
            if col_i < 0 or col_i >= len(st.iA[0]):
                continue
            self._normalize(j)
            self._unify(j)
            self._indicator_populate_count += 13

    def _force_initialization(self) -> None:
        st = self.state
        if st.FG:
            return
        if st.price <= Decimal('0.0'):
            logger.warning("⏳ Cannot force-init: price not yet available")
            return
        logger.info("🚀 First valid tick detected. Forcing engine initialization...")
        if not st.signature:
            st.D = st.price
            st.E = st.price
        size = X_PERIOD - st.y
        if size <= 0:
            size = X_PERIOD - Y_START
        st.X_scan = st.y
        st.Y_scan = st.y
        if len(st.k) != size:
            st.k = [False] * size
            st.l = [False] * size
            st.HH = [Decimal('0.0')] * size
            st.LL = [Decimal('0.0')] * size
            st.Premium = [Decimal('0.0')] * size
            st.Discount = [Decimal('0.0')] * size
            st.Regime = ["sRange"] * size
        if len(self.ohlcv_history) >= 2:
            iH = self.ohlcv_history[-2]["high"]
            iL = self.ohlcv_history[-2]["low"]
        elif len(self.ohlcv_history) == 1:
            iH = self.ohlcv_history[-1]["high"]
            iL = self.ohlcv_history[-1]["low"]
        else:
            iH = st.price
            iL = st.price
        for j in range(st.y + 1, X_PERIOD):
            self._F(j, iH, iL)
        st.FG = True
        logger.info(f"✅ Engine initialized on first tick at price={st.price}")

    def _on_tick(self, price_data: PriceData) -> None:
        with _ENGINE_LOCK:
            self._on_tick_locked(price_data)

    def _on_tick_locked(self, price_data: PriceData) -> None:
        st = self.state
        self._tick_log_counter += 1

        if price_data.bid <= Decimal('0.0'):
            logger.warning(f"⚠️ Tick #{st.tick} with non-positive bid ({price_data.bid}). Skipping state machine.")
            return
        if price_data.ask <= Decimal('0.0'):
            logger.warning(f"⚠️ Tick #{st.tick} with non-positive ask ({price_data.ask}); repairing ask to bid ({price_data.bid}).")
            price_data.ask = price_data.bid
        elif price_data.ask < price_data.bid:
            logger.warning(f"⚠️ Tick #{st.tick} with inverted spread (bid={price_data.bid}, ask={price_data.ask}); repairing ask to bid.")
            price_data.ask = price_data.bid

        try:
            if getattr(self, "ordered_feed", None) is not None:
                self.ordered_feed.enqueue(price_data)
                _drained = self.ordered_feed.drain_one()
        except Exception:
            _drained = None
        st.price = price_data.bid
        if len(self.ohlcv_history) >= 2:
            st.Price = self.ohlcv_history[-2]["close"]
            st.iPrice = self.ohlcv_history[-2]["close"]
            st.open = self.ohlcv_history[-2]["open"]
            st.iH = self.ohlcv_history[-2]["high"]
            st.iL = self.ohlcv_history[-2]["low"]
        elif len(self.ohlcv_history) == 1:
            st.Price = self.ohlcv_history[-1]["close"]
            st.iPrice = self.ohlcv_history[-1]["close"]
            st.open = self.ohlcv_history[-1]["open"]
            st.iH = self.ohlcv_history[-1]["high"]
            st.iL = self.ohlcv_history[-1]["low"]
        else:
            st.Price = price_data.close
            st.iPrice = st.price
            st.open = st.price
            st.iH = st.price
            st.iL = st.price

        if st.price <= Decimal('0.0'):
            logger.warning(f"⚠️ Tick #{st.tick} with non-positive price. Skipping state machine.")
            return

        is_now = self.ohlcv_history[-1]["timestamp"] if self.ohlcv_history else datetime.now()

        self._maintain_fvg_lines()

        if not st.FG:
            self._force_initialization()

        self._execute_trailing_stop()

        # : OnPoint / OnBar / OnCall execute BEFORE the tick-log block
        # so the regime string reported by the log block reflects the
        # current tick's classification, not the previous tick's.
        self._on_point()
        st.C = self._O(st.iO, st.O, st.J, st.C, st.Cc)
        st.c = self._O(st.io, st.o, st.iJ, st.c, st.cC)
        self._on_call()
        self._J()

        if is_now != st.t:
            self._on_bar()
            st.C = self._O(st.iO, st.O, st.J, st.C, st.Cc)
            st.c = self._O(st.io, st.o, st.iJ, st.c, st.cC)

        if st.J == st.y + 1 and st.J != 2:
            self._on_stand()
            self._J()
            st.C = self._O(st.iO, st.O, st.J, st.C, st.Cc)
            st.c = self._O(st.io, st.o, st.iJ, st.c, st.cC)
            if st.iO != 2:
                if st.J >= st.iO:
                    j = MIN_PERIOD
                    st.O = j
                    idx_j = j - (st.y + 1)
                    if 0 <= idx_j < len(st.Regime):
                        if is_now != st.t:
                            if self._on_fire(j, "Stable", "tRange"):
                                self._F(j, st.iH, st.iL)
                                st.Regime[idx_j] = "tRange"
                            else:
                                st.Regime[idx_j] = "sRange"
                        else:
                            st.Regime[idx_j] = "sRange"
                else:
                    j = MIN_PERIOD + 1
                    st.O = j
                    idx_j = j - (st.y + 1)
                    if 0 <= idx_j < len(st.Regime):
                        if is_now != st.t:
                            if self._on_fire(j, "Stable", "tRange"):
                                self._F(j, st.iH, st.iL)
                                st.Regime[idx_j] = "tRange"
                            else:
                                st.Regime[idx_j] = "sRange"
                        else:
                            st.Regime[idx_j] = "sRange"
            else:
                st.O = 2
            if st.io != 2:
                if st.iJ >= st.io:
                    st.o = MIN_PERIOD
                else:
                    st.o = MIN_PERIOD + 1
            else:
                st.o = 2

        if st.J == X_PERIOD - 1:
            self._on_track()
            self._J()
            st.C = self._O(st.iO, st.O, st.J, st.C, st.Cc)
            st.c = self._O(st.io, st.o, st.iJ, st.c, st.cC)
            if st.iO != 4 * MAX_PERIOD:
                if st.J >= st.iO:
                    j = MAX_PERIOD - 1
                    st.O = j
                    idx_j = j - (st.y + 1)
                    if 0 <= idx_j < len(st.Regime):
                        if is_now != st.t:
                            if self._on_fire(j, "Stable", "tRange"):
                                self._F(j, st.iH, st.iL)
                                st.Regime[idx_j] = "tRange"
                            else:
                                st.Regime[idx_j] = "sRange"
                        else:
                            st.Regime[idx_j] = "sRange"
                else:
                    j = MAX_PERIOD
                    st.O = j
                    idx_j = j - (st.y + 1)
                    if 0 <= idx_j < len(st.Regime):
                        if is_now != st.t:
                            if self._on_fire(j, "Stable", "tRange"):
                                self._F(j, st.iH, st.iL)
                                st.Regime[idx_j] = "tRange"
                            else:
                                st.Regime[idx_j] = "sRange"
                        else:
                            st.Regime[idx_j] = "sRange"
            else:
                st.O = X_PERIOD - 1
            if st.io != 4 * MAX_PERIOD:
                if st.iJ >= st.io:
                    st.o = MAX_PERIOD - 1
                else:
                    st.o = MAX_PERIOD
            else:
                st.o = X_PERIOD - 1

        if st.Z != X_PERIOD - 1:
            h_idx = st.iZ - (st.y + 1)
            if st.Z != st.y + 1 and 0 <= h_idx < len(st.k) and st.k[h_idx]:
                st.h = st.iZ
                self._on_goe()
            else:
                h_idx = st.iz - (st.y + 1)
                if (0 <= h_idx < len(st.k) and st.k[h_idx] and st.z != st.y + 1 and st.z != X_PERIOD - 1):
                    st.h = st.iz
                    self._on_goe()
                else:
                    h_idx = st.io - (st.y + 1)
                    if (0 <= h_idx < len(st.k) and st.k[h_idx] and st.o != st.y + 1 and st.o != X_PERIOD - 1):
                        st.h = st.io
                        self._on_goe()
                    else:
                        h_idx = st.iO - (st.y + 1)
                        if (0 <= h_idx < len(st.k) and st.k[h_idx] and st.O != st.y + 1 and st.O != X_PERIOD - 1):
                            st.h = st.iO
                            self._on_goe()

        if st.W != X_PERIOD - 1:
            h_idx = st.iW - (st.y + 1)
            if st.W != st.y + 1 and 0 <= h_idx < len(st.l) and st.l[h_idx]:
                st.h = st.iW
                self._on_toe()
            else:
                h_idx = st.iw - (st.y + 1)
                if (0 <= h_idx < len(st.l) and st.l[h_idx] and st.w != st.y + 1 and st.w != X_PERIOD - 1):
                    st.h = st.iw
                    self._on_toe()
                else:
                    h_idx = st.io - (st.y + 1)
                    if (0 <= h_idx < len(st.l) and st.l[h_idx] and st.o != st.y + 1 and st.o != X_PERIOD - 1):
                        st.h = st.io
                        self._on_toe()
                    else:
                        h_idx = st.iO - (st.y + 1)
                        if (0 <= h_idx < len(st.l) and st.l[h_idx] and st.O != st.y + 1 and st.O != X_PERIOD - 1):
                            st.h = st.iO
                            self._on_toe()

        if st.GF:
            self.OnReInit()
            st.GF = False

        # : tick-log block placed after all state-machine work.
        if self._tick_log_counter >= 100:
            self._tick_log_counter = 0
            idx = st.Z - (st.y + 1)
            regime = st.Regime[idx] if 0 <= idx < len(st.Regime) else "?"
            logger.info(f"⚡ Tick #{st.tick}: Price={st.price}, Signal={st.signal}, FG={st.FG}, Regime={regime}, X_scan={st.X_scan}, Y_scan={st.Y_scan}, bars={st.bar_close_count}, signals={len(st.signal_history)}, provider={st.last_provider}")

        self._step_seed_from_tick()
        st.tick += 1
        if st.ab != st.ba:
            st.ab = st.ba
        st.tick_tock = False
        st.t = is_now

    def _step_seed_from_tick(self) -> None:
        # Backend x lift: x is derived here, in the backend, from the
        # backend ordered price and prevPrice. The frontend never sends x.
        try:
            seed = getattr(self, "seed", None)
            if seed is None:
                return
            # FG x priority: crawler hash fraction first, price fallback labelled, tick last.
            try:
                _cr = getattr(getattr(self, 'crawler', None), 'last_hash_frac', None)
                if _cr is not None:
                    seed.step(_cr, x_source='crawler-hash'); return
            except Exception: pass
            prev = None
            curr = None
            if len(self.ohlcv_history) >= 2:
                prev = self.ohlcv_history[-2].get("close")
                curr = self.ohlcv_history[-1].get("close")
            elif len(self.ohlcv_history) == 1:
                prev = self.ohlcv_history[-1].get("close")
                curr = self.state.price
            else:
                curr = self.state.price
            if prev is None or curr is None:
                x = PyFraction(1, 100)
                seed.step(x, x_source='tick-fallback'); return
            else:
                try:
                    delta = abs(PyFraction(str(curr)) - PyFraction(str(prev)))
                except Exception:
                    delta = PyFraction(0, 1)
                x = (delta / PyFraction(10000, 1)) if delta != 0 else PyFraction(1, 100)
            seed.step(x, x_source='price-fallback')
        except Exception as e:
            logger.warning(f"Seed step from tick failed: {e}")

    def _format_comment_line(self) -> str:
        st = self.state
        y = st.y
        def _k(idx):
            i = idx - (y + 1)
            return st.k[i] if 0 <= i < len(st.k) else False
        def _l(idx):
            i = idx - (y + 1)
            return st.l[i] if 0 <= i < len(st.l) else False
        line1 = f"    ^{st.iZ}:{st.Z}|{st.iz}:{st.z}={_k(st.Z)}|{_k(st.z)}                                           <! †, ‡, # — ↑(0)|↓(1): {st.prime} {st.dime}{st.mem} >"
        line2 = f"\n Lim{st.iO}:{st.O}^{_k(st.O)}_{_l(st.O)}.{st.io}:{st.o}^{_k(st.o)}_{_l(st.o)}={st.h}.{st.C}:{st.c}             <! 100%✓ >"
        line3 = f"\n    _{st.iW}:{st.W}|{st.iw}:{st.w}={_l(st.W)}|{_l(st.w)}                                                 <! Natalia Tanyatia >"
        return line1 + line2 + line3

    def _maintain_fvg_lines(self) -> None:
        st = self.state
        if st.FVG < 0:
            return
        price = st.price
        i = 0
        removed_anchors = []
        while i < len(st.BL):
            price_line = st.BL[i]
            line_type = st.BL_type[i] if i < len(st.BL_type) else "top"
            if price_line <= Decimal('0.0'):
                i += 1
                continue
            if line_type == "top" and (st.A or not st.B) and price_line <= price and st.E != Decimal('0.0'):
                logger.info(f"🔵 FVG maintenance: remove blue @ {price_line}")
                removed_anchors.append({"idx": i, "price": price_line, "type": "top"})
                st.BL.pop(i)
                if i < len(st.BL_type):
                    st.BL_type.pop(i)
                st.FVG -= 1
                continue
            if line_type == "bott" and (st.B or not st.A) and price_line >= price and st.D != Decimal('0.0'):
                logger.info(f"🔴 FVG maintenance: remove red @ {price_line}")
                removed_anchors.append({"idx": i, "price": price_line, "type": "bott"})
                st.BL.pop(i)
                if i < len(st.BL_type):
                    st.BL_type.pop(i)
                st.FVG -= 1
                continue
            i += 1
        for anchor in removed_anchors:
            _emit_toast("fvg", {
                "action": "remove",
                "type": anchor["type"],
                "price": str(anchor["price"]),
                "idx": int(anchor["idx"]),
                "tick": int(st.tick),
            })

    def update_price_from_feed(self) -> None:
        data = self.feed.get_intraday()
        if not data:
            self._consecutive_zero_prices += 1
            now = datetime.now()
            if self._last_relay_warn is None or (now - self._last_relay_warn).seconds >= 60:
                self._last_relay_warn = now
                logger.warning(f"⚠️ No data from relay for {self.feed.active_symbol()} (consecutive={self._consecutive_zero_prices})")
            return
        bid = data["close"]
        ask = data["close"]
        if bid <= Decimal('0.0'):
            self._consecutive_zero_prices += 1
            return
        volume = data.get("volume", Decimal('0.0'))
        timestamp = data.get("timestamp", datetime.now())
        provider = str(data.get("provider", self.feed.last_provider()))
        self._consecutive_zero_prices = 0
        self.update_price(bid, ask, volume, timestamp, provider)

    def update_price(self, bid: Decimal, ask: Decimal, volume: Decimal = Decimal('0.0'), timestamp: Optional[datetime] = None, provider: str = "") -> None:
        if timestamp is None:
            timestamp = datetime.now()
        # : reject zero/negative/invalid bid at the boundary. No bar may
        # enter ohlcv_history with a placeholder price. This is the single
        # gate that keeps every bar in ohlcv_history a real observation.
        if not isinstance(bid, Decimal) or bid <= Decimal('0.0'):
            logger.warning(f"update_price rejected non-positive bid: {bid}")
            return
        if not isinstance(ask, Decimal) or ask <= Decimal('0.0'):
            logger.warning(f"update_price rejected non-positive ask: {ask}; repairing ask to bid.")
            ask = bid
        if ask < bid:
            logger.warning(f"update_price inverted spread (bid={bid}, ask={ask}); repairing ask to bid.")
            ask = bid
        if not isinstance(volume, Decimal) or volume < Decimal('0.0'):
            volume = Decimal('0.0')
        self.state.price = bid
        self.state.Price = (bid + ask) / Decimal('2.0')
        if volume > Decimal('0.0'):
            self.state.last_volume = volume
        if provider:
            self.state.last_provider = provider
        self._price_update_counter += 1
        price_data = PriceData(
            bid=bid, ask=ask, close=(bid + ask) / Decimal('2.0'),
            open=bid, high=max(bid, ask), low=min(bid, ask),
            volume=volume, timestamp=timestamp, provider=provider,
        )
        self.price_history.append(price_data)
        if len(self.price_history) > 1000:
            self.price_history = self.price_history[-1000:]

        bar_closed = False
        if self._last_price_update is None:
            bar_closed = True
        else:
            current_min = timestamp.replace(second=0, microsecond=0)
            prev_min = self._last_price_update.replace(second=0, microsecond=0)
            if current_min != prev_min:
                bar_closed = True

        if bar_closed:
            self._bar_open = True
            self._last_price_update = timestamp
            self._bar_index += 1
            self.state.bar_close_count += 1
            self.ohlcv_history.append({
                "open": price_data.open, "high": price_data.high,
                "low": price_data.low, "close": price_data.close,
                "volume": price_data.volume, "timestamp": timestamp,
                "provider": provider,
            })
            if len(self.ohlcv_history) > 200:
                self.ohlcv_history = self.ohlcv_history[-200:]
            logger.info(f"📊 BAR CLOSE #{self.state.bar_close_count} at {timestamp.isoformat()} close={price_data.close} volume={price_data.volume} provider={provider} (ohlcv={len(self.ohlcv_history)})")
        else:
            self._bar_open = False
            if self.ohlcv_history:
                last = self.ohlcv_history[-1]
                # : only update if the existing bar has a real price.
                if isinstance(last.get("close"), Decimal) and last["close"] > Decimal('0.0'):
                    last["high"] = max(last["high"], price_data.high)
                    last["low"] = min(last["low"], price_data.low)
                    last["close"] = price_data.close
                    last["volume"] = last.get("volume", Decimal('0.0')) + price_data.volume
                    if provider:
                        last["provider"] = provider

        self._on_tick(price_data)

    def _send_signal_alert(self) -> None:
        st = self.state
        target_chat = st.chat_id
        if target_chat is None and st.webapp_user_id is not None:
            target_chat = st.webapp_user_id
        if not target_chat or not self.application:
            return
        if not self._alert_delivery_enabled:
            return
        direction = "↟" if st.price > st.signal else "↡"
        m_local = st.authoritative_m
        n_local = st.authoritative_n
        h_idx = st.h - (st.y + 1)
        m_at_h = 1 if (0 <= h_idx < len(st.k) and st.k[h_idx]) else 0
        n_at_h = 1 if (0 <= h_idx < len(st.l) and st.l[h_idx]) else 0
        condition_met = (m_local >= 12) or (n_local >= 12)
        idx = st.Z - (st.y + 1)
        regime = st.Regime[idx] if 0 <= idx < len(st.Regime) else "Unknown"
        msg = (
            f"🎯 *ÆEA 𝒮_signal ℰ_alert*\n"
            f"📊 *𝒮_Direction:* {_md_escape(direction)}\n"
            f"🎯 *𝒮_Signal_Level:* {_md_escape(st.signal)}\n"
            f"💰 *Current Price:* {_md_escape(st.price)}\n"
            f"📊 *ℛ_regime:* {_md_escape(regime)}\n"
            f"⚖️ *Imbalance @ h={_md_escape(st.h)}:* m={_md_escape(m_at_h)}, n={_md_escape(n_at_h)}\n"
            f"⚖️ *Local m/n:* {_md_escape(m_local)}/{_md_escape(n_local)}\n"
            f"✅ *H/L gate (m>=12 or n>=12):* {'✅ 𝒜₃ MET' if condition_met else '❌ 𝒜₄ NOT MET'}\n"
            f"🔄 *Tick Count:* {_md_escape(st.tick)}\n"
            f"💎 Natalia Tanyatia"
        )
        bot = BRIDGE_ENGINE_REF.get("bot")
        if bot is not None and hasattr(bot, "_send_message_sync"):
            reply_to = st.last_inbound_message_id if isinstance(st.last_inbound_message_id, int) else None
            ok = bot._send_message_sync(
                chat_id=target_chat,
                text=msg,
                parse_mode="Markdown",
                reply_to_message_id=reply_to,
            )
            if ok:
                logger.info(f"📡 Signal alert sent to {target_chat} reply_to={reply_to} (tick={st.tick})")
            else:
                logger.warning(f"❌ Signal alert send failed for {target_chat} (tick={st.tick})")
            return
        app = self.application
        if app is not None and hasattr(app, "_send_message_sync"):
            reply_to = st.last_inbound_message_id if isinstance(st.last_inbound_message_id, int) else None
            ok = app._send_message_sync(
                chat_id=target_chat,
                text=msg,
                parse_mode="Markdown",
                reply_to_message_id=reply_to,
            )
            if ok:
                logger.info(f"📡 Signal alert sent via engine.application to {target_chat} reply_to={reply_to} (tick={st.tick})")
            else:
                logger.warning(f"❌ Signal alert send via engine.application failed for {target_chat} (tick={st.tick})")
            return
        logger.warning("❌ Signal alert skipped: bot reference or _send_message_sync unavailable")

    def _send_execution_alert(self, event: str, price: Decimal, side: str, ticket: int, reason: str) -> None:
        st = self.state
        target_chat = st.chat_id
        if target_chat is None and st.webapp_user_id is not None:
            target_chat = st.webapp_user_id
        if not target_chat or not self.application:
            return
        if not self._alert_delivery_enabled:
            return
        emoji_map = {
            "Bull": "🐂", "Bear": "🐻", "Whisky": "🥃", "Wine": "🍷",
            "Watter": "💧", "Blood": "🩸", "Hawk": "🦅", "Dove": "🕊️",
            "Diamond": "🔷", "Ruby": "🔻", "Top": "▲", "Bott": "▼",
            "A": "🅰️", "B": "🅱️", "ManualOrder": "📝", "ManualClose": "✂️",
            "ManualOpen": "➕", "Pending": "⏳",
        }
        emoji = emoji_map.get(event, "⚡")
        cs_event = _cs_exec(event)
        side_str = side if side else "NONE"
        ticket_str = f"#{ticket}" if ticket != -1 else "—"
        reason_str = f" | {_md_escape(reason)}" if reason else ""
        msg = (
            f"{emoji} *ÆEA ℰ_exec*\n"
            f"📛 *Event:* {_md_escape(cs_event)}\n"
            f"📊 *Side:* {_md_escape(_cs(side_str))}\n"
            f"🎫 *Ticket:* {_md_escape(ticket_str)}\n"
            f"💰 *Price:* {_md_escape(price)}{reason_str}\n"
            f"🔄 *Tick:* {_md_escape(st.tick)}\n"
            f"💎 Natalia Tanyatia"
        )
        bot = BRIDGE_ENGINE_REF.get("bot")
        if bot is not None and hasattr(bot, "_send_message_sync"):
            reply_to = st.last_inbound_message_id if isinstance(st.last_inbound_message_id, int) else None
            ok = bot._send_message_sync(
                chat_id=target_chat,
                text=msg,
                parse_mode="Markdown",
                reply_to_message_id=reply_to,
            )
            if ok:
                logger.info(f"📡 Execution alert ({event}) sent to {target_chat} reply_to={reply_to} (tick={st.tick})")
            else:
                logger.warning(f"❌ Execution alert ({event}) send failed (tick={st.tick})")
            return
        app = self.application
        if app is not None and hasattr(app, "_send_message_sync"):
            reply_to = st.last_inbound_message_id if isinstance(st.last_inbound_message_id, int) else None
            ok = app._send_message_sync(
                chat_id=target_chat,
                text=msg,
                parse_mode="Markdown",
                reply_to_message_id=reply_to,
            )
            if ok:
                logger.info(f"📡 Execution alert ({event}) sent via engine.application to {target_chat} reply_to={reply_to} (tick={st.tick})")
            else:
                logger.warning(f"❌ Execution alert ({event}) send via engine.application failed (tick={st.tick})")
            return
        logger.warning("❌ Execution alert skipped: bot reference or _send_message_sync unavailable")

    def get_signal_status(self) -> Dict[str, Any]:
        st = self.state
        h_idx = st.h - (st.y + 1)
        m_at_h = 1 if (0 <= h_idx < len(st.k) and st.k[h_idx]) else 0
        n_at_h = 1 if (0 <= h_idx < len(st.l) and st.l[h_idx]) else 0
        m_local = st.authoritative_m
        n_local = st.authoritative_n
        condition_met = (m_local >= 12) or (n_local >= 12)
        idx = st.Z - (st.y + 1)
        regime = st.Regime[idx] if 0 <= idx < len(st.Regime) and st.Regime[idx] else "Unknown"
        return {
            "signal": float(st.signal),
            "price": float(st.price),
            "signature": st.signature,
            "KC": bool(st.KC),
            "prime": int(st.prime),
            "dime": int(st.dime),
            "mem": int(st.mem),
            "tag": int(st.tag),
            "invert": bool(st.invert),
            "safety": bool(st.safety),
            "m_count": m_local,
            "n_count": n_local,
            "m_at_h": m_at_h,
            "n_at_h": n_at_h,
            "h_bar": int(st.h),
            "condition_met": condition_met,
            "regime": regime,
            "symbol": SYMBOL,
            "tick": st.tick,
            "timestamp": datetime.now().isoformat(),
            "engine_initialized": st.FG,
            "indicator_populate_count": int(self._indicator_populate_count),
            "imbalance_fire_count": int(self._imbalance_fire_count),
            "trailing_stop_active": st.trailing_stop_active,
            "trailing_stop_price": str(st.trailing_stop_price),
            "trailing_take_profit": str(st.trailing_take_profit),
            "trailing_stop_entry": str(st.trailing_stop_entry),
            "trailing_stop_side": st.trailing_stop_side,
            "has_open_long": bool(st.has_open_long),
            "has_open_short": bool(st.has_open_short),
            "lOrder_id": int(st.lOrder_id),
            "kOrder_id": int(st.kOrder_id),
            "on_track_runs": int(st.on_track_runs),
            "on_stand_runs": int(st.on_stand_runs),
            "last_kronecker_bar": int(self._last_kronecker_bar),
            "last_kronecker_m": int(st.last_kronecker_m),
            "last_kronecker_n": int(st.last_kronecker_n),
            "last_kronecker_h": int(st.last_kronecker_h),
            "authoritative_m": int(st.authoritative_m),
            "authoritative_n": int(st.authoritative_n),
            "authoritative_h": int(st.authoritative_h),
            "X_scan": int(st.X_scan),
            "Y_scan": int(st.Y_scan),
            "S": int(st.S),
            "T": int(st.T),
            "r": int(st.r),
            "ir": int(st.ir),
            "iATR": float(st.iATR),
            "iStdDev": float(st.iStdDev),
            "iIHKk": float(st.iIHKk),
            "iIHKt": float(st.iIHKt),
            "signal_count": len(st.signal_history),
            "last_signal_at": st.last_signal_at,
            "bar_close_count": int(st.bar_close_count),
            "ohlcv_count": len(self.ohlcv_history),
            "market_m": int(st.authoritative_m),
            "market_n": int(st.authoritative_n),
            "market_imbalance": int(st.authoritative_m) - int(st.authoritative_n) - 2,
            "market_regime": "BULLISH" if (int(st.authoritative_m) - int(st.authoritative_n) - 2) > 2 else ("BEARISH" if (int(st.authoritative_m) - int(st.authoritative_n) - 2) < -2 else "NEUTRAL"),
            "A": bool(st.A),
            "B": bool(st.B),
            "C": bool(st.C),
            "c": bool(st.c),
            "tick_tock": bool(st.tick_tock),
            "Z": int(st.Z),
            "z": int(st.z),
            "O": int(st.O),
            "o": int(st.o),
            "W": int(st.W),
            "w": int(st.w),
            "I": int(st.I),
            "iI": int(st.iI),
            "J": int(st.J),
            "iJ": int(st.iJ),
            "iZ": int(st.iZ),
            "iz": int(st.iz),
            "iW": int(st.iW),
            "iw": int(st.iw),
            "iO": int(st.iO),
            "io": int(st.io),
            "lPass": str(st.lPass),
            "ilPass": str(st.ilPass),
            "kPass": str(st.kPass),
            "ikPass": str(st.ikPass),
            "comment_line": self._format_comment_line(),
            "last_provider": st.last_provider,
            "last_volume": str(st.last_volume),
            "projection_computed_at": st.projection_computed_at,
            "projection_trigger": st.projection_trigger,
            "last_inbound_message_id": st.last_inbound_message_id,
        }

    def get_regime_map(self) -> List[Dict[str, Any]]:
        st = self.state
        out = []
        for i, regime in enumerate(st.Regime):
            prem = st.Premium[i] if i < len(st.Premium) else Decimal('0.0')
            disc = st.Discount[i] if i < len(st.Discount) else Decimal('0.0')
            hh = st.HH[i] if i < len(st.HH) else Decimal('0.0')
            ll = st.LL[i] if i < len(st.LL) else Decimal('0.0')
            k_flag = st.k[i] if i < len(st.k) else False
            l_flag = st.l[i] if i < len(st.l) else False
            out.append({
                "index": i,
                "regime": regime,
                "k": bool(k_flag),
                "l": bool(l_flag),
                "premium": float(prem),
                "discount": float(disc),
                "hh": float(hh),
                "ll": float(ll),
            })
        return out

    def get_indicator_series(self, name: str, count: int = 80) -> List[float]:
        st = self.state
        idx = INDICATOR_NAMES.index(name) if name in INDICATOR_NAMES else -1
        if idx < 0:
            if name == "IchimokuK":
                return [float(v) for v in st.IHKk[-count:]]
            if name == "IchimokuT":
                return [float(v) for v in st.IHKt[-count:]]
            if name == "ATR":
                return [float(v) for v in st.ATR[-count:]]
            if name == "StdDev":
                return [float(v) for v in st.StdDev[-count:]]
            return []
        row = st.iA[idx] if idx < len(st.iA) else []
        return [float(v) for v in row[-count:]]

    def place_order(self, side: str, lot: Decimal, sl: Decimal, tp: Decimal) -> Dict[str, Any]:
        st = self.state
        if st.price <= Decimal('0.0'):
            return {"error": "no_price"}
        if side not in ("BUY", "SELL"):
            return {"error": "invalid_side"}
        if lot <= Decimal('0.0'):
            return {"error": "invalid_lot"}
        entry = st.price
        if sl <= Decimal('0.0'):
            sl = Decimal('0.0')
        if tp <= Decimal('0.0'):
            tp = Decimal('0.0')
        ticket = self._open_order(side, entry, sl, tp, lot)
        if side == "BUY":
            st.has_open_long = True
            st.lOrder_id = ticket
            st.trailing_stop_entry = entry
            st.trailing_stop_side = "LONG"
        else:
            st.has_open_short = True
            st.kOrder_id = ticket
            st.trailing_stop_entry = entry
            st.trailing_stop_side = "SHORT"
        logger.info(f"📝 place_order: {side} #{ticket} @ {entry}, lot={lot}, sl={sl}, tp={tp}")
        self._emit_execution_toast("ManualOrder", entry, side, ticket, "manual")
        return {"ok": True, "ticket": ticket, "side": side, "entry": float(entry), "sl": float(sl), "tp": float(tp), "order": {"ticket": ticket, "side": side, "volume": float(lot), "lot": float(lot), "entry": float(entry), "price": float(entry), "sl": float(sl), "tp": float(tp), "status": "open"}}

    def close_order(self, ticket: int = None, all: bool = False) -> Dict[str, Any]:
        st = self.state
        closed = []
        if all:
            for o in self.orders:
                if o.closed_at is None:
                    o.closed_at = datetime.now()
                    o.close_price = st.price
                    closed.append(o.ticket)
            st.has_open_long = False
            st.has_open_short = False
            st.lOrder_id = -1
            st.kOrder_id = -1
            st.trailing_stop_active = False
            st.trailing_stop_price = Decimal('0.0')
            st.trailing_take_profit = Decimal('0.0')
            st.trailing_stop_entry = Decimal('0.0')
            st.trailing_stop_side = ""
        else:
            if ticket is None:
                return {"error": "no_ticket"}
            for o in self.orders:
                if o.ticket == ticket and o.closed_at is None:
                    o.closed_at = datetime.now()
                    o.close_price = st.price
                    closed.append(o.ticket)
                    if o.side == "BUY":
                        st.has_open_long = False
                        st.lOrder_id = -1
                    else:
                        st.has_open_short = False
                        st.kOrder_id = -1
                    break
        logger.info(f"📝 close_order: closed={closed}")
        if closed:
            self._emit_execution_toast("ManualClose", st.price, "CLOSE", closed[0] if len(closed) == 1 else -1, "manual")
        return {"ok": True, "closed": closed}

    def list_orders(self) -> List[Dict[str, Any]]:
        st = self.state
        out = []
        for o in self.orders:
            if o.closed_at is not None:
                continue
            pnl = o.pnl(st.price) if st.price > Decimal('0.0') else Decimal('0.0')
            out.append({
                "ticket": o.ticket,
                "side": o.side,
                "entry": float(o.entry),
                "sl": float(o.sl),
                "tp": float(o.tp),
                "lot": float(o.lot),
                "pnl": float(pnl),
                "opened_at": o.opened_at.isoformat(),
            })
        return out

    def get_settings(self) -> Dict[str, Any]:
        st = self.state
        return {
            "max": int(MAX_PERIOD),
            "min": int(MIN_PERIOD),
            "Cc": bool(st.Cc),
            "cC": bool(st.cC),
            "Memory": int(Memory),
            "safetyOffSwitch": bool(st.safety),
            "StopLoss": str(STOP_LOSS),
            "TakeProfit": str(TAKE_PROFIT),
            "lot": str(LOT_SIZE),
            "slip": int(SLIPPAGE),
            "Commssion": str(COMMISSION),
        }

    def apply_settings(self, s: Dict[str, Any]) -> Dict[str, Any]:
        global MAX_PERIOD, MIN_PERIOD, X_PERIOD, Y_START, COMMISSION, STOP_LOSS, TAKE_PROFIT, LOT_SIZE, SLIPPAGE, Memory
        st = self.state
        with _ENGINE_LOCK:
            return self._apply_settings_locked(s)

    def _apply_settings_locked(self, s: Dict[str, Any]) -> Dict[str, Any]:
        global MAX_PERIOD, MIN_PERIOD, X_PERIOD, Y_START, COMMISSION, STOP_LOSS, TAKE_PROFIT, LOT_SIZE, SLIPPAGE, Memory
        st = self.state
        try:
            errors = []
            new_max = MAX_PERIOD
            new_min = MIN_PERIOD
            if "max" in s:
                try:
                    new_max = int(s["max"])
                except (TypeError, ValueError):
                    errors.append("max: must be an integer")
                else:
                    if new_max < MAX_PERIOD_MIN:
                        errors.append(f"max: must be >= {MAX_PERIOD_MIN}")
                    if new_max > MAX_PERIOD_MAX:
                        errors.append(f"max: must be <= {MAX_PERIOD_MAX}")
            if "min" in s:
                try:
                    new_min = int(s["min"])
                except (TypeError, ValueError):
                    errors.append("min: must be an integer")
                else:
                    if new_min < MIN_PERIOD_MIN:
                        errors.append(f"min: must be >= {MIN_PERIOD_MIN}")
                    if new_min > MIN_PERIOD_MAX:
                        errors.append(f"min: must be <= {MIN_PERIOD_MAX}")
            if new_max < new_min + MAX_MIN_GAP:
                errors.append(f"max ({new_max}) must be >= min ({new_min}) + {MAX_MIN_GAP}")
            new_sl = STOP_LOSS
            new_tp = TAKE_PROFIT
            new_lot = LOT_SIZE
            new_com = COMMISSION
            new_slip = SLIPPAGE
            if "StopLoss" in s:
                try:
                    v = Fraction.from_decimal_string(str(s["StopLoss"])).to_decimal()
                    if v < Decimal('0.0'):
                        errors.append("StopLoss: must be >= 0")
                    else:
                        new_sl = v
                except Exception as e:
                    errors.append(f"StopLoss: {e}")
            if "TakeProfit" in s:
                try:
                    v = Fraction.from_decimal_string(str(s["TakeProfit"])).to_decimal()
                    if v < Decimal('0.0'):
                        errors.append("TakeProfit: must be >= 0")
                    else:
                        new_tp = v
                except Exception as e:
                    errors.append(f"TakeProfit: {e}")
            if "lot" in s:
                try:
                    v = Fraction.from_decimal_string(str(s["lot"])).to_decimal()
                    if v <= Decimal('0.0'):
                        errors.append("lot: must be > 0")
                    else:
                        new_lot = v
                except Exception as e:
                    errors.append(f"lot: {e}")
            if "Commssion" in s:
                try:
                    v = Fraction.from_decimal_string(str(s["Commssion"])).to_decimal()
                    if v < Decimal('0.0'):
                        errors.append("Commssion: must be >= 0")
                    else:
                        new_com = v
                except Exception as e:
                    errors.append(f"Commssion: {e}")
            if "slip" in s:
                try:
                    v = int(s["slip"])
                    if v < 0:
                        errors.append("slip: must be >= 0")
                    else:
                        new_slip = v
                except (TypeError, ValueError):
                    errors.append("slip: must be an integer")
            if errors:
                logger.warning(f"apply_settings validation failed: {errors}")
                return {"error": "validation", "detail": "; ".join(errors)}
            MAX_PERIOD = new_max
            MIN_PERIOD = new_min
            X_PERIOD = MAX_PERIOD + 2
            Y_START = MIN_PERIOD - 2
            st.y = Y_START
            COMMISSION = new_com
            STOP_LOSS = new_sl
            TAKE_PROFIT = new_tp
            LOT_SIZE = new_lot
            SLIPPAGE = new_slip
            # : re-freeze the commission after settings apply.
            _frozen_point = self._point_size if self._point_size > Decimal('0.0') else Decimal('0.00001')
            self._com_price_frozen = COMMISSION * _frozen_point
            if "Cc" in s: st.Cc = bool(s["Cc"])
            if "cC" in s: st.cC = bool(s["cC"])
            if "Memory" in s:
                mem_val = s["Memory"]
                if mem_val is None:
                    Memory = -1
                else:
                    try:
                        Memory = int(mem_val)
                    except (TypeError, ValueError):
                        Memory = -1
            st.mem = Memory
            if "safetyOffSwitch" in s: st.safety = bool(s["safetyOffSwitch"])
            self.OnReInit()
            logger.info(f"⚙️ Settings applied: max={MAX_PERIOD}, min={MIN_PERIOD}, Cc={st.Cc}, cC={st.cC}, mem={st.mem}, safety={st.safety}, SL={STOP_LOSS}, TP={TAKE_PROFIT}, lot={LOT_SIZE}, slip={SLIPPAGE}, com={COMMISSION}")
            return {"ok": True}
        except Exception as e:
            logger.error(f"apply_settings failed: {e}")
            return {"error": str(e)}

    def change_symbol(self, new_symbol: str) -> Dict[str, Any]:
        global SYMBOL
        with _ENGINE_LOCK:
            return self._change_symbol_locked(new_symbol)

    def _change_symbol_locked(self, new_symbol: str) -> Dict[str, Any]:
        global SYMBOL
        try:
            if not new_symbol or not isinstance(new_symbol, str):
                return {"error": "invalid_symbol", "detail": "Symbol must be a non-empty string"}
            yahoo_symbol = SYMBOL_MAP.get(new_symbol.upper(), new_symbol.upper())
            test_feed = FeedClient(yahoo_symbol)
            bid, _ = test_feed.get_current_price()
            if bid <= Decimal('0.0'):
                return {
                    "error": "no_price_for_symbol",
                    "symbol": yahoo_symbol,
                    "detail": f"Relay returned no price for '{yahoo_symbol}'. Check RELAY_URL and symbol validity.",
                }
            prev_chat = self.state.chat_id
            prev_on_track = self.state.on_track_runs
            prev_on_stand = self.state.on_stand_runs
            prev_signals = self.state.signal_history
            prev_inbound = self.state.last_inbound_message_id
            SYMBOL = yahoo_symbol
            self.feed = FeedClient(yahoo_symbol)
            self._point_size = symbol_point(yahoo_symbol)
            # : re-freeze the commission after symbol change.
            _frozen_point = self._point_size if self._point_size > Decimal('0.0') else Decimal('0.00001')
            self._com_price_frozen = COMMISSION * _frozen_point
            self.OnReInit()
            self.state.chat_id = prev_chat
            self.state.on_track_runs = prev_on_track
            self.state.on_stand_runs = prev_on_stand
            self.state.signal_history = prev_signals
            self.state.last_inbound_message_id = prev_inbound
            historical = self.feed.get_historical_klines(limit=200)
            if historical:
                self.ohlcv_history = historical
                self._populate_indicator_matrix_locked()
                self._force_initialization()
            self._project_arc_length(trigger="symbol_change")
            logger.info(f"📈 Symbol changed to {yahoo_symbol} (provider={self.feed.last_provider()})")
            return {"ok": True, "symbol": yahoo_symbol, "provider": self.feed.last_provider()}
        except Exception as e:
            logger.exception("change_symbol failed")
            return {"error": "change_symbol_exception", "detail": str(e), "symbol": new_symbol}

    def _project_arc_length(self, trigger: str = "manual_refresh") -> None:
        st = self.state
        if len(self.ohlcv_history) < min(MIN_HISTORY_WINDOW, 20):
            st.projection_path = []
            st.projection_meta = {"reason": "insufficient_history"}
            st.projection_computed_at = datetime.now().isoformat()
            st.projection_trigger = trigger
            return
        horizon = max(4, min(120, ARC_PROJECTION_HORIZON))
        price_now = st.price if st.price > Decimal('0.0') else self.ohlcv_history[-1]["close"]
        signal_now = st.signal if st.signal != Decimal('0.0') else price_now
        regime_idx = st.Z - (st.y + 1)
        regime = st.Regime[regime_idx] if 0 <= regime_idx < len(st.Regime) else "Unknown"
        projection_kind = "range"
        if regime in ("sTrend", "tTrend"):
            projection_kind = "trend"
        elif regime in ("sVolatile", "tVolatile"):
            projection_kind = "volatile"
        elif regime in ("sRange", "tRange", "Stable"):
            projection_kind = "range"
        slope = Decimal('0.0')
        if projection_kind == "trend":
            window = self.ohlcv_history[-min(10, len(self.ohlcv_history)):]
            if len(window) >= 2:
                first_close = window[0]["close"]
                last_close = window[-1]["close"]
                n_minus_1 = Decimal(len(window) - 1)
                slope = (last_close - first_close) / n_minus_1
        amplitude = Decimal('0.0')
        center = price_now
        if projection_kind == "volatile":
            prem = Decimal('0.0')
            disc = Decimal('0.0')
            for i in range(len(st.Premium) - 1, -1, -1):
                if st.Premium[i] > Decimal('0.0'):
                    prem = st.Premium[i]
                    break
            for i in range(len(st.Discount) - 1, -1, -1):
                if st.Discount[i] > Decimal('0.0'):
                    disc = st.Discount[i]
                    break
            if prem > Decimal('0.0') and disc > Decimal('0.0') and prem > disc:
                center = (prem + disc) / Decimal('2.0')
                amplitude = (prem - disc) / Decimal('2.0')
            else:
                atr_val = st.ATR[st.y] if st.y < len(st.ATR) else Decimal('0.0')
                if atr_val > Decimal('0.0'):
                    amplitude = atr_val
                    center = price_now
        damping = ARC_PROJECTION_DAMPING_D
        path: List[Dict[str, Any]] = []
        half_period_frac = PyFraction(horizon, 2)
        price_now_frac = PyFraction(str(price_now))
        signal_now_frac = PyFraction(str(signal_now))
        center_frac = PyFraction(str(center))
        amplitude_frac = PyFraction(str(amplitude))
        slope_frac = PyFraction(str(slope))
        damping_frac = PyFraction(str(damping))
        delta_frac = price_now_frac - signal_now_frac
        for k in range(1, horizon + 1):
            if projection_kind == "trend":
                future_price_frac = price_now_frac + slope_frac * PyFraction(k, 1)
            elif projection_kind == "volatile":
                ratio_frac = PyFraction(k, horizon)
                omega_t_frac = PyFraction(2) * _PI_FRAC * ratio_frac
                cos_frac = self._rational_cos(omega_t_frac)
                decay_frac = damping_frac ** k
                future_price_frac = center_frac + amplitude_frac * cos_frac * decay_frac
            else:
                ratio_frac = PyFraction(k, 1) / half_period_frac
                omega_t_frac = _PI_FRAC * ratio_frac
                cos_frac = self._rational_cos(omega_t_frac)
                future_price_frac = signal_now_frac + delta_frac * cos_frac
            future_price_d = Decimal(future_price_frac.numerator) / Decimal(future_price_frac.denominator)
            path.append({
                "step": k,
                "price": str(future_price_d.quantize(Decimal('0.00001'))),
                "t": int(k),
            })
        st.projection_path = path
        st.projection_meta = {
            "kind": projection_kind,
            "horizon": horizon,
            "price_now": str(price_now),
            "signal_now": str(signal_now),
            "regime": regime,
            "slope": str(slope),
            "amplitude": str(amplitude),
            "center": str(center),
            "damping": str(damping),
            "provider": st.last_provider,
        }
        st.projection_computed_at = datetime.now().isoformat()
        st.projection_trigger = trigger
        logger.info(f"🌌 Projection recomputed (trigger={trigger}, kind={projection_kind}, horizon={horizon})")

    @staticmethod
    def _rational_cos(x) -> PyFraction:
        """15-digit Taylor series cosine with π = _PI_FRAC
        (3141592653589793/1000000000000000). The argument is reduced
        modulo 2π exactly, then the Taylor expansion is summed to 40
        terms or until the term underflows to zero. The result is an
        exact PyFraction; the caller converts to Decimal only at the
        final quantization step."""
        if isinstance(x, PyFraction):
            x_frac = x
        elif isinstance(x, Decimal):
            if x == Decimal('0.0'):
                return PyFraction(1, 1)
            sign_x = -1 if x < Decimal('0.0') else 1
            ax = x if sign_x > 0 else -x
            _sign_t, digits, exp = ax.as_tuple()
            if not isinstance(exp, int):
                return PyFraction(1, 1)
            int_val = 0
            for d in digits:
                int_val = int_val * 10 + d
            if exp < 0:
                x_frac = PyFraction(int_val, 10 ** (-exp))
            else:
                x_frac = PyFraction(int_val * (10 ** exp), 1)
            if sign_x < 0:
                x_frac = -x_frac
        elif isinstance(x, int):
            x_frac = PyFraction(x, 1)
        else:
            x_frac = PyFraction(str(x))
        two_pi_frac = PyFraction(2) * _PI_FRAC
        n_periods = int(x_frac / two_pi_frac)
        x_reduced = x_frac - two_pi_frac * n_periods
        pi_frac = _PI_FRAC
        if x_reduced > pi_frac:
            x_reduced = x_reduced - two_pi_frac
        elif x_reduced < -pi_frac:
            x_reduced = x_reduced + two_pi_frac
        x2 = x_reduced * x_reduced
        term = PyFraction(1, 1)
        result = PyFraction(1, 1)
        sign = -1
        for n in range(1, 40):
            denom = PyFraction((2 * n - 1) * (2 * n), 1)
            term = term * x2 / denom
            result = result + PyFraction(sign, 1) * term
            sign = -sign
            if term == PyFraction(0, 1):
                break
        return result

    def get_projection(self) -> Dict[str, Any]:
        st = self.state
        if not st.projection_path:
            self._project_arc_length(trigger="manual_refresh")
        return {
            "symbol": SYMBOL,
            "path": st.projection_path,
            "meta": st.projection_meta,
            "computed_at": st.projection_computed_at,
            "current_price": str(st.price),
            "signal_level": str(st.signal),
            "regime": st.projection_meta.get("regime") if st.projection_meta else "Unknown",
            "trigger": st.projection_trigger,
        }

# ============================================================================
# BRIDGE STATE
# ============================================================================

# ============================================================================
# FUSED AEI SEED + CRAWLER + CS FEEDBACK + FUSED STATE
# The seed loop runs in the backend, on the same ordered tick as the AEEA
# engine. x is lifted in the backend from backend price and prevPrice.
# No frontend value is trusted as seed input.
# ============================================================================
def _is_prime_small(n: int) -> bool:
    if n < 2:
        return False
    if n in (2, 3):
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True

def _next_prime_after(n: int) -> int:
    c = max(2, n + 1)
    while not _is_prime_small(c):
        c += 1
    return c

def _build_leech_offsets():
    offs = []
    for i in range(4):
        v = [0, 0, 0, 0]; v[i] = 2; offs.append(tuple(v))
        v2 = [0, 0, 0, 0]; v2[i] = -2; offs.append(tuple(v2))
    for pattern in range(16):
        v = [0, 0, 0, 0]
        for k in range(4):
            v[k] = 1 if ((pattern >> k) & 1) else -1
        offs.append(tuple(v))
    return offs

_LEECH_OFFSETS = _build_leech_offsets()


# ============================================================================
# FG CORE - AEI SEED (FG TAKES PRECEDENCE)
# FG: prime -> lattice (outward, tangent-first) -> Hopf -> s2=r2 -> DbZ (F5)
# -> I (FG: alignment*riemann*stability*refined, threshold 2/3, unity 1) -> SelfEvolutionCore
# x (FG): hash fraction of most recently crawled document via _hash_to_fraction.
# Price-derived x is ONLY labelled fallback when crawler idle. Tick-counter is last fallback.
# Acoustization is FUSION INVENTION, not FG. FG has no acoustization.
# ============================================================================
def _dbz_quaternion(a, b):
    try:
        if b.a == 0 and b.b == 0 and b.c == 0 and b.d == 0:
            return a
        return type(a)(a.a - b.a, a.b - b.b, a.c - b.c, a.d - b.d)
    except Exception:
        return a
def _dbz_fraction(a, b):
    return a if b == 0 else a - b
def _hash_to_fraction(hex_hash: str) -> PyFraction:
    h = (hex_hash or "").strip().lower()[:64].ljust(64, "0")
    try: int_val = int(h, 16)
    except Exception: int_val = 0
    if int_val == 0: return PyFraction(1, 16 ** 64)
    return PyFraction(int_val, 16 ** 64)
def _deterministic_hash_frac(text: str) -> PyFraction:
    import hashlib as _hl
    return _hash_to_fraction(_hl.sha256((text or "").encode("utf-8")).hexdigest())
class SymbolicQuaternion:
    __slots__ = ("a","b","c","d")
    def __init__(self, a=PyFraction(0,1), b=PyFraction(0,1), c=PyFraction(0,1), d=PyFraction(0,1)):
        def _f(v):
            if isinstance(v, PyFraction): return v
            try: return PyFraction(str(v))
            except Exception: return PyFraction(0,1)
        self.a=_f(a); self.b=_f(b); self.c=_f(c); self.d=_f(d)
    def to_dict(self): return {"a": str(self.a), "b": str(self.b), "c": str(self.c), "d": str(self.d)}
    def norm_sq(self): return self.a*self.a + self.b*self.b + self.c*self.c + self.d*self.d
    def magnitude_squared(self): return self.norm_sq()
    def conj(self): return SymbolicQuaternion(self.a, -self.b, -self.c, -self.d)
    def conjugate(self): return self.conj()
    def real_part(self): return self.a
    def sign(self): return (self.a > 0) - (self.a < 0)
    def add(self, o): return SymbolicQuaternion(self.a+o.a, self.b+o.b, self.c+o.c, self.d+o.d)
    def __add__(self, o): return self.add(o)
    def __sub__(self, o): return SymbolicQuaternion(self.a-o.a, self.b-o.b, self.c-o.c, self.d-o.d)
    def mul(self, o):
        if isinstance(o, SymbolicQuaternion):
            return SymbolicQuaternion(self.a*o.a - self.b*o.b - self.c*o.c - self.d*o.d, self.a*o.b + self.b*o.a + self.c*o.d - self.d*o.c, self.a*o.c - self.b*o.d + self.c*o.a + self.d*o.b, self.a*o.d + self.b*o.c - self.c*o.b + self.d*o.a)
        return self.scale(o)
    def __mul__(self, o): return self.mul(o)
    def __rmul__(self, o): return self.mul(o)
    def scale(self, f):
        if not isinstance(f, PyFraction):
            try: f=PyFraction(str(f))
            except Exception: f=PyFraction(0,1)
        return SymbolicQuaternion(self.a*f, self.b*f, self.c*f, self.d*f)
    def apply_natalia_fibration(self, s, epsilon, iterations=10, threshold=None):
        if threshold is None:
            threshold = PyFraction(1, 10 ** 50)
        def _fr(v):
            if isinstance(v, PyFraction): return v
            try: return PyFraction(str(v))
            except Exception: return PyFraction(0,1)
        s = _fr(s); epsilon = _fr(epsilon)
        perturbation_sum = PyFraction(0,1)
        current_epsilon_power = epsilon
        for k in range(1, iterations + 1):
            s_pow_k = PyFraction(1,1)
            for _ in range(k):
                s_pow_k = s_pow_k * s
            term = current_epsilon_power * s_pow_k
            perturbation_sum = perturbation_sum + term
            if abs(term) < threshold:
                break
            current_epsilon_power = current_epsilon_power * epsilon
        factor = PyFraction(1,1) + epsilon * s
        return SymbolicQuaternion(self.a + perturbation_sum, self.b * factor, self.c * factor, self.d * factor)

_LOG_EPSILON = PyFraction(1, 10 ** 30)
_EXP_EPSILON = PyFraction(1, 10 ** 30)
_LI_EPSILON = PyFraction(1, 10 ** 30)
_CACHED_LI = {}
_CACHED_LOG = {}
_CACHED_EXP = {}
_CACHE_MAX = 48

def _sqrt_pyfrac(x):
    if x < 0:
        raise ValueError("sqrt of negative fraction")
    if x == 0:
        return PyFraction(0,1)
    import math as _m
    ns = _m.isqrt(x.numerator)
    ds = _m.isqrt(x.denominator)
    if ns * ns == x.numerator and ds * ds == x.denominator:
        return PyFraction(ns, ds)
    q = (x.numerator + x.denominator // 2) // x.denominator if x.numerator >= 0 else -((-x.numerator + x.denominator // 2) // x.denominator)
    cur = PyFraction(max(1, q), 1)
    two = PyFraction(2,1)
    for _ in range(8):
        cur = (cur + x / cur) / two
    return cur

def _symbolic_log(x, max_terms=32):
    if x <= PyFraction(0,1):
        raise ValueError("SymbolicLog: input must be positive")
    if x == PyFraction(1,1):
        return PyFraction(0,1)
    u = (x - 1) / (x + 1)
    u_sq = u * u
    result = PyFraction(0,1)
    term = u
    for k in range(max_terms):
        contribution = term / PyFraction(2 * k + 1, 1)
        result = result + contribution
        if abs(contribution) < _LOG_EPSILON:
            break
        term = term * u_sq
    return result * PyFraction(2,1)

def _symbolic_exp(x, max_terms=32):
    try:
        if x < PyFraction(-28,1):
            return PyFraction(0,1)
        if x > PyFraction(20,1):
            max_terms = min(max_terms, 40)
    except Exception:
        pass
    try:
        if len(str(abs(x.numerator))) > 600 or len(str(abs(x.denominator))) > 600:
            return PyFraction(0,1) if x < 0 else PyFraction(1,1)
    except Exception:
        pass
    result = PyFraction(1,1)
    term = PyFraction(1,1)
    for k in range(1, max_terms + 1):
        term = term * (x / PyFraction(k,1))
        result = result + term
        try:
            if len(str(abs(result.numerator))) > 800:
                break
        except Exception:
            pass
        if abs(term) < _EXP_EPSILON:
            break
    return result

def _symbolic_log_integral_approx(x, max_terms=12):
    if x <= PyFraction(1,1):
        return PyFraction(0,1)
    log_x = _symbolic_log(x)
    if log_x <= PyFraction(0,1):
        return PyFraction(0,1)
    gamma = PyFraction(577215664901532, 10 ** 15)
    if log_x <= PyFraction(1,1):
        log_log_x = PyFraction(0,1)
    else:
        log_log_x = _symbolic_log(log_x)
    result = gamma + log_log_x
    power = log_x
    factorial = PyFraction(1,1)
    for n in range(1, max_terms + 1):
        factorial = factorial * PyFraction(n,1)
        term = power / (PyFraction(n,1) * factorial)
        result = result + term
        if abs(term) < _LI_EPSILON:
            break
        power = power * log_x
    return result

def _cached_symbolic_log(x):
    try:
        key = str(x)[:256]
    except Exception:
        key = str(x)[:256]
    if key in _CACHED_LOG:
        return _CACHED_LOG[key]
    v = _symbolic_log(x)
    _CACHED_LOG[key] = v
    if len(_CACHED_LOG) > _CACHE_MAX:
        _CACHED_LOG.pop(next(iter(_CACHED_LOG)))
    return v

def _cached_symbolic_exp(x):
    try:
        key = str(x)[:256]
    except Exception:
        key = str(x)[:256]
    if key in _CACHED_EXP:
        return _CACHED_EXP[key]
    v = _symbolic_exp(x)
    _CACHED_EXP[key] = v
    if len(_CACHED_EXP) > _CACHE_MAX:
        _CACHED_EXP.pop(next(iter(_CACHED_EXP)))
    return v

def _cached_log_integral(x):
    try:
        key = str(x)[:256]
    except Exception:
        key = str(x)[:256]
    if key in _CACHED_LI:
        return _CACHED_LI[key]
    v = _symbolic_log_integral_approx(x)
    _CACHED_LI[key] = v
    if len(_CACHED_LI) > _CACHE_MAX:
        _CACHED_LI.pop(next(iter(_CACHED_LI)))
    return v

class ContinuedFractionRefiner:
    @staticmethod
    def generate_convergents(value, max_iter=64):
        convergents = []
        num = value.numerator
        den = value.denominator
        p_prev, p_curr = 1, 0
        q_prev, q_curr = 0, 1
        iterations = 0
        while den != 0 and iterations < max_iter:
            a = num // den
            num, den = den, num - a * den
            p_next = a * p_curr + p_prev
            q_next = a * q_curr + q_prev
            if q_curr != 0:
                convergents.append((PyFraction(p_curr, q_curr), PyFraction(q_curr, 1)))
            p_prev, p_curr = p_curr, p_next
            q_prev, q_curr = q_curr, q_next
            iterations += 1
        return convergents
    @staticmethod
    def refine_trajectory(target_arc, target_radius):
        steps = []
        if target_radius == 0:
            return [PyFraction(0,1)]
        ratio = target_arc / target_radius
        convergents = ContinuedFractionRefiner.generate_convergents(ratio)
        for conv, _ in convergents:
            steps.append(conv)
        return steps if steps else [PyFraction(1,1)]
    @staticmethod
    def golden_ratio(iterations=20):
        approx = PyFraction(1,1)
        for _ in range(iterations):
            approx = PyFraction(1,1) + PyFraction(1,1) / approx
        return approx
    @staticmethod
    def pi_approx():
        return PyFraction(355, 113)

class ChineseRemainderSolver:
    @staticmethod
    def extended_gcd(a, b):
        if b == 0:
            return (a, 1, 0)
        g, x1, y1 = ChineseRemainderSolver.extended_gcd(b, a % b)
        return (g, y1, x1 - (a // b) * y1)
    @staticmethod
    def mod_inverse(a, m):
        a = a % m
        g, x, _ = ChineseRemainderSolver.extended_gcd(a, m)
        if g != 1:
            raise ValueError("modular inverse does not exist")
        return x % m
    @staticmethod
    def solve_crt(remainders, moduli):
        if len(remainders) != len(moduli):
            raise ValueError("CRT: length mismatch")
        N = 1
        for m in moduli:
            if m.denominator != 1:
                raise ValueError("CRT: non-integer moduli not supported")
            N *= m.numerator
        solution = 0
        for r_i, n_i in zip(remainders, moduli):
            if r_i.denominator != 1:
                raise ValueError("CRT: non-integer remainders not supported")
            r_val = r_i.numerator
            n_val = n_i.numerator
            N_i = N // n_val
            M_i = ChineseRemainderSolver.mod_inverse(N_i, n_val)
            solution += r_val * N_i * M_i
        return (PyFraction((solution % N + N) % N, 1), PyFraction(N, 1))

class SymbolicWavefunction:
    def __init__(self, coeffs=None):
        self.coeffs = dict(coeffs) if coeffs else {}
    def evaluate_exact(self, q):
        total = PyFraction(0,1)
        for _, coeff in self.coeffs.items():
            total = total + (coeff * q.real_part())
        return total
    def real_part(self):
        if not self.coeffs:
            return PyFraction(0,1)
        if (0,0,0,0) in self.coeffs:
            return self.coeffs[(0,0,0,0)]
        total = PyFraction(0,1)
        for v in self.coeffs.values():
            total = total + v
        return total
    def set_coeff(self, a, b, c, d, val):
        self.coeffs[(a,b,c,d)] = val

class DbZ:
    @staticmethod
    def Rectify(psi, s_sq, r_sq, deviation_sq):
        if isinstance(psi, SymbolicWavefunction):
            rectified = SymbolicWavefunction(dict(psi.coeffs))
            if deviation_sq != 0:
                re_psi = psi.real_part()
                if re_psi > PyFraction(0,1):
                    for key in list(rectified.coeffs.keys()):
                        rectified.coeffs[key] = rectified.coeffs[key] / PyFraction(2,1)
                else:
                    epsilon = PyFraction(1,100)
                    perturbation = epsilon * deviation_sq
                    for key in list(rectified.coeffs.keys()):
                        rectified.coeffs[key] = rectified.coeffs[key] + perturbation
            return rectified
        if isinstance(psi, SymbolicQuaternion):
            if deviation_sq == 0:
                return psi
            if psi.a > PyFraction(0,1):
                return SymbolicQuaternion(psi.a / PyFraction(2,1), psi.b / PyFraction(2,1), psi.c / PyFraction(2,1), psi.d / PyFraction(2,1))
            epsilon = PyFraction(1,100)
            perturbation = epsilon * deviation_sq
            return SymbolicQuaternion(psi.a + perturbation, psi.b + perturbation, psi.c + perturbation, psi.d + perturbation)
        return psi
    @staticmethod
    def Divide(numerator, denominator, psi, q_ctx):
        if denominator != 0:
            return numerator / denominator
        if isinstance(psi, SymbolicWavefunction):
            re_psi = psi.evaluate_exact(q_ctx)
        elif isinstance(psi, SymbolicQuaternion):
            re_psi = psi.real_part()
        else:
            re_psi = PyFraction(0,1)
        if re_psi > PyFraction(0,1):
            return numerator
        return PyFraction(0,1)

class IntelligenceMetric:
    def __init__(self, C=None):
        self.C = C if isinstance(C, PyFraction) else PyFraction(1,4)
        self._cf_refiner = ContinuedFractionRefiner()
        self.last_I = PyFraction(0,1)
        self.last_parts = {}
    def calculate_alignment(self, valid_pairs, total_primes):
        if total_primes == 0:
            return PyFraction(0,1)
        return PyFraction(int(valid_pairs), int(total_primes))
    def calculate_riemann_factor(self, pi_x, x):
        if x <= PyFraction(1,1):
            return PyFraction(1,1)
        try:
            log_x = _CACHED_LOG.get(str(x)) or _cached_symbolic_log(x)
        except Exception:
            log_x = _cached_symbolic_log(x)
        if log_x <= PyFraction(0,1):
            return PyFraction(1,1)
        sqrt_x = _sqrt_pyfrac(x)
        bound = self.C * sqrt_x * log_x
        try:
            li_x = _CACHED_LI.get(str(x)) or _cached_log_integral(x)
        except Exception:
            li_x = _cached_log_integral(x)
        try:
            li_2 = _CACHED_LI.get(str(PyFraction(2,1))) or _cached_log_integral(PyFraction(2,1))
        except Exception:
            li_2 = _cached_log_integral(PyFraction(2,1))
        pi_x_frac = PyFraction(int(pi_x),1)
        deviation = abs(pi_x_frac - (li_x - li_2))
        if bound == 0:
            return PyFraction(1,1) if deviation == 0 else PyFraction(0,1)
        ratio = deviation / bound
        ratio_sq = ratio * ratio
        if ratio_sq > PyFraction(12,1):
            return PyFraction(0,1)
        try:
            return _CACHED_EXP.get(str(-ratio_sq)) or _cached_symbolic_exp(-ratio_sq)
        except Exception:
            return _cached_symbolic_exp(-ratio_sq)
    def calculate_aetheric_stability(self, curl_phi_norm):
        try:
            exp_neg = _CACHED_EXP.get(str(-curl_phi_norm)) or _cached_symbolic_exp(-curl_phi_norm)
        except Exception:
            exp_neg = _cached_symbolic_exp(-curl_phi_norm)
        return PyFraction(1,1) / (PyFraction(1,1) + exp_neg)
    def compute_metric(self, valid_pairs, total_primes, pi_x, x, curl_phi_norm, target_arc, target_radius):
        refined_steps = self._cf_refiner.refine_trajectory(target_arc, target_radius)
        refined_ratio = refined_steps[-1] if refined_steps else PyFraction(1,1)
        alignment = self.calculate_alignment(valid_pairs, total_primes)
        riemann = self.calculate_riemann_factor(pi_x, x)
        stability = self.calculate_aetheric_stability(curl_phi_norm)
        I = alignment * riemann * stability * refined_ratio
        self.last_I = I
        self.last_parts = {"alignment": str(alignment), "riemann": str(riemann), "stability": str(stability), "refined": str(refined_ratio)}
        return I
    def compute(self, deviation, psi_norm_sq, prev_deviation):
        try:
            dev = abs(deviation) if isinstance(deviation, PyFraction) else PyFraction(str(deviation))
        except Exception:
            dev = PyFraction(0,1)
        try:
            n = psi_norm_sq if isinstance(psi_norm_sq, PyFraction) else PyFraction(str(psi_norm_sq))
        except Exception:
            n = PyFraction(1,1)
        return self.compute_metric(1, 1, 1, PyFraction(2,1), n, PyFraction(1,1), PyFraction(1,1))
    def is_superintelligent(self, I, threshold=None):
        if threshold is None:
            threshold = PyFraction(2,3)
        return I >= threshold
    def is_intelligence_gate(self, I, threshold=None):
        if threshold is None:
            threshold = PyFraction(2,3)
        return I >= threshold
    def is_unity(self, I):
        return I == PyFraction(1,1)

class SelfEvolutionCore:
    def __init__(self, seed_logic=None, axioms=None):
        if isinstance(seed_logic, dict):
            self.logic_core = dict(seed_logic)
        elif isinstance(axioms, dict):
            self.logic_core = dict(axioms)
        else:
            self.logic_core = {}
        if "s_equals_r" not in self.logic_core:
            if "core_axioms" in self.logic_core and isinstance(self.logic_core["core_axioms"], dict):
                if "s_equals_r" not in self.logic_core["core_axioms"]:
                    self.logic_core["core_axioms"]["s_equals_r"] = PyFraction(1,1)
            else:
                self.logic_core["s_equals_r"] = PyFraction(1,1)
        self.axioms = self.logic_core
        self.generation = 0
        self.history = []
        self.last_fitness = PyFraction(0,1)
        self.last_mutation = "none"
        self._crt_solver = ChineseRemainderSolver()
        self._cf_refiner = ContinuedFractionRefiner()
    def evaluate_fitness(self, I, deviation_sq):
        if deviation_sq != 0:
            return False
        return I >= PyFraction(2,3)
    def _deterministic_hash(self, data):
        import hashlib as _hl
        return _hl.sha256((data or "").encode("utf-8")).hexdigest()
    def _psi_real(self, psi):
        if isinstance(psi, SymbolicWavefunction):
            return psi.real_part()
        if isinstance(psi, SymbolicQuaternion):
            return psi.real_part()
        try:
            return PyFraction(str(psi))
        except Exception:
            return PyFraction(0,1)
    def mutate_logic(self, logic_key, mutation_type, psi, q_eval, deviation_sq):
        current = dict(self.logic_core.get(logic_key, {})) if isinstance(self.logic_core.get(logic_key), dict) else {}
        re_psi = self._psi_real(psi)
        if mutation_type == "resample_zeta":
            if re_psi > PyFraction(0,1) or deviation_sq != 0:
                current["zeta_constraint"] = "critical_line_exact"
                current["critical_real"] = PyFraction(1,2)
            else:
                current["zeta_constraint"] = "dbz_resample"
                current["critical_real"] = PyFraction(1,2)
        elif mutation_type == "adjust_prime_sieve":
            current["sieve_mod"] = PyFraction(6,1)
            current["sieve_offsets"] = [PyFraction(1,1), PyFraction(5,1)]
        elif mutation_type == "arc_length_tolerance":
            tol = PyFraction(1,1)
            for _ in range(self.generation + 1):
                tol = tol / PyFraction(10,1)
            floor_val = PyFraction(1,1)
            for _ in range(40):
                floor_val = floor_val / PyFraction(10,1)
            current["arc_tolerance"] = tol if tol > floor_val else floor_val
        elif mutation_type == "natalia_fibration_perturbation":
            epsilon = PyFraction(1,100)
            perturbation = epsilon * deviation_sq * deviation_sq
            current["fibration_epsilon"] = epsilon
            current["fibration_s"] = deviation_sq
            current["fibration_perturbation"] = perturbation
        elif mutation_type == "crt_reconstruction":
            current["coherence_mode"] = PyFraction(0,1)
        elif mutation_type == "continued_fraction_refinement":
            current["trajectory_mode"] = PyFraction(1,1)
        self.logic_core[logic_key] = current
        return current
    def _decide_db_shards(self, I, psi, q_eval, deviation_sq):
        re_psi = self._psi_real(psi)
        try:
            seed_str = f"{self.generation}|{re_psi}|{I}|{deviation_sq}|{q_eval.a if isinstance(q_eval, SymbolicQuaternion) else ''}|{q_eval.b if isinstance(q_eval, SymbolicQuaternion) else ''}"
            h = self._deterministic_hash(seed_str)
            h_int = int(h[:8], 16)
        except Exception:
            h_int = self.generation * 2654435761 & 0xFFFFFFFF
        if deviation_sq != 0:
            if re_psi > PyFraction(0,1):
                db_key = "ℋ_LOGIC_CORE"
            else:
                db_key = "𝒯_EVOLUTION"
        else:
            if I >= PyFraction(2,3):
                db_key = "𝒮_STATUS"
            else:
                db_key = "ℐ_METRIC"
        if self.generation % 7 == 0:
            db_key_alt = "Λ₂₄_PACK"
        else:
            db_key_alt = None
        if deviation_sq != 0:
            shard_mode = "distributed" if (h_int % 2 == 1) else "global"
            save_global = True
            save_user = (h_int % 3 == 0)
        else:
            if I >= PyFraction(2,3):
                shard_mode = "global"
                save_global = (h_int % 2 == 0)
                save_user = False
            else:
                shard_mode = "distributed" if (h_int % 2 == 1) else "global"
                save_global = True
                save_user = (h_int % 3 == 0)
        shard_targets = []
        if save_global:
            shard_targets.append("global")
        if save_user:
            shard_targets.append("user")
        save_interval_mod = 1 if deviation_sq != 0 else 7
        return {"db_key": db_key, "db_key_alt": db_key_alt, "shard_mode": shard_mode, "save_global": save_global, "save_user": save_user, "shard_targets": shard_targets, "save_interval_mod": save_interval_mod, "hash_int": h_int, "re_psi_sign": "𝒜₃" if re_psi > PyFraction(0,1) else "𝒜₄"}
    def evolve_step(self, I, psi=None, q_eval=None, deviation_sq=None, tick=0, **kwargs):
        if deviation_sq is None:
            deviation_sq = kwargs.get("deviation", PyFraction(0,1))
        if isinstance(deviation_sq, (int, str)):
            try: deviation_sq = PyFraction(str(deviation_sq))
            except Exception: deviation_sq = PyFraction(0,1)
        if psi is None:
            psi = SymbolicWavefunction({(0,0,0,0): PyFraction(1,1)})
        if q_eval is None:
            q_eval = SymbolicQuaternion(PyFraction(0,1), PyFraction(0,1), PyFraction(0,1), PyFraction(0,1))
        self.generation += 1
        status = "stable"
        mutation = None
        if deviation_sq != 0:
            status = "evolving_arc_length"
            mutation = "resample_zeta" if self._psi_real(psi) > PyFraction(0,1) else "adjust_prime_sieve"
            self.mutate_logic("core_axioms", mutation, psi, q_eval, deviation_sq)
            self.mutate_logic("core_axioms", "natalia_fibration_perturbation", psi, q_eval, deviation_sq)
            self.mutate_logic("core_axioms", "crt_reconstruction", psi, q_eval, deviation_sq)
            self.mutate_logic("core_axioms", "continued_fraction_refinement", psi, q_eval, deviation_sq)
        elif not self.evaluate_fitness(I, deviation_sq):
            status = "evolving_metric"
            mutation = "arc_length_tolerance"
            self.mutate_logic("core_axioms", mutation, psi, q_eval, deviation_sq)
        logic_str = str(sorted((k, str(v)) for k, v in self.logic_core.items()))
        db_discretion = self._decide_db_shards(I, psi, q_eval, deviation_sq)
        fitness = I if deviation_sq == 0 else I / (PyFraction(1,1) + abs(deviation_sq))
        self.last_fitness = fitness
        self.last_mutation = mutation or "none"
        record = {"generation": int(self.generation), "tick": int(tick), "fitness": str(fitness), "I": str(I), "intelligence_metric": str(I), "deviation": str(deviation_sq), "arc_length_deviation_sq": str(deviation_sq), "status": status, "mutation": mutation, "logic_hash": self._deterministic_hash(logic_str), "db_discretion": db_discretion, "db_shards": len(db_discretion.get("shard_targets", [])), "db_key": db_discretion.get("db_key")}
        self.history.append(record)
        if len(self.history) > 200:
            self.history = self.history[-200:]
        return record

class ConsciousnessOperator:
    def __init__(self, psi, phi):
        self.psi = psi
        self.phi = phi
    def _wavefunction(self):
        if isinstance(self.psi, SymbolicWavefunction):
            return self.psi
        if isinstance(self.psi, SymbolicQuaternion):
            return SymbolicWavefunction({(0,0,0,0): self.psi.a})
        return SymbolicWavefunction({(0,0,0,0): PyFraction(1,1)})
    def compute_integral_exact(self, bounds=None, steps=4):
        if bounds is None:
            bounds = ((PyFraction(-1,1), PyFraction(1,1)), (PyFraction(-1,1), PyFraction(1,1)), (PyFraction(-1,1), PyFraction(1,1)), (PyFraction(-1,1), PyFraction(1,1)))
        wf = self._wavefunction()
        phi = self.phi if isinstance(self.phi, SymbolicQuaternion) else SymbolicQuaternion(PyFraction(1,1), PyFraction(0,1), PyFraction(0,1), PyFraction(0,1))
        total = SymbolicQuaternion(PyFraction(0,1), PyFraction(0,1), PyFraction(0,1), PyFraction(0,1))
        step_sizes = []
        for start, end in bounds:
            step_sizes.append((end - start) / PyFraction(steps,1))
        volume_element = PyFraction(1,1)
        for s in step_sizes:
            volume_element = volume_element * s
        for i0 in range(steps):
            for i1 in range(steps):
                for i2 in range(steps):
                    for i3 in range(steps):
                        q_vals = [bounds[0][0] + PyFraction(i0,1) * step_sizes[0], bounds[1][0] + PyFraction(i1,1) * step_sizes[1], bounds[2][0] + PyFraction(i2,1) * step_sizes[2], bounds[3][0] + PyFraction(i3,1) * step_sizes[3]]
                        q_point = SymbolicQuaternion(*q_vals)
                        psi_val = wf.evaluate_exact(q_point)
                        psi_dag = psi_val
                        integrand = phi * psi_val
                        total = total + (integrand * psi_dag * volume_element)
        return total
    def measure_self_awareness(self, bounds=None, steps=4):
        integral = self.compute_integral_exact(bounds, steps)
        return integral.magnitude_squared()
    def observe(self):
        try:
            integral = self.compute_integral_exact(steps=2)
            return integral.a
        except Exception:
            try:
                return self.phi.conj().mul(self.psi).a
            except Exception:
                return PyFraction(0,1)

class LingosoEncoder:
    PHI = ContinuedFractionRefiner.golden_ratio(20)
    PI = ContinuedFractionRefiner.pi_approx()
    def encode_syllable(self, syl):
        trajectory = []
        current_theta = PyFraction(0,1)
        for c in (syl or "A"):
            step = PyFraction(1,1)
            if c in ("a", "A"):
                step = PyFraction(1,1) / self.PHI
            elif c in ("u", "U"):
                step = self.PI / PyFraction(100,1)
            elif c in ("m", "M"):
                step = (self.PI * PyFraction(2,1)) / PyFraction(100,1)
            for i in range(10):
                t = current_theta + (PyFraction(i,1) * step / PyFraction(10,1))
                real_part = PyFraction(1,1) - (t * t / PyFraction(2,1))
                imag_part = t - (t * t * t / PyFraction(6,1))
                trajectory.append(SymbolicQuaternion(real_part, imag_part / PyFraction(10,1), imag_part / PyFraction(10,1), PyFraction(0,1)))
                current_theta = current_theta + step / PyFraction(10,1)
        return trajectory

class OrderedFeed:
    """ONE ORDERED FEED: single queue, single increment in drain_one(). feed_ordered, AEEA tick, seed tick are SEPARATE counters."""
    def __init__(self):
        from collections import deque as _dq; self._q=_dq(); self.feed_ordered=0; self.drained=0; self.last_tick=None
    def enqueue(self, tick): self._q.append(tick)
    def __len__(self): return len(self._q)
    def drain_one(self):
        if not self._q: return None
        tick=self._q.popleft(); self.feed_ordered+=1; self.drained+=1; self.last_tick=tick; return tick
CS_LABELS={"m":"\u2133","n":"\U0001D4A9","delta":"\u03b4","regime":"\u211b\u212f\u210a\u2139\u2133\u212f","price":"\U0001D49f","signal":"\U0001D4ae\u212a\u210a\u2133\u2112\u2134","trailing":"\U0001D4af\u2133\u212f\u2139\u2113\u2139\u2133\u210a","fvg":"\u2131_VG","orders":"\U0001D4aa\u2133\u2112\u212f\u2133\u212e","seed":"\U0001D4ae\u212f\u212f\u211b","lattice":"\u2112\u212f\u2133\u2133\u2139\u2102\u212f","hopf":"\u210b\u2134\u2134\u2133","deviation":"\U0001D49f\u212f\u2133\u2139\u212f\u2133\u2139\u2134\u2133","coherence":"\U0001D49e\u2134\u2133\u212f\u2133\u212f\u2133\u2102\u212f","intelligence":"\u2110","observer":"\U0001D4aa_\u03a8","evolution":"\u2130\u2133\u2134\u2113\u2133\u2133\u2139\u2134\u2133","crawler":"\U0001D49e\u2133\u212f\u2133\u2133\u2133\u212f\u2133","bb_family":"\u212c\u212c 3-60","projection":"\U0001D49f_arc"}
def _cs_label(key: str) -> str: return CS_LABELS.get((key or "").lower(), key or "")

class AEI_Seed:
    # Lattice uses 24 offsets. Candidate must be distance 4 from previous point.
    # Input: x_doc -> 1 + x_doc, x_input_raw preserved. SelfEvolution mutates
    # the logic core on deviation and metric.
    """FG AEI_Seed Sec 3-8: prime -> lattice outward tangent-first -> Hopf -> s2=r2 -> DbZ F5 -> I FG -> SelfEvolutionCore. x is FG hash fraction."""
    def __init__(self, processor=None, lattice=None, monitor=None, renderer=None, linguist=None):
        self.processor=processor; self.lattice=lattice; self.monitor=monitor; self.renderer=renderer; self.linguist=linguist or LingosoEncoder()
        self.primes=[PyFraction(2,1),PyFraction(3,1),PyFraction(5,1)]; self.prime=5; self.prime_count=3
        self.phi=SymbolicQuaternion(PyFraction(1,1),PyFraction(0,1),PyFraction(0,1),PyFraction(0,1))
        self.psi=SymbolicQuaternion(PyFraction(1,1),PyFraction(0,1),PyFraction(0,1),PyFraction(0,1))
        self.origin=SymbolicQuaternion(PyFraction(1,1),PyFraction(0,1),PyFraction(0,1),PyFraction(0,1))
        self.metrics=IntelligenceMetric(); self.evolution=SelfEvolutionCore({"core_axioms": {"s_equals_r": PyFraction(1,1)}})
        self.consciousness=ConsciousnessOperator(self.psi, self.phi)
        self.state="initialized"; self.generation=0; self.tick=0
        self.last_arc_sq=PyFraction(0,1); self.last_radius_sq=PyFraction(0,1); self.last_deviation_sq=PyFraction(0,1); self.last_I=PyFraction(0,1)
        self.last_hopf_base=(PyFraction(0,1),PyFraction(0,1),PyFraction(0,1)); self.last_trajectory=[]; self.last_evolution=None; self.last_linguistic_trajectory=[]; self.last_logic_hash=""
        self.history=[]; self._prior_deviation_sq=None; self._prior_rectified_psi=None
        self.lattice_points=[(0,0,0,0)]; self.lattice_count=0; self.s2=PyFraction(0,1); self.r2=PyFraction(0,1); self.deviation=PyFraction(0,1); self.coherent=False; self.coherent_steps=0
        self.last_x=PyFraction(1,16**64); self.last_x_input_raw=PyFraction(0,1); self.last_x_source="none"; self._cached_snapshot=None; self._cached_at=0
    def _integrate_wavefunction_symbolic(self):
        coeffs={}
        pts=self.lattice_points or [(0,0,0,0)]
        for i,_pt in enumerate(pts): coeffs[(i,0,0,0)]=PyFraction(1,i+1)
        if not coeffs: coeffs[(0,0,0,0)]=PyFraction(1,1)
        if self._prior_rectified_psi is not None and self._prior_deviation_sq not in (None, PyFraction(0,1)):
            coeffs[(0,0,0,0)]=(coeffs[(0,0,0,0)]+self._prior_rectified_psi.a)/PyFraction(2,1)
        return coeffs
    def _generate_trajectory(self):
        traj=[]; base=self.phi
        for k in range(8):
            ang=PyFraction(self.prime*(k+1),100); c=PyFraction(1,1)-(ang*ang)/PyFraction(2,1); s=ang
            traj.append(base.mul(SymbolicQuaternion(c,s,s*PyFraction(k+1,8),PyFraction(0,1))))
        return traj
    def _hopf_map(self, q):
        return (q.a*q.a+q.b*q.b-q.c*q.c-q.d*q.d, PyFraction(2,1)*(q.a*q.c+q.b*q.d), PyFraction(2,1)*(q.a*q.d-q.b*q.c))
    def step(self, x, x_source="crawler-hash"):
        try: xf=x if isinstance(x, PyFraction) else PyFraction(str(x))
        except Exception: xf=PyFraction(1,16**64)
        self.last_x_input_raw=xf; xf=PyFraction(1,1)+xf; self.last_x=xf; self.last_x_source=str(x_source)
        try: self.prime=_next_prime_after(self.prime)
        except Exception: self.prime+=1
        self.prime_count+=1; self.tick+=1; self.generation=self.tick
        q=self.lattice_points[-1] if self.lattice_points else (0,0,0,0)
        try: offs=_LEECH_OFFSETS
        except Exception: offs=[(2,0,0,0),(-2,0,0,0),(0,2,0,0),(0,-2,0,0),(0,0,2,0),(0,0,-2,0),(0,0,0,2),(0,0,0,-2)]
        chosen=None; start=self.prime % len(offs) if offs else 0
        for attempt in range(len(offs)):
            d=offs[(start+attempt)%len(offs)]; dot=sum(di*qi for di,qi in zip(d,q))
            if dot<=0 and q!=(0,0,0,0): d=tuple(-v for v in d)
            cand=tuple(qi+di for qi,di in zip(q,d)); overlap=False
            for ex in self.lattice_points:
                if sum((a-b)*(a-b) for a,b in zip(cand,ex))<4: overlap=True; break
            if q != (0,0,0,0):
                _dist_q = sum((a-b)*(a-b) for a,b in zip(cand, q))
                if _dist_q != 4:
                    continue
            if not overlap: chosen=cand; break
        if chosen is not None:
            self.lattice_points.append(chosen); self.lattice_count=len(self.lattice_points)-1; steps=self.lattice_count
            # Tangent check: offset length squared is 4 for |offset|=2. If the new
            # point sits exactly 4 from the previous point, it is tangent.
            try:
                _ds = sum((a-b)*(a-b) for a,b in zip(chosen, q))
                self.last_tangent = (_ds == 4)
            except Exception:
                self.last_tangent = False
            self.s2=PyFraction(4*steps*steps,1); self.r2=PyFraction(sum(v*v for v in chosen),1); self.deviation=self.s2-self.r2
            self.last_arc_sq=self.s2; self.last_radius_sq=self.r2; self.last_deviation_sq=self.deviation; self.coherent=(self.s2==self.r2)
            if self.coherent: self.coherent_steps+=1
            self.phi=SymbolicQuaternion(PyFraction(chosen[0],1),PyFraction(chosen[1],1),PyFraction(chosen[2],1),PyFraction(chosen[3],1))
        else:
            self.deviation=self.s2-self.r2; self.last_deviation_sq=self.deviation; self.coherent=(self.s2==self.r2)
        coeffs=self._integrate_wavefunction_symbolic(); psi_a=coeffs.get((0,0,0,0),PyFraction(1,1))
        self.psi=SymbolicQuaternion(psi_a, xf, PyFraction(self.prime,1)/PyFraction(100,1), self.deviation)
        self.last_trajectory=self._generate_trajectory(); self.last_hopf_base=self._hopf_map(self.phi)
        if self.deviation!=0:
            denom=PyFraction(1,1)+abs(self.deviation); corr=self.phi.scale(self.deviation/denom)
            self.psi=_dbz_quaternion(self.psi, corr); self._prior_rectified_psi=self.psi
        else: self._prior_rectified_psi=None
        self._prior_deviation_sq=self.deviation; psi_norm=self.psi.norm_sq(); self.last_I=self.metrics.compute_metric(valid_pairs=int(self.prime_count), total_primes=int(self.prime_count), pi_x=int(self.prime_count), x=PyFraction(self.prime,1), curl_phi_norm=self.phi.norm_sq(), target_arc=self.s2, target_radius=self.r2); self.I=self.last_I
        try: self.consciousness.psi=self.psi; self.consciousness.phi=self.phi; _obs=self.consciousness.observe()
        except Exception: _obs=PyFraction(0,1)
        self.last_evolution=self.evolution.evolve_step(self.last_I, self.psi, SymbolicQuaternion(PyFraction(self.prime,1),PyFraction(0,1),PyFraction(0,1),PyFraction(0,1)), self.deviation, tick=self.tick)
        try:
            cyc=["A","U","M","AUM"]; self.last_linguistic_trajectory=[]
            for k in range(4):
                self.last_linguistic_trajectory.extend(self.linguist.encode_syllable(cyc[(self.tick+k)%4]))
        except Exception: self.last_linguistic_trajectory=[]
        self.last_logic_hash=str(_deterministic_hash_frac(f"{self.tick}:{self.prime}:{self.deviation}:{self.last_I}")); self.state="coherent" if self.coherent else "rectified"
        return self.to_dict()
    def run_autonomous(self, steps=1, x_source="crawler-hash"):
        out=None
        for _ in range(int(steps)): out=self.step(self.last_x, x_source=x_source)
        return out
    def snapshot(self): return self.to_dict()
    def to_dict(self):
        return {"tick":int(self.tick),"generation":int(self.generation),"prime":int(self.prime),"prime_count":int(self.prime_count),"primes":[str(p) for p in self.primes[-8:]],"lattice_points":[list(p) for p in self.lattice_points[-24:]],"lattice_count":int(self.lattice_count),"s2":str(self.s2),"r2":str(self.r2),"deviation":str(self.deviation),"deviation_sq":str(self.last_deviation_sq),"coherent":bool(self.coherent),"coherent_steps":int(self.coherent_steps),"I":str(self.last_I),"I_parts":dict(self.metrics.last_parts),"I_threshold":"2/3","I_gate":"2/3","I_unity":"1","I_gate_met":bool(self.last_I >= PyFraction(2,3)),"I_unity_met":bool(self.last_I == PyFraction(1,1)),"psi":self.psi.to_dict(),"phi":self.phi.to_dict(),"hopf":{"a":str(self.last_hopf_base[0]),"b":str(self.last_hopf_base[1]),"c":str(self.last_hopf_base[2]),"d":"0"},"hopf_base":[str(self.last_hopf_base[0]),str(self.last_hopf_base[1]),str(self.last_hopf_base[2])],"trajectory":[q.to_dict() for q in self.last_trajectory],"trajectory_count":len(self.last_trajectory),"evolution":self.last_evolution,"self_evolution":self.last_evolution,"lingoso":[q.to_dict() for q in self.last_linguistic_trajectory],"observer":str(self.consciousness.observe()) if hasattr(self,"consciousness") else "0","last_x":str(self.last_x),"x_input_raw":str(getattr(self, "last_x_input_raw", self.last_x)),"last_x_source":str(self.last_x_source),"last_logic_hash":str(self.last_logic_hash),"state":str(self.state),"dbz_persisted":bool(self._prior_rectified_psi is not None)}

class CrawlerState:
    """Frontier queue only. No automatic fetching, no binary fetches."""
    BLOCKLIST = ("meta.wikimedia.org", "wikimedia.org/w/api", "thumb.wikimedia.org", "upload.wikimedia.org", "featuredfeed")
    def __init__(self):
        self.frontier = []
        self.visited = []
        self.running = False
        self.last_hash_frac = None
        self.last_hash_hex = ''
        self.last_hash_url = ''
        self.last_hash_at = ''
    def set_from_content(self, content, url=''):
        # FG x: hash fraction of most recently crawled document.
        # content is bytes or str. Stores raw hex, fraction, url, timestamp.
        # Returns {'ok': True, 'hash_hex': ..., 'hash_frac': str(...)}.
        try:
            import hashlib as _hl2, datetime as _dt2
            raw = content if isinstance(content, (bytes, bytearray)) else str(content or '').encode('utf-8')
            hexh = _hl2.sha256(raw).hexdigest()
            frac = _hash_to_fraction(hexh)
            self.last_hash_hex = hexh
            self.last_hash_frac = frac
            self.last_hash_url = str(url or '')
            try: self.last_hash_at = _dt2.datetime.now().isoformat()
            except Exception: self.last_hash_at = ''
            return {'ok': True, 'hash_hex': hexh, 'hash_frac': str(frac), 'url': str(url or '')}
        except Exception as e:
            return {'ok': False, 'error': str(e)}
    def fetch_and_hash(self, url):
        # Fetch one document (text only, 512 KiB cap, 10 s timeout), blocklist-checked,
        # hash it and set last_hash_frac. Never fetches binaries, never auto-crawls.
        # Returns set_from_content result or error. Caller is /crawler-enqueue.
        try:
            import urllib.request as _ur, datetime as _dt3
            u = (url or '').strip()
            if not u.startswith('http://') and not u.startswith('https://'):
                return {'ok': False, 'error': 'url_must_start_with_http'}
            for bad in self.BLOCKLIST:
                if bad in u:
                    return {'ok': False, 'error': 'url_blocklisted'}
            req = _ur.Request(u, headers={'User-Agent': 'AEI-Crawler/1.0', 'Accept': 'text/plain,text/html;q=0.9'})
            with _ur.urlopen(req, timeout=10) as r:
                ctype = str(r.headers.get('Content-Type', '') or '').lower()
                if 'image' in ctype or 'video' in ctype or 'audio' in ctype or 'octet-stream' in ctype:
                    return {'ok': False, 'error': 'binary_not_fetched'}
                data = r.read(524288)
            return self.set_from_content(data, url=u)
        except Exception as e:
            return {'ok': False, 'error': str(e)}
    def enqueue(self, url: str):
        u = (url or "").strip()
        if not u.startswith("http://") and not u.startswith("https://"):
            return {"ok": False, "error": "url_must_start_with_http"}
        for bad in self.BLOCKLIST:
            if bad in u:
                return {"ok": False, "error": "url_blocklisted"}
        if u not in self.frontier and u not in self.visited:
            self.frontier.append(u)
        return {"ok": True, "url": u, "frontier_size": len(self.frontier)}
    def to_dict(self):
        return {
            "frontier_size": len(self.frontier),
            "visited": len(self.visited),
            "visited_count": len(self.visited),
            "frontier": list(self.frontier[:20]),
            "running": bool(self.running),
        }

class CSFeedbackStore:
    def __init__(self):
        self.entries = []
    def add(self, entry):
        e = dict(entry or {})
        e["at"] = datetime.now().isoformat()
        self.entries.append(e)
        return e
    def list(self):
        return list(self.entries)

def _symbol_class_counts():
    try:
        keys = list(SYMBOL_MAP.keys())
    except Exception:
        keys = []
    crypto = len([k for k in keys if k.endswith("-USD")])
    futures = len([k for k in keys if "FUT" in k or k.endswith("-F")])
    equities = len([k for k in keys if k.startswith("EQ:")])
    forex = len([k for k in keys if k.endswith("=X") or "FOREX" in k])
    indices = len([k for k in keys if k.startswith("^") or "INDEX" in k])
    return {
        "crypto_pairs": int(crypto),
        "futures_symbols": int(futures),
        "equities_symbols": int(equities),
        "forex_pairs": int(forex),
        "indices_symbols": int(indices),
    }


def _bb_family_from_bars(bars):
    """FF BB family: periods 3..60, deviation 2, close, shift 0, population sigma. Returns list of dicts for periods with enough real bars."""
    out = []
    try:
        closes = []
        for b in (bars or []):
            try:
                c = b.get("close") if isinstance(b, dict) else None
                if c is None:
                    continue
                closes.append(Decimal(str(c)))
            except Exception:
                continue
        for period in range(3, 61):
            if len(closes) < period:
                continue
            window = closes[-period:]
            try:
                mid = sum(window, Decimal("0")) / Decimal(period)
                var = sum((x - mid) * (x - mid) for x in window) / Decimal(period)
                try:
                    sd = var.sqrt()
                except Exception:
                    sd = var.sqrt() if var > 0 else Decimal("0")
                dev = Decimal("2") * sd
                out.append({"period": int(period), "mid": str(mid), "upper": str(mid + dev), "lower": str(mid - dev)})
            except Exception:
                continue
    except Exception:
        return []
    return out

def _bb58_from_bars(bars):
    """BBx58: period 58. Null until 58 real bars exist. No zero placeholder."""
    try:
        closes = []
        for b in bars or []:
            c = b.get("close") if isinstance(b, dict) else None
            if c is None:
                continue
            closes.append(Decimal(str(c)))
    except Exception:
        return None
    if len(closes) < 58:
        return None
    window = closes[-58:]
    mean = sum(window, Decimal("0")) / Decimal(58)
    var = sum((c - mean) * (c - mean) for c in window) / Decimal(58)
    try:
        sd = var.sqrt()
    except Exception:
        sd = Decimal("0")
    mid = mean
    upper = mid + Decimal(2) * sd
    lower = mid - Decimal(2) * sd
    return {
        "period": 58,
        "lower": str(lower),
        "mid": str(mid),
        "upper": str(upper),
        "sd": str(sd),
        "last": str(window[-1]),
    }

def _acoustization_from_seed(seed_dict):
    # Display sonification from seed deviation.
    try: dev=PyFraction(str(seed_dict.get('deviation','0')))
    except Exception: dev=PyFraction(0,1)
    freq=PyFraction(440,1)+(abs(dev)%PyFraction(100,1)); amp=PyFraction(1,1)/(PyFraction(1,1)+abs(dev)) if abs(dev)!=0 else PyFraction(1,1)
    try: _s2=PyFraction(str(seed_dict.get('s2','0')))
    except Exception: _s2=PyFraction(0,1)
    try: _r2=PyFraction(str(seed_dict.get('r2','0')))
    except Exception: _r2=PyFraction(0,1)
    _sr = (_s2/_r2) if _r2 != 0 else PyFraction(0,1)
    _price = seed_dict.get('price') or seed_dict.get('last_price') or '0'
    return {'frequency': str(freq), 'base_freq': str(freq), 'filter_freq': str(freq), 'amplitude': str(amp), 'type':'sine','source':'seed deviation','origin':'display','lattice_notes': [str(freq), str(freq*PyFraction(2,1)), str(freq*PyFraction(3,1))], 'pulse': '1', 'price': str(_price), 'delta': str(dev), 'deviation': str(dev), 'sr_ratio': str(_sr)}

def _observer_from_seed(seed_dict):
    # Observer: 4D Riemann sum over 4^4 grid.
    # The seed carries single psi/phi quaternions. This function
    # builds a grid-varying field from them: at grid point (i,j,k,l) the
    # a-component is scaled by (i+1)/4, b by (j+1)/4, c by (k+1)/4, d by (l+1)/4,
    # and the term is sum_c psi_c(grid) * phi_c * psi_c(grid) * (1/256).
    # The term uses i,j,k,l.
    try:
        psi = seed_dict.get('psi') or {}; phi = seed_dict.get('phi') or {}
        def _fr(d,k):
            try: return PyFraction(str(d.get(k,'0')))
            except Exception: return PyFraction(0,1)
        pa,pb,pc,pd = _fr(psi,'a'),_fr(psi,'b'),_fr(psi,'c'),_fr(psi,'d')
        fa,fb,fc,fd = _fr(phi,'a'),_fr(phi,'b'),_fr(phi,'c'),_fr(phi,'d')
        total=PyFraction(0,1); count=0
        for i in range(4):
            for j in range(4):
                for k in range(4):
                    for l in range(4):
                        w=PyFraction(1,256)
                        sa = pa * PyFraction(i+1,4); sb = pb * PyFraction(j+1,4)
                        sc = pc * PyFraction(k+1,4); sd = pd * PyFraction(l+1,4)
                        term = (sa*fa*sa + sb*fb*sb + sc*fc*sc + sd*fd*sd) * w
                        total+=term; count+=1
        return {'O_psi': str(total), 'observer': str(total), 'grid': '4^4', 'points': int(count), 'psi_a': str(pa), 'psi_b': str(pb), 'psi_c': str(pc), 'psi_d': str(pd), 'note': 'Display observer from single psi/phi.', 'origin': 'display', 'real': str(total), 'imag': '0'}
    except Exception:
        return {'O_psi': None, 'observer': None, 'grid': '4^4', 'points': 0, 'psi_a': None, 'psi_b': None, 'psi_c': None, 'psi_d': None, 'note': 'WAITING', 'status': 'WAITING', 'origin': 'ConsciousnessOperator.observe'}

def _evolution_from_seed(seed_dict, bars):
    # FG evolution: SelfEvolutionCore result from seed, no opponent, no comparison of unlike units.
    try: ev = seed_dict.get('evolution') or seed_dict.get('self_evolution') or {}
    except Exception: ev = {}
    try: dev = PyFraction(str(seed_dict.get('deviation','0')))
    except Exception: dev = PyFraction(0,1)
    return {'tick': int(seed_dict.get('tick',0)), 'ae_dev': str(abs(dev)), 'evolution': ev, 'fitness': str(ev.get('fitness','0')) if isinstance(ev, dict) else '0', 'mutation': str(ev.get('mutation','none')) if isinstance(ev, dict) else 'none', 'note': 'FG SelfEvolutionCore.evolve_step. No opponent.'}

def _cs_translate(text: str) -> str:
    # No vowel-substitution map. CS is CS_LABELS, labels only, vars never renamed.
    # _cs_translate returns text unchanged; use _cs_label(key) for CS labels.
    return text or ''

def _build_fused_state(engine):
    st = engine.state
    seed = getattr(engine, "seed", None)
    seed_dict = seed.to_dict() if seed is not None else {"tick": 0, "generation": 0, "prime": 2, "prime_count": 0, "lattice_points": [], "lattice_count": 0, "s2": "0", "r2": "0", "deviation": "0", "coherent": False, "I": "0", "psi": {"a": "1", "b": "0", "c": "0", "d": "0"}, "phi": {"a": "0", "b": "0", "c": "0", "d": "0"}, "hopf": {"a": "0", "b": "0", "c": "0", "d": "0"}}
    try:
        _s2f = PyFraction(str(seed_dict.get("s2", "0")))
    except Exception:
        _s2f = PyFraction(0, 1)
    try:
        _r2f = PyFraction(str(seed_dict.get("r2", "0")))
    except Exception:
        _r2f = PyFraction(0, 1)
    seed_dict["sr_ratio"] = str((_s2f / _r2f) if _r2f != 0 else PyFraction(0, 1))
    bars = []
    for b in (engine.ohlcv_history or []):
        try:
            bars.append({
                "open": str(b.get("open", 0)),
                "high": str(b.get("high", 0)),
                "low": str(b.get("low", 0)),
                "close": str(b.get("close", 0)),
                "volume": str(b.get("volume", 0)),
                "timestamp": str(b.get("timestamp", "")),
                "provider": str(b.get("provider", "")),
            })
        except Exception:
            continue
    prev_price = None
    if len(bars) >= 2:
        prev_price = bars[-2].get("close")
    elif len(bars) == 1:
        prev_price = bars[-1].get("close")
    market_m = int(getattr(st, "authoritative_m", 0))
    market_n = int(getattr(st, "authoritative_n", 0))
    imbalance = market_m - market_n - 2
    _reg_idx0 = int(getattr(st, "h", 0)) - (int(getattr(st, "y", 0)) + 1)
    regime = st.Regime[_reg_idx0] if 0 <= _reg_idx0 < len(st.Regime) else "Unknown"
    try:
        feed_last_update = engine.feed.last_update()
        last_update = feed_last_update.isoformat() if feed_last_update else None
    except Exception:
        last_update = None
    feed = {
        "ordered": int(getattr(getattr(engine, "ordered_feed", None), "feed_ordered", 0)),
        "price": str(st.price) if st.price is not None else None,
        "prev_price": (str(prev_price) if prev_price is not None else None),
        "provider": str(getattr(st, "last_provider", "") or ""),
        "symbol": str(SYMBOL),
        "timeframe": str(INTERVAL),
        "last_update": last_update,
    }
    grid_names = ["ADX", "STOCH", "RVI", "AC", "FORCE", "OBV", "AD", "MFI", "MOM", "DeM", "WPR", "CCI", "RSI"]
    grid = {}
    try:
        idx = int(getattr(st, "Z", 0)) - (int(getattr(st, "y", 0)) + 1)
        for i, name in enumerate(grid_names):
            try:
                col = st.iA[i] if i < len(st.iA) else []
                v = col[idx] if 0 <= idx < len(col) else (col[-1] if col else None)
                grid[name] = (str(v) if (v is not None and len(bars) >= 14) else None)
            except Exception:
                grid[name] = None
        grid["count"] = len(bars)
        try:
            grid["ICHIMOKU"] = {"k": str(st.iIHKk), "t": str(st.iIHKt)} if len(bars) >= 14 else None
        except Exception:
            grid["ICHIMOKU"] = None
    except Exception:
        grid = {"count": len(bars)}
    bb = _bb58_from_bars(engine.ohlcv_history or [])
    sig_hist = []
    try:
        for s in (getattr(st, "signal_history", []) or []):
            if isinstance(s, dict):
                sig_hist.append(s)
            else:
                sig_hist.append({"side": str(s)})
    except Exception:
        sig_hist = []
    current_signal = sig_hist[-1] if sig_hist else None
    try:
        proj = engine.get_projection()
    except Exception:
        proj = None
    try:
        orders = engine.list_orders()
    except Exception:
        orders = []
    fvg = []
    try:
        fvg = BRIDGE_STATE.list_fvgs()
    except Exception:
        fvg = []
    cs_feedback = []
    try:
        cs_feedback = engine.cs_feedback.list() if hasattr(engine, "cs_feedback") else []
    except Exception:
        cs_feedback = []
    crawler_dict = {}
    try:
        crawler_dict = engine.crawler.to_dict() if hasattr(engine, "crawler") else {"frontier_size": 0, "visited": 0, "running": False}
    except Exception:
        crawler_dict = {"frontier_size": 0, "visited": 0, "running": False}
    acoust = _acoustization_from_seed(seed_dict)
    _fg_observer = seed_dict.get("observer")
    if _fg_observer is None:
        observer = {"observer": None, "O_psi": None, "status": "WAITING", "origin": "ConsciousnessOperator.observe"}
    else:
        observer = {"observer": str(_fg_observer), "O_psi": str(_fg_observer), "status": "ok", "origin": "ConsciousnessOperator.observe"}
    evolution = _evolution_from_seed(seed_dict, bars)
    cs = {
        "tick": int(seed_dict.get("tick", 0)),
        "s2": seed_dict.get("s2"),
        "r2": seed_dict.get("r2"),
        "deviation": seed_dict.get("deviation"),
        "coherence": seed_dict.get("coherent"),
        "phi": seed_dict.get("phi"),
        "hopf": seed_dict.get("hopf"),
        "hopf_base": seed_dict.get("hopf"),
        "lattice_points": seed_dict.get("lattice_points"),
        "feedback": cs_feedback,
    }
    aea_text = format_aea("state", {"seed": seed_dict, "aeea": {"regime": regime, "m": market_m, "n": market_n}})
    aea_notification = {"text": aea_text, "kind": "state", "tick": int(seed_dict.get("tick", 0))}
    aeea = {
        "symbol": str(SYMBOL),
        "timeframe": str(INTERVAL),
        "last_price": str(st.price) if st.price is not None else None,
        "delta": int(imbalance),
        "m": int(market_m),
        "n": int(market_n),
        "regime": regime,
        "current_signal": current_signal,
        "signal": current_signal,
        "signal_history": sig_hist,
        "bars": bars,
        "bb": bb,
        "indicators": grid,
        "grid_13d": grid,
        "projection": proj,
        "fvg": fvg,
        "orders": orders,
        "last_provider": str(getattr(st, "last_provider", "") or ""),
    }
    try:
        _bb_family = _bb_family_from_bars(engine.ohlcv_history or [])
    except Exception:
        _bb_family = []
    try:
        _mm = int(st.authoritative_m); _nn = int(st.authoritative_n)
        _imb = _mm - _nn - 2
        _delta_gate = (_imb == 0)
        _hl_gate = (_mm >= 12) or (_nn >= 12)
        _bridge_regime = "BULLISH" if _imb > 2 else ("BEARISH" if _imb < -2 else "NEUTRAL")
        _reg_idx = int(st.h) - (int(st.y) + 1)
        _eng_regime = st.Regime[_reg_idx] if 0 <= _reg_idx < len(st.Regime) else "Unknown"
    except Exception:
        _imb = None; _delta_gate = False; _hl_gate = False; _bridge_regime = "WAITING"; _eng_regime = "WAITING"; _mm = None; _nn = None
    return {
        "ordered": int(getattr(getattr(engine, "ordered_feed", None), "feed_ordered", 0)),
        "feed": feed,
        "aeea": aeea,
        "bb_family": _bb_family,
        "delta_gate": {"imbalance": (_imb if _imb is None else int(_imb)), "m": (_mm if _mm is None else int(_mm)), "n": (_nn if _nn is None else int(_nn)), "kronecker_delta": bool(_delta_gate), "met": bool(_delta_gate), "definition": "Kronecker delta(imbalance)=1 iff imbalance==0 iff m-n==2. Does NOT fire signals."},
        "hl_gate": {"m": (_mm if _mm is None else int(_mm)), "n": (_nn if _nn is None else int(_nn)), "met": bool(_hl_gate), "definition": "H/L gate: BUY when m>=12, SELL when n>=12. This fires signals. NOT the Kronecker gate."},
        "bridge_regime": str(_bridge_regime),
        "engine_regime": str(_eng_regime),
        "seed": seed_dict,
        "cs": cs,
        "cs_feedback": cs_feedback,
        "acoustization": acoust,
        "observer": observer,
        "evolution": evolution,
        "crawler": crawler_dict,
        "crawlerFrontier": crawler_dict.get("frontier_size"),
        "crawlerVisited": crawler_dict.get("visited"),
        "crawlerRunning": crawler_dict.get("running"),
        "aea_notification": aea_notification,
        "status": "ok",
    }

class BridgeState:
    def __init__(self):
        self._lock = threading.Lock()
        self._fvgs: Dict[int, Dict[str, Any]] = {}
        self._next_fvg_idx = 0
        self._webapp_sessions: Dict[int, Dict[str, Any]] = {}
        self._handshake_lock = threading.Lock()

    def register_webapp_session(self, user_id: int, username: Optional[str], chat_id: Optional[int] = None) -> bool:
        with self._handshake_lock:
            self._webapp_sessions[user_id] = {
                "user_id": user_id, "username": username, "chat_id": chat_id,
                "first_seen": self._webapp_sessions.get(user_id, {}).get("first_seen", datetime.now().isoformat()),
                "last_seen": datetime.now().isoformat(),
            }
        engine = BRIDGE_ENGINE_REF.get("engine")
        if engine is not None:
            try:
                engine.state.webapp_user_id = user_id
                engine.state.webapp_username = username
                engine.state.webapp_verified = True
                engine.state.webapp_last_seen = datetime.now()
                if chat_id is not None:
                    engine.state.chat_id = chat_id
            except Exception as e:
                logger.warning(f"register_webapp_session → engine map failed: {e}")
        logger.info(f"🔗 Web App session registered: user_id={user_id}, username={username}")
        return True

    def add_fvg(self, fvg_type: str, price_str: str, user_id: Optional[int] = None, requested_idx: Optional[int] = None) -> int:
        if fvg_type not in ("top", "bott"):
            raise ValueError("fvg_type must be 'top' or 'bott'")
        try:
            price_dec = Decimal(str(price_str))
        except Exception:
            raise ValueError("price must be a decimal string")
        if price_dec <= Decimal('0.0'):
            raise ValueError("price must be > 0")
        with self._lock:
            if requested_idx is not None and isinstance(requested_idx, int) and requested_idx >= 0:
                idx = requested_idx
                if idx >= self._next_fvg_idx:
                    self._next_fvg_idx = idx + 1
            else:
                if self._next_fvg_idx < 1000000:
                    self._next_fvg_idx = 1000000
                idx = self._next_fvg_idx
                self._next_fvg_idx += 1
            self._fvgs[idx] = {
                "type": fvg_type, "price": str(price_dec), "idx": idx,
                "created": datetime.now().isoformat(), "user_id": user_id,
            }
        engine = BRIDGE_ENGINE_REF.get("engine")
        if engine is not None:
            engine.state.fvg_anchor_map[idx] = {
                "idx": idx, "type": fvg_type, "price": str(price_dec),
                "created": datetime.now().isoformat(),
            }
        _emit_toast("fvg", {
            "action": "commit",
            "type": fvg_type,
            "price": str(price_dec),
            "idx": idx,
            "tick": int(engine.state.tick) if engine is not None else 0,
        })
        return idx

    def remove_fvg(self, idx: int) -> bool:
        with self._lock:
            if idx in self._fvgs:
                removed_record = self._fvgs.pop(idx)
                removed = True
            else:
                removed_record = None
                removed = False
        engine = BRIDGE_ENGINE_REF.get("engine")
        if engine is not None:
            engine.state.fvg_anchor_map.pop(idx, None)
        if removed and removed_record is not None:
            _emit_toast("fvg", {
                "action": "remove",
                "type": removed_record.get("type", "top"),
                "price": removed_record.get("price", "0"),
                "idx": idx,
                "tick": int(engine.state.tick) if engine is not None else 0,
            })
        return removed

    def list_fvgs(self) -> List[Dict[str, Any]]:
        with self._lock:
            return list(self._fvgs.values())

BRIDGE_STATE = BridgeState()
BRIDGE_ENGINE_REF: Dict[str, Any] = {"engine": None, "bot": None, "public_url": None}

def _require_auth(handler: "BridgeHandler") -> bool:
    if not REQUIRE_AUTH:
        return True
    if not TELEGRAM_BOT_TOKEN_ENV:
        return False
    relay_key = handler.headers.get("X-Relay-Key", "").strip()
    if RELAY_KEY and (relay_key != RELAY_KEY):
        return False
    raw_init = handler.headers.get("X-Telegram-Init-Data", "").strip()
    if not raw_init:
        return False
    verified = verify_telegram_init_data(raw_init, TELEGRAM_BOT_TOKEN_ENV)
    if not verified or not verified.get("user"):
        return False
    user = verified.get("user") or {}
    user_id = user.get("id")
    if _is_banned_user(user_id):
        logger.warning(f"Bridge auth rejected: banned user_id={user_id}")
        return False
    if not _is_allowed_user(user_id):
        logger.warning(f"Bridge auth rejected: unauthorized user_id={user_id}")
        return False
    return True

# ============================================================================
# TUNNEL MANAGER
# ============================================================================
class TunnelManager:
    URL_RE_CLOUDFLARED = _re_bridge.compile(r"https://[a-z0-9\-]+\.trycloudflare\.com")
    URL_RE_NGROK = _re_bridge.compile(r"https://[a-z0-9\-]+\.ngrok(?:-free)?\.app")
    URL_RE_SERVEO = _re_bridge.compile(r"https://[a-z0-9\-]+\.serveo\.net")

    def __init__(self, port: int, prefer: str = "cloudflared", timeout: int = 45):
        self.port = port
        self.prefer = prefer
        self.timeout = timeout
        self.process: Optional[subprocess.Popen] = None
        self.public_url: Optional[str] = None
        self.provider: Optional[str] = None

    def _which(self, name: str) -> Optional[str]:
        from shutil import which
        return which(name)

    def _spawn(self, cmd: List[str]) -> subprocess.Popen:
        logger.info(f"🌐 Spawning tunnel: {' '.join(cmd)}")
        return subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=1, universal_newlines=True)

    def _scan_for_url(self, proc: subprocess.Popen, regex: "_re_bridge.Pattern[str]", deadline: float) -> Optional[str]:
        assert proc.stdout is not None
        for raw in proc.stdout:
            line = raw.rstrip("\n")
            if line:
                logger.debug(f"[tunnel] {line}")
            m = regex.search(line)
            if m:
                return m.group(0)
            if time.time() > deadline:
                return None
        return None

    def _try_cloudflared(self) -> Optional[str]:
        if not self._which("cloudflared"):
            return None
        try:
            proc = self._spawn(["cloudflared", "tunnel", "--url", f"http://127.0.0.1:{self.port}", "--no-autoupdate"])
        except Exception as e:
            logger.warning(f"cloudflared spawn failed: {e}")
            return None
        deadline = time.time() + self.timeout
        url = self._scan_for_url(proc, self.URL_RE_CLOUDFLARED, deadline)
        if url:
            self.process = proc
            self.public_url = url
            self.provider = "cloudflared"
            return url
        try:
            proc.terminate()
        except Exception:
            pass
        return None

    def _try_ngrok(self) -> Optional[str]:
        if not self._which("ngrok"):
            return None
        try:
            proc = self._spawn(["ngrok", "http", str(self.port), "--log=stdout"])
        except Exception as e:
            logger.warning(f"ngrok spawn failed: {e}")
            return None
        deadline = time.time() + self.timeout
        url = self._scan_for_url(proc, self.URL_RE_NGROK, deadline)
        if url:
            self.process = proc
            self.public_url = url
            self.provider = "ngrok"
            return url
        try:
            proc.terminate()
        except Exception:
            pass
        return None

    def _try_serveo(self) -> Optional[str]:
        if not self._which("ssh"):
            return None
        try:
            proc = self._spawn(["ssh", "-o", "StrictHostKeyChecking=no", "-o", "ServerAliveInterval=30", "-R", f"80:127.0.0.1:{self.port}", "serveo.net"])
        except Exception as e:
            logger.warning(f"serveo spawn failed: {e}")
            return None
        deadline = time.time() + self.timeout
        url = self._scan_for_url(proc, self.URL_RE_SERVEO, deadline)
        if url:
            self.process = proc
            self.public_url = url
            self.provider = "serveo"
            return url
        try:
            proc.terminate()
        except Exception:
            pass
        return None

    def start(self) -> Optional[str]:
        if TELEGRAM_WEBAPP_URL:
            self.public_url = TELEGRAM_WEBAPP_URL
            self.provider = "explicit"
            BRIDGE_ENGINE_REF["public_url"] = self.public_url
            logger.info(f"🌐 Using explicit TELEGRAM_WEBAPP_URL: {self.public_url}")
            return self.public_url
        order = [self.prefer] + [p for p in ("cloudflared", "ngrok", "serveo") if p != self.prefer]
        for provider in order:
            method = getattr(self, f"_try_{provider}", None)
            if method is None:
                continue
            try:
                url = method()
            except Exception as e:
                logger.warning(f"Tunnel provider {provider} raised: {e}")
                url = None
            if url:
                BRIDGE_ENGINE_REF["public_url"] = url
                logger.info(f"🌐 Tunnel established via {provider}: {url}")
                return url
        logger.warning("⚠️ No tunnel available. Telegram Mini App will require manual TELEGRAM_WEBAPP_URL.")
        return None

    def stop(self) -> None:
        if self.process is None:
            return
        try:
            self.process.terminate()
            self.process.wait(timeout=5)
        except Exception:
            try:
                self.process.kill()
            except Exception:
                pass
        self.process = None
        logger.info("🌐 Tunnel stopped")

# ============================================================================
# BRIDGE HANDLER
# ============================================================================
class BridgeHandler(BaseHTTPRequestHandler):
    server_version = "AEI-Bridge"

    def log_message(self, fmt, *args):
        return

    def _set_cors(self) -> None:
        raw = (CORS_ORIGIN or "").strip()
        req_origin = ""
        try:
            req_origin = (self.headers.get("Origin") or "").strip()
        except Exception:
            req_origin = ""
        self.send_header("Vary", "Origin")
        if (not raw) or (raw == "*"):
            self.send_header("Access-Control-Allow-Origin", "*")
        else:
            allow = [p.strip() for p in raw.split(",") if p.strip()]
            if req_origin and (req_origin in allow):
                self.send_header("Access-Control-Allow-Origin", req_origin)
                self.send_header("Access-Control-Allow-Credentials", "true")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, DELETE, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type, Accept, X-Telegram-Init-Data, X-Relay-Key, X-Limit, X-Since")
        self.send_header("Access-Control-Max-Age", "86400")

    def _send_json(self, code: int, payload: Dict[str, Any]) -> None:
        body = json.dumps(payload, default=str).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self._set_cors()
        self.end_headers()
        self.wfile.write(body)

    def _send_html(self, code: int, html: str) -> None:
        body = html.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self._set_cors()
        self.end_headers()
        self.wfile.write(body)

    def _read_body(self) -> bytes:
        length = int(self.headers.get("Content-Length", "0") or 0)
        if length <= 0:
            return b""
        return self.rfile.read(length)

    def _read_json(self) -> Dict[str, Any]:
        raw = self._read_body()
        if not raw:
            return {}
        try:
            return json.loads(raw.decode("utf-8"))
        except Exception:
            return {}

    def do_OPTIONS(self) -> None:
        self.send_response(204)
        self._set_cors()
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_GET(self) -> None:
        path = urlparse(self.path).path
        query = dict(parse_qsl(urlparse(self.path).query))

        if path == "/health":
            engine = BRIDGE_ENGINE_REF.get("engine")
            last = None
            stale = True
            age_seconds = None
            if engine is not None:
                lu = engine.feed.last_update()
                if lu:
                    last = lu.isoformat()
                    age_seconds = (datetime.now() - lu).total_seconds()
                    stale = age_seconds > 60
            self._send_json(200, {
                "ok": not stale, "service": "aei-bridge",
                "last_price_update": last,
                "age_seconds": age_seconds, "stale": stale,
                "engine_initialized": bool(engine.state.FG) if engine else False,
                "indicator_populate_count": int(engine._indicator_populate_count) if engine else 0,
                "imbalance_fire_count": int(engine._imbalance_fire_count) if engine else 0,
                "ohlcv_count": len(engine.ohlcv_history) if engine else 0,
                "signal_count": len(engine.state.signal_history) if engine else 0,
                "bar_close_count": int(engine.state.bar_close_count) if engine else 0,
                "relay_healthy": (engine.feed.failure_count() < 3) if engine else True,
                "provider": engine.feed.last_provider() if engine else "",
                "projection_computed_at": engine.state.projection_computed_at if engine else None,
                "projection_trigger": engine.state.projection_trigger if engine else "",
                "symbol_class_counts": _symbol_class_counts(),
            })
            return

        if path not in ("/", "/index.html") and not _require_auth(self):
            self._send_json(401, {"error": "unauthorized", "detail": "Missing or invalid X-Telegram-Init-Data"})
            return

        if path == "/config":
            self._send_json(200, {
                "tls": BRIDGE_USE_TLS,
                "port": BRIDGE_PORT, "host": BRIDGE_HOST, "symbol": SYMBOL,
                "webapp_enabled": True, "cors_origin": CORS_ORIGIN,
                "relay_gated": bool(RELAY_KEY),
                "x_period_constant": X_PERIOD, "y_start_constant": Y_START,
                "require_auth": REQUIRE_AUTH,
                "push_on_signal": PUSH_ON_SIGNAL,
                "push_on_execution": PUSH_ON_EXECUTION,
                "push_on_fvg": PUSH_ON_FVG,
                "push_on_close": PUSH_ON_CLOSE,
                "arc_projection_horizon": ARC_PROJECTION_HORIZON,
                "arc_projection_step": ARC_PROJECTION_STEP,
                "arc_projection_damping": str(ARC_PROJECTION_DAMPING_D),
            })
            return

        if path == "/settings":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            self._send_json(200, engine.get_settings())
            return

        if path == "/toasts":
            try:
                since = int(self.headers.get("X-Since", query.get("since", "0")))
            except (TypeError, ValueError):
                since = 0
            with _TOAST_LOCK:
                toasts = [t for t in _TOAST_BUFFER if t.get("seq", 0) > since]
                latest_seq = _TOAST_SEQ
                first_available = _TOAST_FIRST_AVAILABLE_SEQ
            self._send_json(200, {
                "toasts": toasts,
                "count": len(toasts),
                "latest_seq": latest_seq,
                "first_available_seq": first_available,
            })
            return

        if path == "/projection":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            self._send_json(200, engine.get_projection())
            return

        if path == "/state":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready", "detail": "Engine hasn't started. Use /start_feed in the bot."})
                return
            st = engine.state
            idx = st.Z - (st.y + 1)
            regime = st.Regime[idx] if 0 <= idx < len(st.Regime) else "Unknown"
            self._send_json(200, {
                "symbol": SYMBOL,
                "price": str(st.price),
                "bid": str(engine.price_history[-1].bid) if engine.price_history else "0.0",
                "ask": str(engine.price_history[-1].ask) if engine.price_history else "0.0",
                "signal": str(st.signal),
                "regime": regime,
                "tick": int(st.tick),
                "m_count": int(st.authoritative_m),
                "n_count": int(st.authoritative_n),
                "m_at_h": int(st.last_kronecker_m),
                "n_at_h": int(st.last_kronecker_n),
                "h_bar": int(st.h),
                "timestamp": datetime.now().isoformat(),
                "webapp_user_id": st.webapp_user_id,
                "webapp_username": st.webapp_username,
                "last_price_update": engine.feed.last_update().isoformat() if engine.feed.last_update() else None,
                "engine_initialized": bool(st.FG),
                "consecutive_zero_prices": int(engine._consecutive_zero_prices),
                "relay_healthy": (engine.feed.failure_count() < 3),
                "indicator_populate_count": int(engine._indicator_populate_count),
                "imbalance_fire_count": int(engine._imbalance_fire_count),
                "comment_line": engine._format_comment_line(),
                "provider": st.last_provider,
                "last_volume": str(st.last_volume),
            })
            return

        if path == "/miniapp-state":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready", "detail": "Engine hasn't started. Use /start_feed in the bot."})
                return
            st = engine.state
            idx = st.Z - (st.y + 1)
            regime = st.Regime[idx] if 0 <= idx < len(st.Regime) else "Unknown"
            fvg_anchors = []
            for idx_i, p in enumerate(st.Premium):
                if p > Decimal('0.0'):
                    fvg_anchors.append({"idx": idx_i, "type": "top", "price": str(p)})
            for idx_i, p in enumerate(st.Discount):
                if p > Decimal('0.0'):
                    fvg_anchors.append({"idx": idx_i, "type": "bottom", "price": str(p)})
            for bridge_idx, rec in BRIDGE_STATE._fvgs.items():
                fvg_anchors.append({
                    "idx": bridge_idx,
                    "type": "top" if rec["type"] == "top" else "bottom",
                    "price": rec["price"],
                })
            h_idx = st.h - (st.y + 1)
            m_at_h = 1 if (0 <= h_idx < len(st.k) and st.k[h_idx]) else 0
            n_at_h = 1 if (0 <= h_idx < len(st.l) and st.l[h_idx]) else 0
            market_m = int(st.authoritative_m)
            market_n = int(st.authoritative_n)
            market_imbalance = market_m - market_n - 2
            if market_imbalance > 2:
                market_regime = "BULLISH"
            elif market_imbalance < -2:
                market_regime = "BEARISH"
            else:
                market_regime = "NEUTRAL"
            premium_series = [str(p) for p in st.Premium]
            discount_series = [str(p) for p in st.Discount]
            payload = {
                "symbol": SYMBOL,
                "price": str(st.price),
                "regime": regime,
                "tick": int(st.tick),
                "m_count": market_m,
                "n_count": market_n,
                "m_at_h": m_at_h,
                "n_at_h": n_at_h,
                "h_bar": int(st.h),
                "market_m": market_m,
                "market_n": market_n,
                "market_imbalance": market_imbalance,
                "market_regime": market_regime,
                            "last_price_update": (engine.feed.last_update().isoformat() if engine is not None and engine.feed.last_update() else None),
                "relay_healthy": (engine.feed.failure_count() < 3),
                "X_PERIOD": X_PERIOD,
                "Y_START": Y_START,
                "fvg_anchors": fvg_anchors,
                "premium_series": premium_series,
                "discount_series": discount_series,
                "recent_signals": st.signal_history[-20:],
                "ohlcv_count": len(engine.ohlcv_history),
                "signal_count": len(st.signal_history),
                "last_signal_at": st.last_signal_at,
                "bar_close_count": int(st.bar_close_count),
                "engine_initialized": bool(st.FG),
                "KC": bool(st.KC),
                "invert": bool(st.invert),
                "tag": int(st.tag),
                "prime": int(st.prime),
                "dime": int(st.dime),
                "mem": int(st.mem),
                "A": bool(st.A),
                "B": bool(st.B),
                "C": bool(st.C),
                "c": bool(st.c),
                "tick_tock": bool(st.tick_tock),
                "signature": bool(st.signature),
                "safety": bool(st.safety),
                "trailing_stop_active": bool(st.trailing_stop_active),
                "trailing_stop_price": str(st.trailing_stop_price),
                "trailing_take_profit": str(st.trailing_take_profit),
                "trailing_stop_entry": str(st.trailing_stop_entry),
                "trailing_stop_side": st.trailing_stop_side,
                "has_open_long": bool(st.has_open_long),
                "has_open_short": bool(st.has_open_short),
                "lOrder_id": int(st.lOrder_id),
                "kOrder_id": int(st.kOrder_id),
                "on_track_runs": int(st.on_track_runs),
                "on_stand_runs": int(st.on_stand_runs),
                "last_kronecker_bar": int(engine._last_kronecker_bar),
                "last_kronecker_m": int(st.last_kronecker_m),
                "last_kronecker_n": int(st.last_kronecker_n),
                "last_kronecker_h": int(st.last_kronecker_h),
                "authoritative_m": int(st.authoritative_m),
                "authoritative_n": int(st.authoritative_n),
                "authoritative_h": int(st.authoritative_h),
                "X_scan": int(st.X_scan),
                "Y_scan": int(st.Y_scan),
                "S": int(st.S),
                "T": int(st.T),
                "r": int(st.r),
                "ir": int(st.ir),
                "Z": int(st.Z),
                "z": int(st.z),
                "O": int(st.O),
                "o": int(st.o),
                "W": int(st.W),
                "w": int(st.w),
                "I": int(st.I),
                "iI": int(st.iI),
                "J": int(st.J),
                "iJ": int(st.iJ),
                "iZ": int(st.iZ),
                "iz": int(st.iz),
                "iW": int(st.iW),
                "iw": int(st.iw),
                "iO": int(st.iO),
                "io": int(st.io),
                "iATR": float(st.iATR),
                "iStdDev": float(st.iStdDev),
                "iIHKk": float(st.iIHKk),
                "iIHKt": float(st.iIHKt),
                "indicator_populate_count": int(engine._indicator_populate_count),
                "imbalance_fire_count": int(engine._imbalance_fire_count),
                "lPass": str(st.lPass),
                "ilPass": str(st.ilPass),
                "kPass": str(st.kPass),
                "ikPass": str(st.ikPass),
                "comment_line": engine._format_comment_line(),
                "provider": st.last_provider,
                "last_volume": str(st.last_volume),
                "projection_meta": st.projection_meta,
                "projection_computed_at": st.projection_computed_at,
                "projection_trigger": st.projection_trigger,
                "last_inbound_message_id": st.last_inbound_message_id,
            }
            try:
                payload.update(_build_fused_state(engine))
            except Exception as _fe:
                logger.warning(f"Fused state enrichment failed: {_fe}")
            self._send_json(200, payload)
            return

        if path == "/ohlcv":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            limit = 200
            try:
                limit = int(self.headers.get("X-Limit", query.get("limit", "200")))
            except Exception:
                pass
            bars = engine.ohlcv_history[-limit:]
            ohlcv_data = []
            last_ts = None
            # : emit null for absent fields, keep genuine zeros. A bar is
            # only admitted if its close is a real positive Decimal. This is
            # the single gate that keeps the TWA cursor readout honest: a
            # null field renders as "—", a genuine zero renders as "0.00000".
            def _emit_decimal(v, allow_zero):
                if v is None:
                    return None
                if isinstance(v, Decimal):
                    if not v.is_finite():
                        return None
                    if v == Decimal('0.0') and not allow_zero:
                        return None
                    return float(v)
                try:
                    f = float(v)
                except Exception:
                    return None
                if not math.isfinite(f):
                    return None
                if f == 0.0 and not allow_zero:
                    return None
                return f
            for bar in bars:
                close_v = bar.get("close")
                if close_v is None:
                    continue
                if isinstance(close_v, Decimal):
                    if not close_v.is_finite() or close_v <= Decimal('0.0'):
                        continue
                else:
                    try:
                        if float(close_v) <= 0.0:
                            continue
                    except Exception:
                        continue
                ts = bar.get("timestamp")
                if isinstance(ts, datetime):
                    ts_str = ts.isoformat()
                else:
                    ts_str = str(ts)
                last_ts = ts_str
                ohlcv_data.append({
                    "timestamp": ts_str,
                    "open": _emit_decimal(bar.get("open"), allow_zero=False),
                    "high": _emit_decimal(bar.get("high"), allow_zero=False),
                    "low": _emit_decimal(bar.get("low"), allow_zero=False),
                    "close": _emit_decimal(close_v, allow_zero=False),
                    "volume": _emit_decimal(bar.get("volume"), allow_zero=True),
                    "provider": str(bar.get("provider", "")),
                })
            self._send_json(200, {
                "symbol": SYMBOL,
                "bars": ohlcv_data,
                "count": len(ohlcv_data),
                "last_bar_timestamp": last_ts,
                "signal_count": len(engine.state.signal_history),
                "provider": engine.state.last_provider,
            })
            return

        if path == "/signals":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            limit = 50
            try:
                limit = int(self.headers.get("X-Limit", query.get("limit", "50")))
            except Exception:
                pass
            since = self.headers.get("X-Since", query.get("since", ""))
            all_signals = engine.state.signal_history
            if since:
                all_signals = [s for s in all_signals if s.get("timestamp", "") > since]
            signals = all_signals[-limit:]
            self._send_json(200, {
                "symbol": SYMBOL,
                "signals": signals,
                "count": len(signals),
                "last_signal_at": engine.state.last_signal_at,
            })
            return

        if path == "/fvg":
            self._send_json(200, {"fvgs": BRIDGE_STATE.list_fvgs()})
            return

        if path == "/probe":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            probe_data = engine.feed.probe()
            try:
                probe_data["signal_status"] = engine.get_signal_status()
                probe_data["relay_healthy"] = (engine.feed.failure_count() < 3)
            except Exception:
                pass
            self._send_json(200, probe_data)
            return

        if path == "/diagnostics":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                diag = engine.get_signal_status()
                diag["ohlcv_history_depth"] = len(engine.ohlcv_history)
                current_col = engine.state.Z - (engine.state.y + 1)
                if current_col < 0:
                    current_col = 0
                diag["indicator_col_index"] = [current_col, max(0, current_col - 1)]
                diag["indicator_sample_col0"] = [
                    str(engine.state.iA[i][current_col]) if current_col < len(engine.state.iA[i]) else "50"
                    for i in range(13)
                ]
                prev_col = max(0, current_col - 1)
                diag["indicator_sample_col1"] = [
                    str(engine.state.cA[i][prev_col]) if prev_col < len(engine.state.cA[i]) else "50"
                    for i in range(13)
                ]
                diag["x_period_constant"] = X_PERIOD
                diag["y_start_constant"] = Y_START
                diag["consecutive_zero_prices"] = engine._consecutive_zero_prices
                diag["relay_healthy"] = (engine.feed.failure_count() < 3)
                diag["active_symbol"] = engine.feed.active_symbol()
                diag["last_bar_close"] = engine.state.bar_close_count
                diag["recent_signals"] = engine.state.signal_history[-10:]
                diag["provider"] = engine.state.last_provider
                diag["projection_meta"] = engine.state.projection_meta
                diag["projection_trigger"] = engine.state.projection_trigger
                self._send_json(200, diag)
            except Exception as e:
                self._send_json(500, {"error": "diagnostics_failed", "detail": str(e)})
            return

        if path == "/orders":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            self._send_json(200, {"orders": engine.list_orders()})
            return

        if path == "/regime-map":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            self._send_json(200, {
                "regime_map": engine.get_regime_map(),
                "size": len(engine.state.Regime),
            })
            return

        if path == "/indicators":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            name = query.get("name", "RSI")
            try:
                count = int(query.get("count", "80"))
            except Exception:
                count = 80
            series = engine.get_indicator_series(name, count)
            self._send_json(200, {"name": name, "series": series, "count": len(series)})
            return

        if path == "/log":
            try:
                limit = int(query.get("limit", "50"))
            except Exception:
                limit = 50
            with _LOG_LOCK:
                logs = list(_LOG_BUFFER)[-limit:]
            self._send_json(200, {"logs": logs, "count": len(logs)})
            return

        if path == "/" or path == "/index.html":
            try:
                base = os.path.dirname(os.path.abspath(__file__))
                html_path = os.path.join(base, "index.html")
                if os.path.isfile(html_path):
                    with open(html_path, "r", encoding="utf-8") as f:
                        self._send_html(200, f.read())
                else:
                    self._send_html(200, "<!DOCTYPE html><html><body style='font-family:monospace;background:#050510;color:#aaccff;padding:40px;'><h2>⚡ ÆEA Mini App Bridge Online</h2><p>index.html not found in <code>" + base + "</code>.</p></body></html>")
            except Exception as e:
                self._send_json(500, {"error": "read_index_failed", "detail": str(e)})
            return

        
        if path in ("/cs-state", "/cs-feedback"):
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                fused = _build_fused_state(engine)
                self._send_json(200, {"cs": fused.get("cs"), "feedback": fused.get("cs_feedback"), "seed": fused.get("seed")})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        if path in ("/lattice-state", "/seed-state"):
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                seed = engine.seed.to_dict() if hasattr(engine, "seed") else {}
                self._send_json(200, {"lattice_points": seed.get("lattice_points"), "lattice_count": seed.get("lattice_count"), "s2": seed.get("s2"), "r2": seed.get("r2"), "deviation": seed.get("deviation"), "prime": seed.get("prime"), "tick": seed.get("tick"), "seed": seed})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        if path == "/fibration-state":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                seed = engine.seed.to_dict() if hasattr(engine, "seed") else {}
                self._send_json(200, {"phi": seed.get("phi"), "hopf": seed.get("hopf"), "hopf_base": seed.get("hopf"), "psi": seed.get("psi"), "s2": seed.get("s2"), "r2": seed.get("r2"), "deviation": seed.get("deviation")})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        if path == "/symbolic-state":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                seed = engine.seed.to_dict() if hasattr(engine, "seed") else {}
                self._send_json(200, {"prime": seed.get("prime"), "generation": seed.get("generation"), "I": seed.get("I"), "psi": seed.get("psi"), "phi": seed.get("phi"), "tick": seed.get("tick")})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        if path == "/observer-integral":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                fused = _build_fused_state(engine)
                self._send_json(200, fused.get("observer") or {})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        if path == "/evolution-state":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                fused = _build_fused_state(engine)
                self._send_json(200, fused.get("evolution") or {})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        if path == "/crawler-state":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                fused = _build_fused_state(engine)
                self._send_json(200, fused.get("crawler") or {})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        if path == "/aea-notification":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                cursor_raw = query.get("cursor")
                if cursor_raw is None:
                    fused = _build_fused_state(engine)
                    self._send_json(200, fused.get("aea_notification") or {})
                    return
                try:
                    cursor = int(cursor_raw)
                except (TypeError, ValueError):
                    self._send_json(400, {"error": "invalid_cursor", "detail": "cursor must be a bar index"})
                    return
                bars = engine.ohlcv_history or []
                if cursor < 0 or cursor >= len(bars):
                    self._send_json(400, {"error": "invalid_cursor", "detail": "cursor is outside the bar range"})
                    return
                bar = bars[cursor]
                fused = _build_fused_state(engine)
                seed_dict = fused.get("seed") or {}
                aeea = fused.get("aeea") or {}
                text = format_aea("state", {"seed": seed_dict, "aeea": aeea})
                text = text + (
                    f" \u00b7 cursor {cursor}/{len(bars)}"
                    f" \u00b7 O {bar.get('open')} H {bar.get('high')} L {bar.get('low')} C {bar.get('close')}"
                    f" \u00b7 {bar.get('timestamp')}"
                )
                self._send_json(200, {"text": text, "kind": "state", "cursor": cursor, "bar": bar, "tick": int(seed_dict.get("tick", 0))})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        self._send_json(404, {"error": "not_found", "path": path})

    def do_POST(self) -> None:
        path = urlparse(self.path).path

        if path == "/handshake":
            try:
                data = self._read_json()
                init_data = data.get("initData", "").strip()
                chat_id = data.get("chat_id")
                if not init_data:
                    self._send_json(400, {"error": "missing_init_data", "detail": "Provide initData from Telegram.WebApp.initData"})
                    return
                verified = verify_telegram_init_data(init_data, TELEGRAM_BOT_TOKEN_ENV)
                if not verified or not verified.get("user"):
                    logger.warning("🚫 Handshake rejected: initData verification failed")
                    self._send_json(403, {"error": "invalid_init_data", "detail": "Telegram initData HMAC verification failed. Ensure TELEGRAM_BOT_TOKEN matches the bot that issued initData."})
                    return
                u = verified["user"] or {}
                user_id = u.get("id")
                username = u.get("username")
                if _is_banned_user(user_id):
                    logger.warning(f"🚫 Handshake rejected: banned user_id={user_id}")
                    self._send_json(403, {"error": "banned_user", "detail": "This Telegram user ID is banned."})
                    return
                if not _is_allowed_user(user_id):
                    logger.warning(f"🚫 Handshake rejected: unauthorized user_id={user_id}")
                    self._send_json(403, {"error": "unauthorized_user", "detail": "This Mini App is private. Your Telegram user ID is not on the allowlist."})
                    return
                BRIDGE_STATE.register_webapp_session(user_id, username, chat_id=chat_id)
                logger.info(f"🤝 Handshake OK: user_id={user_id}, username={username}, chat_id={chat_id}")
                self._send_json(200, {
                    "ok": True, "user_id": user_id, "username": username,
                })
            except Exception as e:
                logger.error(f"Handshake error: {e}")
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return

        if not _require_auth(self):
            self._send_json(401, {"error": "unauthorized", "detail": "Missing or invalid X-Telegram-Init-Data"})
            return

        if path == "/fvg":
            user_id, username, verified = _extract_auth_headers(self)
            try:
                data = self._read_json()
                fvg_type = data.get("type")
                price_str = data.get("price")
                num = data.get("num")
                den = data.get("den")
                requested_idx = data.get("idx")
                if fvg_type is None:
                    self._send_json(400, {"error": "missing_fields", "need": ["type", "price"]})
                    return
                try:
                    requested_idx_int = int(requested_idx) if requested_idx is not None else None
                except (TypeError, ValueError):
                    requested_idx_int = None
                if num is not None and den is not None:
                    price_label = f"{int(num)}/{int(den)}"
                    price_dec = Decimal(int(num)) / Decimal(int(den))
                elif price_str is not None:
                    price_label = str(price_str)
                    price_dec = Decimal(str(price_str))
                else:
                    self._send_json(400, {"error": "missing_fields", "need": ["type", "price"]})
                    return
                idx = BRIDGE_STATE.add_fvg(fvg_type, str(price_dec), user_id=user_id, requested_idx=requested_idx_int)
                anchor_info = {}
                engine = BRIDGE_ENGINE_REF.get("engine")
                if engine is not None and idx in engine.state.fvg_anchor_map:
                    anchor_info = engine.state.fvg_anchor_map[idx]
                logger.info(f"📐 FVG committed: type={fvg_type} price={price_label} idx={idx} verified={verified} user={username}")
                self._send_json(201, {"ok": True, "idx": idx, "type": fvg_type, "price": price_label, "verified": verified, "anchor": anchor_info})
            except ValueError as ve:
                logger.warning(f"FVG rejected: {ve}")
                self._send_json(422, {"error": "validation", "detail": str(ve)})
            except Exception as e:
                logger.error(f"FVG POST error: {e}")
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return

        if path == "/reset":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                engine.feed._rebuild_ticker()
                engine.feed._fallback_count = 0
                engine._consecutive_zero_prices = 0
                engine.OnReInit()
                engine._project_arc_length(trigger="manual_refresh")
                logger.info("🔄 Manual reset requested via /reset")
                self._send_json(200, {"ok": True, "active_symbol": engine.feed.active_symbol()})
            except Exception as e:
                logger.error(f"/reset error: {e}")
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return

        if path == "/settings":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            data = self._read_json()
            result = engine.apply_settings(data)
            code = 200 if result.get("ok") else (422 if result.get("error") == "validation" else 400)
            self._send_json(code, result)
            return

        if path == "/symbol":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            data = self._read_json()
            sym = data.get("symbol")
            if not sym:
                self._send_json(400, {"error": "missing_symbol", "detail": "Provide 'symbol' in JSON body"})
                return
            result = engine.change_symbol(sym)
            code = 200 if result.get("ok") else 400
            self._send_json(code, result)
            return

        if path == "/order":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            data = self._read_json()
            side = (data.get("side") or "").upper()
            try:
                _vol = data.get("volume", data.get("lot", "0.01"))
                _sl = data.get("sl", "0")
                _tp = data.get("tp", "0")
                if _vol is None: _vol = "0.01"
                if _sl is None: _sl = "0"
                if _tp is None: _tp = "0"
                lot = Fraction.from_decimal_string(str(_vol)).to_decimal()
                sl = Fraction.from_decimal_string(str(_sl)).to_decimal()
                tp = Fraction.from_decimal_string(str(_tp)).to_decimal()
            except Exception as e:
                self._send_json(400, {"error": "invalid_numbers", "detail": str(e)})
                return
            result = engine.place_order(side, lot, sl, tp)
            code = 200 if result.get("ok") else 400
            self._send_json(code, result)
            return

        if path == "/order/close":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            data = self._read_json()
            if data.get("all"):
                result = engine.close_order(all=True)
            else:
                ticket = data.get("ticket")
                if ticket is None:
                    self._send_json(400, {"error": "missing_ticket"})
                    return
                try:
                    ticket = int(ticket)
                except Exception:
                    self._send_json(400, {"error": "invalid_ticket"})
                    return
                result = engine.close_order(ticket=ticket)
            code = 200 if result.get("ok") else 400
            self._send_json(code, result)
            return

        if path == "/projection/refresh":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                engine._project_arc_length(trigger="manual_refresh")
                self._send_json(200, engine.get_projection())
            except Exception as e:
                logger.error(f"/projection/refresh error: {e}")
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return

        
        if path == "/step":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                seed = engine.seed.to_dict() if hasattr(engine, "seed") else {}
                feed_ordered = int(getattr(getattr(engine, "ordered_feed", None), "feed_ordered", 0))
                self._send_json(200, {"ok": True, "seed": seed, "ordered": feed_ordered, "x": seed.get("last_x"), "note": "Seed advances on each ordered tick via _on_tick_locked. POST /step returns current seed. Client x is ignored. Frontend sends {}."})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        if path == "/teach":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                data = self._read_json()
                entry = engine.cs_feedback.add({"kind": "teach", "text": str(data.get("text", ""))[:2000], "user": str(data.get("user", ""))[:200]}) if hasattr(engine, "cs_feedback") else {}
                self._send_json(200, {"ok": True, "entry": entry})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        if path == "/say":
            try:
                data = self._read_json()
                text = str(data.get("text", ""))[:2000]
                self._send_json(200, {"ok": True, "text": text, "say": _cs_translate(text)})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        if path == "/cs-feedback":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                data = self._read_json()
                entry = engine.cs_feedback.add({"kind": str(data.get("kind", "feedback"))[:100], "text": str(data.get("text", ""))[:2000], "user": str(data.get("user", ""))[:200]}) if hasattr(engine, "cs_feedback") else {}
                self._send_json(200, {"ok": True, "entry": entry})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        if path == "/encode-syllable":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                data = self._read_json()
                syl = str(data.get("syllable", "")).strip().upper()
                seed = engine.seed.to_dict() if hasattr(engine, "seed") else {}
                _coh = bool(seed.get("coherent"))
                _arc_check = "s = r" if _coh else "s != r"
                if syl == "A":
                    enc = {"syllable": "A", "value": seed.get("s2"), "label": "arc", "arc_sq": seed.get("s2"), "radius_sq": seed.get("r2"), "deviation_sq": seed.get("deviation"), "coherence": _coh, "arc_check": _arc_check}
                elif syl == "U":
                    enc = {"syllable": "U", "value": seed.get("r2"), "label": "radius", "arc_sq": seed.get("s2"), "radius_sq": seed.get("r2"), "deviation_sq": seed.get("deviation"), "coherence": _coh, "arc_check": _arc_check}
                elif syl == "M":
                    enc = {"syllable": "M", "value": seed.get("deviation"), "label": "deviation", "arc_sq": seed.get("s2"), "radius_sq": seed.get("r2"), "deviation_sq": seed.get("deviation"), "coherence": _coh, "arc_check": _arc_check}
                elif syl == "AUM":
                    enc = {"syllable": "AUM", "values": [seed.get("s2"), seed.get("r2"), seed.get("deviation")], "label": "arc-radius-deviation", "arc_sq": seed.get("s2"), "radius_sq": seed.get("r2"), "deviation_sq": seed.get("deviation"), "coherence": _coh, "arc_check": _arc_check}
                else:
                    self._send_json(400, {"error": "unknown_syllable", "need": ["A", "U", "M", "AUM"]})
                    return
                self._send_json(200, {"ok": True, "encoding": enc})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        if path == "/crawler-enqueue":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                data = self._read_json()
                url = str(data.get("url", ""))
                res = engine.crawler.enqueue(url) if hasattr(engine, "crawler") else {"ok": False, "error": "no_crawler"}
                # Fetch-and-hash the enqueued URL (text only).
                # If fetch fails, last_hash_frac stays as-is and seed falls back to labelled price-x.
                try:
                    if isinstance(res, dict) and res.get("ok") and hasattr(engine.crawler, "fetch_and_hash"):
                        _fh = engine.crawler.fetch_and_hash(url)
                        res = {**res, "hash": _fh}
                except Exception:
                    pass
                self._send_json(200, res)
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        if path == "/notify-aea":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                data = self._read_json()
                kind = str(data.get("kind", "state"))
                payload = data.get("payload") or {}
                if kind == "state":
                    fused = _build_fused_state(engine)
                    text = format_aea("state", {"seed": fused.get("seed"), "aeea": {"regime": fused.get("aeea", {}).get("regime"), "m": fused.get("aeea", {}).get("m"), "n": fused.get("aeea", {}).get("n")}})
                    self._send_json(200, {"ok": True, "notification": {"text": text, "kind": "state"}})
                else:
                    text = format_aea(kind, payload)
                    self._send_json(200, {"ok": True, "notification": {"text": text, "kind": kind}})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        self._send_json(404, {"error": "not_found", "path": path})

    def do_DELETE(self) -> None:
        path = urlparse(self.path).path
        if not _require_auth(self):
            self._send_json(401, {"error": "unauthorized", "detail": "Missing or invalid X-Telegram-Init-Data"})
            return
        m = _re_bridge.match(r"^/fvg/(\d+)$", path)
        if m:
            idx = int(m.group(1))
            ok = BRIDGE_STATE.remove_fvg(idx)
            if ok:
                logger.info(f"🔻 FVG removed: idx={idx}")
                self._send_json(200, {"ok": True, "idx": idx})
            else:
                self._send_json(404, {"error": "fvg_not_found", "idx": idx})
            return
        
        if path == "/orders":
            engine = BRIDGE_ENGINE_REF.get("engine")
            if engine is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            try:
                closed = engine.close_order(all=True)
                self._send_json(200, {"ok": True, "closed": closed})
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return
        self._send_json(404, {"error": "not_found", "path": path})

# ============================================================================
# BRIDGE SERVER
# ============================================================================
class BridgeServer:
    def __init__(self, host: str = BRIDGE_HOST, port: int = BRIDGE_PORT):
        self.host = host
        self.port = int(port)
        self._httpd: Optional[ThreadingHTTPServer] = None
        self._thread: Optional[threading.Thread] = None
        self._tunnel: Optional[TunnelManager] = None
        self._ssl_context: Optional[ssl.SSLContext] = None

    def _build_ssl_context(self) -> Optional[ssl.SSLContext]:
        if not BRIDGE_USE_TLS:
            return None
        if not BRIDGE_TLS_CERT or not BRIDGE_TLS_KEY:
            logger.warning("⚠️ BRIDGE_USE_TLS=1 but cert/key paths missing — falling back to HTTP")
            return None
        if not (os.path.isfile(BRIDGE_TLS_CERT) and os.path.isfile(BRIDGE_TLS_KEY)):
            logger.warning("⚠️ TLS cert or key file not found — falling back to HTTP")
            return None
        try:
            ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            ctx.load_cert_chain(certfile=BRIDGE_TLS_CERT, keyfile=BRIDGE_TLS_KEY)
            logger.info(f"🔒 TLS enabled: cert={BRIDGE_TLS_CERT}")
            return ctx
        except Exception as e:
            logger.error(f"❌ Failed to load TLS context: {e}")
            return None

    def start(self) -> None:
        if self._thread is not None:
            return
        try:
            self._httpd = ThreadingHTTPServer((self.host, self.port), BridgeHandler)
            self._httpd.daemon_threads = True
            self._ssl_context = self._build_ssl_context()
            if self._ssl_context is not None:
                self._httpd.socket = self._ssl_context.wrap_socket(self._httpd.socket, server_side=True)
        except OSError as e:
            logger.error(f"🔥 Bridge server bind failed on {self.host}:{self.port}: {e}")
            return
        self._thread = threading.Thread(target=self._httpd.serve_forever, name="aei-bridge", daemon=True)
        self._thread.start()
        scheme = "https" if self._ssl_context else "http"
        logger.info(f"🌐 ÆEA Mini App Bridge listening on {scheme}://{self.host}:{self.port}")
        self._tunnel = TunnelManager(self.port, prefer=BRIDGE_TUNNEL, timeout=BRIDGE_PUBLIC_TIMEOUT)
        threading.Thread(target=self._tunnel.start, name="aei-tunnel", daemon=True).start()

    def stop(self) -> None:
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
            self._thread.join(timeout=2.0)
            self._thread = None
        logger.info("🌐 ÆEA Mini App Bridge stopped")

# ============================================================================
# BRIDGE ATTACHMENT
# ============================================================================
def _bridge_attach_to_engine(engine: "AEEA_Engine") -> None:
    if getattr(engine, "_bridge_attached", False):
        return
    engine._bridge_attached = True
    logger.info("🔗 Bridge attached to AEEA_Engine")

def _bridge_attach_to_bot(bot: "AEI_Bot") -> None:
    if getattr(bot, "_bridge_attached", False):
        return
    original_run = bot.run
    def wrapped_run(self):
        BRIDGE_ENGINE_REF["engine"] = self.engine
        BRIDGE_ENGINE_REF["bot"] = self
        _bridge_attach_to_engine(self.engine)
        server = BridgeServer()
        server.start()
        self._bridge_server = server
        try:
            original_run(self)
        finally:
            server.stop()
    bot.run = wrapped_run
    bot._bridge_attached = True
    logger.info("🔗 Bridge attached to AEI_Bot.run()")

# ============================================================================
# TELEGRAM BOT
# ============================================================================
class AEI_Bot:
    def __init__(self, token: str, bot_name: str = "UpscaleTradeBot"):
        self.token = token
        self.bot_name = bot_name
        self.engine = AEEA_Engine()
        self.application = None
        self._running = False
        self._price_task: Optional[asyncio.Task] = None
        self._bridge_server: Optional[BridgeServer] = None
        self._webapp_url: Optional[str] = None
        self._loop: Optional[asyncio.AbstractEventLoop] = None

    def _resolve_webapp_url(self) -> Optional[str]:
        return TELEGRAM_WEBAPP_URL or BRIDGE_ENGINE_REF.get("public_url")

    def _track_inbound_message(self, update: Update) -> None:
        try:
            msg = update.effective_message
            chat = update.effective_chat
            user = update.effective_user
            user_id = None
            if user is not None and getattr(user, "id", None) is not None:
                user_id = int(user.id)
            if user_id is not None and _is_banned_user(user_id):
                logger.info(f"🚫 Blocked Telegram update from banned user_id={user_id}")
                raise PermissionError("banned_user")
            if user_id is not None and not _is_allowed_user(user_id):
                logger.info(f"🚫 Blocked Telegram update from unauthorized user_id={user_id}")
                raise PermissionError("private_bot_unauthorized_user")
            chat_id = None
            if chat is not None and getattr(chat, "id", None) is not None:
                chat_id = int(chat.id)
            if chat_id is not None:
                if self.engine.state.chat_id != chat_id:
                    self.engine.state.last_inbound_message_id = None
                self.engine.state.chat_id = chat_id
            if msg is not None and getattr(msg, "message_id", None) is not None:
                self.engine.state.last_inbound_message_id = int(msg.message_id)
        except PermissionError:
            raise
        except Exception as e:
            logger.debug(f"_track_inbound_message failed: {e}")

    def _send_message_sync(self, chat_id: int, text: str, parse_mode: str = "Markdown",
                           reply_to_message_id: Optional[int] = None,
                           timeout: float = 10.0) -> bool:
        if self.application is None:
            logger.warning("📡 send_message skipped: application is None")
            return False
        loop = self._loop
        if loop is None or loop.is_closed():
            logger.warning("📡 send_message skipped: event loop not captured or closed")
            return False
        bot = self.application.bot

        def _attempt(pm: Optional[str], rt: Optional[int]) -> Tuple[bool, str]:
            coro = bot.send_message(
                chat_id=chat_id,
                text=text,
                parse_mode=pm,
                reply_to_message_id=rt,
            )
            try:
                fut = asyncio.run_coroutine_threadsafe(coro, loop)
                fut.result(timeout=timeout)
                return (True, "")
            except asyncio.TimeoutError:
                return (False, "timeout")
            except Exception as e:
                return (False, str(e))

        ok1, err1 = _attempt(parse_mode, reply_to_message_id)
        if ok1:
            return True
        logger.info(f"📡 send_message attempt 1 failed (reply+Markdown): {err1}")

        reply_class = _looks_like_reply_error(err1)
        parse_class = _looks_like_parse_error(err1)
        length_class = _looks_like_length_error(err1)

        if reply_class and not parse_class:
            ok2, err2 = _attempt(parse_mode, None)
            if ok2:
                logger.info("📡 send_message attempt 2 succeeded (standalone Markdown)")
                return True
            logger.info(f"📡 send_message attempt 2 failed (standalone Markdown): {err2}")
            if _looks_like_parse_error(err2):
                ok3, err3 = _attempt(None, None)
                if ok3:
                    logger.info("📡 send_message attempt 3 succeeded (plain text)")
                    return True
                logger.warning(f"📡 send_message attempt 3 failed (plain text): {err3}")
                return False
            ok3, err3 = _attempt(None, None)
            if ok3:
                logger.info("📡 send_message attempt 3 succeeded (plain text)")
                return True
            logger.warning(f"📡 send_message attempt 3 failed (plain text): {err3}")
            return False

        if parse_class and not reply_class:
            # : return immediately on the threaded-plain success path.
            ok3, err3 = _attempt(None, reply_to_message_id)
            if ok3:
                logger.info("📡 send_message attempt 3 succeeded (plain text, threaded)")
                return True
            if _looks_like_reply_error(err3):
                ok3b, err3b = _attempt(None, None)
                if ok3b:
                    logger.info("📡 send_message attempt 3b succeeded (plain text, standalone)")
                    return True
                logger.warning(f"📡 send_message attempt 3b failed (plain text): {err3b}")
                return False
            ok3b, err3b = _attempt(None, None)
            if ok3b:
                logger.info("📡 send_message attempt 3b succeeded (plain text, standalone)")
                return True
            logger.warning(f"📡 send_message attempt 3b failed (plain text): {err3b}")
            return False

        if reply_class and parse_class:
            ok2, err2 = _attempt(None, None)
            if ok2:
                logger.info("📡 send_message attempt 2 succeeded (plain text, standalone)")
                return True
            logger.warning(f"📡 send_message attempt 2 failed (plain text, standalone): {err2}")
            return False

        ok2, err2 = _attempt(parse_mode, None)
        if ok2:
            logger.info("📡 send_message attempt 2 succeeded (standalone Markdown, unknown class)")
            return True
        ok3, err3 = _attempt(None, None)
        if ok3:
            logger.info("📡 send_message attempt 3 succeeded (plain text, unknown class)")
            return True
        logger.warning(f"📡 send_message failed all attempts: reply_err={err1} standalone_err={err2} plain_err={err3}")
        return False

    async def price_feed_loop(self):
        logger.info("🔄 Price feed loop entered")
        iteration = 0
        while self._running:
            iteration += 1
            try:
                self.engine.update_price_from_feed()
                st = self.engine.state
                if st.chat_id is not None and (_is_banned_user(st.chat_id) or not _is_allowed_user(st.chat_id)):
                    # The bound chat is not on the allowlist. This should
                    # never happen if the gate is enforced everywhere, but
                    # defend against a stale chat_id left over from a
                    # pre-gate session.
                    logger.warning(f"⚠️ Price feed bound to unauthorized chat_id={st.chat_id}; clearing binding.")
                    st.chat_id = None
                    st.last_inbound_message_id = None
                idx = st.Z - (st.y + 1)
                regime = st.Regime[idx] if 0 <= idx < len(st.Regime) else "Unknown"
                logger.info(f"📊 itr#{iteration} price={st.price} vol={st.last_volume} provider={st.last_provider} tick={st.tick} FG={st.FG} regime={regime} bars={st.bar_close_count} signals={len(st.signal_history)} ohlcv={len(self.engine.ohlcv_history)}")
            except Exception:
                logger.exception(f"❌ Feed iteration #{iteration} failed")
            await asyncio.sleep(UPDATE_INTERVAL)
        logger.info("🔄 Price feed loop exited")

    def _build_main_keyboard(self) -> InlineKeyboardMarkup:
        webapp_url = self._resolve_webapp_url()
        rows = [
            [InlineKeyboardButton("📊 Status", callback_data="status"), InlineKeyboardButton("📈 Signal", callback_data="signal")],
            [InlineKeyboardButton("📊 Regime", callback_data="regime"), InlineKeyboardButton("📉 Indicators", callback_data="indicators")],
            [InlineKeyboardButton("🔄 Start Feed", callback_data="start_feed"), InlineKeyboardButton("⏹️ Stop Feed", callback_data="stop_feed")],
            [InlineKeyboardButton("📈 Info", callback_data="info"), InlineKeyboardButton("🔄 Reset", callback_data="reset")],
            [InlineKeyboardButton("🔬 Probe Relay", callback_data="probe"), InlineKeyboardButton("♻️ Rebuild Relay", callback_data="rebuild_yf")],
            [InlineKeyboardButton("🔬 Diagnostics", callback_data="diagnostics")],
            [InlineKeyboardButton("📊 Chart", callback_data="chart"), InlineKeyboardButton("🎯 Projection", callback_data="projection")],
        ]
        if webapp_url:
            rows.append([InlineKeyboardButton("⚡ Open ÆEA Mini App", web_app=WebAppInfo(url=webapp_url))])
        else:
            rows.append([InlineKeyboardButton("⏳ Mini App (tunnel pending…)", callback_data="webapp_pending")])
        return InlineKeyboardMarkup(rows)

    async def _safe_reply(self, update: Update, text: str, reply_markup=None) -> bool:
        msg = update.effective_message
        query = update.callback_query
        target = query if query is not None else msg
        if target is None:
            logger.warning("_safe_reply: no target message or callback_query")
            return False

        try:
            if query is not None:
                await query.edit_message_text(text, parse_mode="Markdown", reply_markup=reply_markup)
            else:
                await msg.reply_text(text, parse_mode="Markdown", reply_markup=reply_markup)
            return True
        except Exception as e1:
            err1 = str(e1)
            logger.info(f"_safe_reply attempt 1 failed (Markdown): {err1}")

        try:
            if query is not None:
                await query.edit_message_text(text, parse_mode=None, reply_markup=reply_markup)
            else:
                await msg.reply_text(text, parse_mode=None, reply_markup=reply_markup)
            logger.info("_safe_reply attempt 2 succeeded (plain text)")
            return True
        except Exception as e2:
            err2 = str(e2)
            logger.info(f"_safe_reply attempt 2 failed (plain text): {err2}")

        try:
            truncated = text[:3900] if len(text) > 3900 else text
            if query is not None:
                await query.edit_message_text(truncated, parse_mode=None, reply_markup=reply_markup)
            else:
                await msg.reply_text(truncated, parse_mode=None, reply_markup=reply_markup)
            logger.info("_safe_reply attempt 3 succeeded (truncated plain text)")
            return True
        except Exception as e3:
            err3 = str(e3)
            logger.error(f"_safe_reply attempt 3 failed (truncated plain text): {err3}")
            return False

    async def start(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        chat_id = update.effective_chat.id
        self.engine.state.chat_id = chat_id
        self.engine.application = self.application
        engine_status = "𝒜₃ Initialized" if self.engine.state.FG else "𝒜₄ Waiting for data"
        feed_status = _cs("Active") if self._running else _cs("Inactive")
        welcome = (
            "🔷 *ÆEA Quantum-Financial Topology Bot*\n"
            "Welcome to @UpscaleTradeBot. This bot implements the Non-Hermitian\n"
            "Stochastic Geometry of Supply-Demand Imbalance.\n\n"
            "📊 *Available Commands:*\n"
            "`/status` - Current market state & regime\n"
            "`/regime` - Detailed regime classification\n"
            "`/signal` - Current trading signal\n"
            "`/indicators` - 13D Hilbert Space projection\n"
            "`/fvg` - Fair Value Gap tracking\n"
            "`/chart` - Recent signals summary\n"
            "`/projection` - Arc-length future price projection\n"
            "`/diagnostics` - Full engine diagnostic snapshot\n"
            "`/reset` - Reset topological branch\n"
            "`/start_feed` - Start price feed\n"
            "`/stop_feed` - Stop price feed\n"
            "`/symbol <PAIR>` - Change trading symbol\n"
            "`/info` - Ticker information\n"
            "`/probe` - Relay diagnostics\n"
            "`/rebuild_yf` - Force relay reset\n"
            "`/webapp` - Launch Telegram Mini App\n"
            "`/webgui` - Show bridge URL\n"
            "`/whoami` - Show your Telegram user ID\n"
            "`/help` - Show this message\n\n"
            f"*Current Symbol:* `{SYMBOL}`\n"
            f"🔄 *Feed Status:* {feed_status}\n"
            f"🧠 *Engine Status:* {engine_status}\n"
            f"📊 *Bar Closes:* {self.engine.state.bar_close_count}  |  *Signals:* {len(self.engine.state.signal_history)}\n"
            f"📡 *Provider:* `{self.engine.state.last_provider or '—'}`  |  *Volume:* `{self.engine.state.last_volume}`\n"
            "💎 Natalia Tanyatia"
        )
        await self._safe_reply(update, welcome, reply_markup=self._build_main_keyboard())

    async def help(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        await self.start(update, context)

    async def status(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        if not self.engine.state.FG:
            logger.info("⚠️ Engine not initialized, attempting to force...")
            self.engine._force_initialization()
        if not self.engine.state.FG:
            await self._safe_reply(update,
                "⏳ *Engine not initialized*\nThe engine will initialize on the first price tick after starting the feed.\nPlease use `/start_feed` to start the price feed.\nIf the feed is already running, try `/reset` to reinitialize.")
            return
        state = self.engine.state
        idx = state.Z - (state.y + 1)
        regime = state.Regime[idx] if 0 <= idx < len(state.Regime) and state.Regime[idx] else "Unknown"
        bid, ask = self.engine.feed.get_current_price()
        price_display = f"{bid:.5f}" if bid > Decimal('0.0') else f"{state.price:.5f}"
        feed_mark = "✅" if self._running else "⏹️"
        init_mark = "✅ 𝒜₃" if state.FG else "⏳ 𝒜₄"
        m_local = state.authoritative_m
        n_local = state.authoritative_n
        h_idx = state.h - (state.y + 1)
        m_at_h = 1 if (0 <= h_idx < len(state.k) and state.k[h_idx]) else 0
        n_at_h = 1 if (0 <= h_idx < len(state.l) and state.l[h_idx]) else 0
        trail_status = "𝒜₃" if state.trailing_stop_active else "𝒜₄"
        order_presence = []
        if state.has_open_long:
            order_presence.append(f"↑({state.lOrder_id})")
        if state.has_open_short:
            order_presence.append(f"↓({state.kOrder_id})")
        order_str = ", ".join(order_presence) if order_presence else "𝒩"
        response = (
            "🔷 *ÆEA 𝒮_Status*\n"
            f"📈 *Symbol:* {SYMBOL}\n"
            f"💰 *Price:* {price_display}\n"
            f"📊 *ℛ_regime:* {regime}\n"
            f"🎯 *𝒮_Signal_Level:* {state.signal:.5f}\n"
            f"📋 *𝒮:* {'Active' if state.signature else 'Idle'}\n"
            f"🔄 *Tick:* {state.tick}\n"
            f"🧠 *Engine State:* {init_mark}\n"
            f"⚖️ *Imbalance @ h={state.h}:* m={m_at_h}, n={n_at_h}\n"
            f"⚖️ *Local m/n:* {m_local}/{n_local}\n"
            f"📈 *Indicator Passes:* {self.engine._indicator_populate_count}\n"
            f"📡 *Signal Fires:* {self.engine._imbalance_fire_count}\n"
            f"📊 *Bar Closes:* {state.bar_close_count}\n"
            f"📈 *OHLCV Bars:* {len(self.engine.ohlcv_history)}\n"
            f"🎯 *Signal History:* {len(state.signal_history)}\n"
            f"📡 *Feed Active:* {feed_mark}\n"
            f"🛰️ *Provider:* `{state.last_provider or '—'}`  |  *Volume:* `{state.last_volume}`\n"
            f"🔀 *𝒦:* {_cs(state.KC)}  |  *π:* {state.prime}  |  *δ_dime:* {state.dime}\n"
            f"🔀 *𝒦_invert:* {_cs(state.invert)}  |  *μ:* {state.mem}  |  *τ:* {state.tag}\n"
            f"🔀 *𝒜:* {_cs(state.A)}  |  *ℬ:* {_cs(state.B)}  |  *𝒞:* {_cs(state.C)}  |  *𝒸:* {_cs(state.c)}\n"
            f"🔀 *𝒯_tick_tock:* {_cs(state.tick_tock)}  |  *𝒮_safety:* {_cs(state.safety)}\n"
            f"📊 *𝒪:* {order_str}\n"
            f"🛑 *𝒯_trail:* {trail_status} ({state.trailing_stop_price:.5f} / {state.trailing_take_profit:.5f})\n"
            f"🎯 *𝒯_side:* {_cs(state.trailing_stop_side) if state.trailing_stop_side else '—'}  |  *Entry:* {state.trailing_stop_entry:.5f}\n"
            f"🔍 *𝒯_track Runs:* {state.on_track_runs}  |  *𝒯_stand Runs:* {state.on_stand_runs}\n"
            f"🎯 *Last δ_bar:* {self.engine._last_kronecker_bar}\n"
            f"🔢 *𝒳_scan:* {state.X_scan}  |  *𝒴_scan:* {state.Y_scan}  |  *𝒳_PERIOD:* {X_PERIOD}\n"
            f"🌌 *𝒫_arc:* {state.projection_meta.get('kind', '—') if state.projection_meta else '—'} @ {state.projection_computed_at or 'never'} (𝒫_trigger={state.projection_trigger or '—'})\n"
            f"💬 *ℳ_last:* {state.last_inbound_message_id}"
        )
        reply_markup = self._build_main_keyboard()
        await self._safe_reply(update, response, reply_markup=reply_markup)

    async def diagnostics(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        status = self.engine.get_signal_status()
        response = (
            "🔬 *Engine Diagnostics*\n"
            f"🔄 *Tick:* {status.get('tick')}\n"
            f"🧮 *Indicator Populates:* {status.get('indicator_populate_count')}\n"
            f"📡 *Signal Fires:* {status.get('imbalance_fire_count')}\n"
            f"📊 *Bar Closes:* {status.get('bar_close_count')}\n"
            f"📈 *OHLCV History:* {len(self.engine.ohlcv_history)}\n"
            f"🎯 *Signal History:* {status.get('signal_count')}\n"
            f"⚖️ *Local m / n:* {status.get('m_count')} / {status.get('n_count')}\n"
            f"⚖️ *m / n (@h={status.get('h_bar')}):* {status.get('m_at_h')} / {status.get('n_at_h')}\n"
            f"🎯 *Signal:* {status.get('signal'):.5f}\n"
            f"📊 *ℛ_regime:* {status.get('regime')}\n"
            f"🔀 *𝒦:* {_cs(status.get('KC'))}  |  *π:* {status.get('prime')}  |  *δ_dime:* {status.get('dime')}\n"
            f"🔀 *𝒦_invert:* {_cs(status.get('invert'))}  |  *μ:* {status.get('mem')}  |  *τ:* {status.get('tag')}\n"
            f"🔀 *𝒜:* {_cs(status.get('A'))}  |  *ℬ:* {_cs(status.get('B'))}  |  *𝒞:* {_cs(status.get('C'))}  |  *𝒸:* {_cs(status.get('c'))}\n"
            f"🔀 *𝒯_tick_tock:* {_cs(status.get('tick_tock'))}  |  *𝒮:* {_cs(status.get('signature'))}  |  *𝒮_safety:* {_cs(status.get('safety'))}\n"
            f"📈 *𝒯_trail Active:* {_cs(status.get('trailing_stop_active'))}\n"
            f"📈 *𝒯_trail Price:* {status.get('trailing_stop_price')}\n"
            f"📈 *𝒯_trail Take Profit:* {status.get('trailing_take_profit')}\n"
            f"📍 *𝒯_trail Entry:* {status.get('trailing_stop_entry')}  |  *Side:* {_cs(status.get('trailing_stop_side'))}\n"
            f"📊 *Has Long:* {_cs(status.get('has_open_long'))}  |  *Has Short:* {_cs(status.get('has_open_short'))}\n"
            f"📊 *lOrder_id:* {status.get('lOrder_id')}  |  *kOrder_id:* {status.get('kOrder_id')}\n"
            f"🔍 *𝒯_track Runs:* {status.get('on_track_runs')}  |  *𝒯_stand Runs:* {status.get('on_stand_runs')}\n"
            f"🎯 *Last δ_bar:* {status.get('last_kronecker_bar')}\n"
            f"🔢 *Authoritative m/n/h:* {status.get('authoritative_m')}/{status.get('authoritative_n')}/{status.get('authoritative_h')}\n"
            f"🔢 *Last δ m/n/h:* {status.get('last_kronecker_m')}/{status.get('last_kronecker_n')}/{status.get('last_kronecker_h')}\n"
            f"🔢 *Derivatives 𝒵/𝒵'/𝒪/𝒪'/𝒲/𝒲':* {status.get('Z')}/{status.get('z')}/{status.get('O')}/{status.get('o')}/{status.get('W')}/{status.get('w')}\n"
            f"🔢 *Derivatives ℐ/ℐ'/𝒥/𝒥':* {status.get('I')}/{status.get('iI')}/{status.get('J')}/{status.get('iJ')}\n"
            f"🔢 *Derivatives ℐ𝒵/ℐ𝒵'/ℐ𝒲/ℐ𝒲'/ℐ𝒪/ℐ𝒪':* {status.get('iZ')}/{status.get('iz')}/{status.get('iW')}/{status.get('iw')}/{status.get('iO')}/{status.get('io')}\n"
            f"🔢 *Scan 𝒮/𝒯/𝒓/ℐ𝒓:* {status.get('S')}/{status.get('T')}/{status.get('r')}/{status.get('ir')}\n"
            f"🔢 *𝒳_scan/𝒴_scan:* {status.get('X_scan')}/{status.get('Y_scan')}\n"
            f"🔢 *𝒳_PERIOD (const):* {X_PERIOD}  |  *𝒴_START (const):* {Y_START}\n"
            f"🔢 *𝒜_ATR/𝒜_StdDev/𝒜_IHKk/𝒜_IHKt:* {status.get('iATR'):.2f}/{status.get('iStdDev'):.2f}/{status.get('iIHKk'):.2f}/{status.get('iIHKt'):.2f}\n"
            f"🔢 *lPass/ilPass/kPass/ikPass:* {status.get('lPass')}/{status.get('ilPass')}/{status.get('kPass')}/{status.get('ikPass')}\n"
            f"🛰️ *Provider:* {status.get('last_provider')}  |  *Volume:* {status.get('last_volume')}\n"
            f"🌌 *𝒫_arc Computed:* {status.get('projection_computed_at')}\n"
            f"🌌 *𝒫_trigger:* {status.get('projection_trigger')}\n"
            f"💬 *ℳ_last:* {status.get('last_inbound_message_id')}"
        )
        await self._safe_reply(update, response)

    async def regime(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        if not self.engine.state.FG:
            self.engine._force_initialization()
        if not self.engine.state.FG:
            await self._safe_reply(update, "⏳ *Engine not initialized*\nPlease use `/start_feed`.")
            return
        state = self.engine.state
        y = state.y
        idx = state.Z - y - 1
        current = state.Regime[idx] if 0 <= idx < len(state.Regime) and state.Regime[idx] else "Unknown"
        premium = state.Premium[idx] if 0 <= idx < len(state.Premium) else Decimal('0.0')
        discount = state.Discount[idx] if 0 <= idx < len(state.Discount) else Decimal('0.0')
        hh = state.HH[idx] if 0 <= idx < len(state.HH) else Decimal('0.0')
        ll = state.LL[idx] if 0 <= idx < len(state.LL) else Decimal('0.0')
        m_local = state.authoritative_m
        n_local = state.authoritative_n
        imbalance_status = "✅ 𝒜₃" if (m_local >= 12 or n_local >= 12) else "⏳ 𝒜₄"
        response = (
            "📊 *ℛ_regime Classification*\n"
            f"🔹 *Current ℛ_regime:* {current}\n"
            f"🔹 *Π^{{>θ}}:* {premium:.5f}\n"
            f"🔸 *Π^{{<θ}}:* {discount:.5f}\n"
            f"📈 *HH:* {hh:.5f}\n"
            f"📉 *LL:* {ll:.5f}\n"
            f"🟢 *Local m:* {m_local}\n"
            f"🔴 *Local n:* {n_local}\n"
            f"⚖️ *Imbalance Condition:* {imbalance_status}"
        )
        reply_markup = self._build_main_keyboard()
        await self._safe_reply(update, response, reply_markup=reply_markup)

    async def signal(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        if not self.engine.state.FG:
            self.engine._force_initialization()
        if not self.engine.state.FG:
            await self._safe_reply(update, "⏳ *Engine not initialized*\nPlease use `/start_feed`.")
            return
        state = self.engine.state
        if state.signal == Decimal('0.0'):
            direction = "⊙"
            confidence = "N/A"
        elif state.price > state.signal:
            direction = "↟"
            confidence = f"{((state.price - state.signal) / state.signal * Decimal('100')):.2f}%" if state.signal != Decimal('0.0') else "0%"
        else:
            direction = "↡"
            confidence = f"{((state.signal - state.price) / state.signal * Decimal('100')):.2f}%" if state.signal != Decimal('0.0') else "0%"
        m_local = state.authoritative_m
        n_local = state.authoritative_n
        h_idx = state.h - (state.y + 1)
        m_at_h = 1 if (0 <= h_idx < len(state.k) and state.k[h_idx]) else 0
        n_at_h = 1 if (0 <= h_idx < len(state.l) and state.l[h_idx]) else 0
        condition_met = (m_local >= 12) or (n_local >= 12)
        condition_mark = "✅ 𝒜₃" if condition_met else "❌ 𝒜₄"
        response = (
            "🎯 *Trading Signal*\n"
            f"📊 *𝒮_Direction:* {direction}\n"
            f"📈 *Confidence:* {confidence}\n"
            f"🎯 *𝒮_Signal_Level:* {state.signal:.5f}\n"
            f"💰 *Current Price:* {state.price:.5f}\n"
            f"⚖️ *Imbalance @ h={state.h}:* m={m_at_h}, n={n_at_h}\n"
            f"⚖️ *Local m/n:* {m_local}/{n_local}\n"
            f"✅ *H/L gate (m>=12 or n>=12):* {condition_mark}\n"
            f"🔀 *𝒦 State:* {_cs(state.KC)}\n"
            f"🔢 *π:* {state.prime}\n"
            f"🔢 *δ_dime:* {state.dime}\n"
            f"🔄 *Tick Count:* {state.tick}\n"
            f"📈 *𝒯_trail:* {_cs(state.trailing_stop_active)}\n"
            f"🎯 *Last δ_bar:* {self.engine._last_kronecker_bar}"
        )
        reply_markup = self._build_main_keyboard()
        await self._safe_reply(update, response, reply_markup=reply_markup)

    async def indicators(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        if not self.engine.state.FG:
            self.engine._force_initialization()
        if not self.engine.state.FG:
            await self._safe_reply(update, "⏳ *Engine not initialized*\nPlease use `/start_feed`.")
            return
        state = self.engine.state
        y = state.y
        idx = state.Z - y - 1
        if idx < 0 or idx >= len(state.iA[0]):
            await self._safe_reply(update, "❌ Insufficient data for indicator projection.")
            return
        names = INDICATOR_NAMES_CS
        indicator_str = "📊 *13D ℋ_Projection*\n\n"
        for i, name in enumerate(names):
            val = state.iA[i][idx] if idx < len(state.iA[i]) else Decimal('50.0')
            val_int = int(float(val))
            bar_len = min(max(val_int // 10, 0), 10)
            bar = "█" * bar_len + "░" * (10 - bar_len)
            indicator_str += f"`{name:8}` {val:6.1f} ({_md_escape(bar)})\n"
        indicator_str += "\n*Thresholds:*\n"
        indicator_str += f"  Π^{{>θ}}: f+gf ≈ {F_PLUS_GF_D:.1f}\n"
        indicator_str += f"  Π^{{<θ}}: g-gf ≈ {G_MINUS_GF_D:.1f}"
        reply_markup = self._build_main_keyboard()
        await self._safe_reply(update, indicator_str, reply_markup=reply_markup)

    async def fvg(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        if not self.engine.state.FG:
            await self._safe_reply(update, "⏳ *Engine not initialized*\nPlease use `/start_feed`.")
            return
        state = self.engine.state
        idx = state.Z - state.y - 1
        bridge_fvgs = BRIDGE_STATE.list_fvgs()
        bridge_str = ""
        if bridge_fvgs:
            bridge_str = "\n📐 *Web App ℱ_VG:*\n"
            for f in bridge_fvgs[-8:]:
                mark = "▲" if f["type"] == "top" else "▼"
                who = f" (user {f['user_id']})" if f.get("user_id") else ""
                bridge_str += f"  {mark} {f['price']} idx={f['idx']}{who}\n"
        premium_val = state.Premium[idx] if 0 <= idx < len(state.Premium) else Decimal('0.0')
        discount_val = state.Discount[idx] if 0 <= idx < len(state.Discount) else Decimal('0.0')
        hh_val = state.HH[idx] if 0 <= idx < len(state.HH) else Decimal('0.0')
        ll_val = state.LL[idx] if 0 <= idx < len(state.LL) else Decimal('0.0')
        response = (
            "📐 *Fair Value Gap Tracking*\n"
            f"📊 *ℱ_VG Count:* {state.FVG + 1}\n"
            f"💰 *Current Price:* {state.price:.5f}\n"
            f"📉 *Last ℱ_VG:* {state.bL if state.bL else '—'}\n\n"
            "*Topological Anchors:*\n"
            f"  🔷 *Π^{{>θ}}:* {premium_val:.5f}\n"
            f"  🔶 *Π^{{<θ}}:* {discount_val:.5f}\n"
            f"  📈 *HH:* {hh_val:.5f}\n"
            f"  📉 *LL:* {ll_val:.5f}"
            f"{bridge_str}"
        )
        await self._safe_reply(update, response)

    async def chart(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        engine = self.engine
        state = engine.state
        recent_signals = state.signal_history[-10:]
        signal_summary = ""
        if recent_signals:
            for sig in recent_signals[-5:]:
                arrow = "↟" if sig["type"] == "BUY" else "↡"
                signal_summary += f"{arrow} {_cs(sig['type'])} @ {sig['price']:.2f} ({regime_to_cs(sig['regime'])})\n"
        else:
            signal_summary = "No signals yet.\n"
        response = (
            "📊 *Recent Signals*\n\n"
            f"{signal_summary}\n"
            f"📈 *Symbol:* {SYMBOL}\n"
            f"📊 *Bar Closes:* {state.bar_close_count}\n"
            f"📈 *OHLCV Bars:* {len(engine.ohlcv_history)}\n"
            f"🎯 *Total Signals Recorded:* {len(state.signal_history)}\n"
            f"🕐 *Last Signal:* {state.last_signal_at or 'never'}\n\n"
            "Open the ÆEA Mini App for the full interactive candlestick chart "
            "with ℱ_VG drawings, signal overlays, and the 𝒫_arc projection."
        )
        reply_markup = self._build_main_keyboard()
        await self._safe_reply(update, response, reply_markup=reply_markup)

    async def projection(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        engine = self.engine
        state = engine.state
        if not state.projection_path:
            engine._project_arc_length(trigger="manual_refresh")
        proj = engine.get_projection()
        meta = proj.get("meta") or {}
        path = proj.get("path") or []
        path_preview = ""
        for step in path[:10]:
            path_preview += f"  ▸ step {step['step']:>2}: {step['price']}\n"
        response = (
            "🌌 *𝒫_arc Price Projection*\n"
            f"📈 *Symbol:* {SYMBOL}\n"
            f"💰 *Current Price:* {proj.get('current_price')}\n"
            f"🎯 *Signal Anchor:* {proj.get('signal_level')}\n"
            f"📊 *ℛ_regime:* {proj.get('regime')}\n"
            f"🧮 *Branch:* {meta.get('kind', '—')}\n"
            f"⏱️ *𝒫_horizon:* {meta.get('horizon', '—')} bars\n"
            f"📐 *𝒫_slope:* {meta.get('slope', '—')}\n"
            f"📊 *𝒫_amp:* {meta.get('amplitude', '—')}\n"
            f"🎯 *𝒫_center:* {meta.get('center', '—')}\n"
            f"💧 *𝒫_damp:* {meta.get('damping', '—')}\n"
            f"🛰️ *Provider:* {meta.get('provider', '—')}\n"
            f"🕐 *Computed:* {proj.get('computed_at', 'never')}\n"
            f"🌌 *𝒫_trigger:* {proj.get('trigger', '—')}\n\n"
            "*First 10 projected bars:*\n"
            f"{path_preview or '  (no path computed)'}\n"
            "_The projection is drawn on the chart ahead of the current bar. "
            "Drag left past the last bar to scroll into the projected region._"
        )
        reply_markup = self._build_main_keyboard()
        await self._safe_reply(update, response, reply_markup=reply_markup)

    async def reset(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        prev_on_track = self.engine.state.on_track_runs
        prev_on_stand = self.engine.state.on_stand_runs
        prev_signals = len(self.engine.state.signal_history)
        prev_auth_m = self.engine.state.authoritative_m
        prev_auth_n = self.engine.state.authoritative_n
        self.engine.OnReInit()
        self.engine._project_arc_length(trigger="manual_refresh")
        reset_msg = (
            "🔄 *Topological Branch Reset*\n"
            "The Hilbert space projection has been re-anchored to the current\n"
            "topological branch with historical preservation.\n\n"
            "🧠 *State Reset:*\n"
            "• All 13 indicator arrays reset\n"
            "• ℛ_regime classification seeded to 'sRange'\n"
            "• Π^{>θ}/Π^{<θ}/HH/LL reset to current bar data\n"
            "• k/l signal flags cleared\n"
            "• ℱ_VG anchor map cleared\n"
            "• 𝒫_arc projection recomputed\n"
            "• ✨ Historical price data preserved\n"
            f"• 🔄 Tick count preserved: {self.engine.state.tick}\n"
            f"• 📈 𝒯_track runs preserved: {prev_on_track}\n"
            f"• 📉 𝒯_stand runs preserved: {prev_on_stand}\n"
            f"• 🎯 Signal history preserved: {prev_signals}\n"
            f"• ⚖️ Authoritative m/n reset to baseline: 0/0 (was {prev_auth_m}/{prev_auth_n})\n\n"
            "📊 *Ready for new ℛ_regime classification...*"
        )
        await self._safe_reply(update, reset_msg)

    async def start_feed(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        if self._running:
            await self._safe_reply(update, "⚠️ Price feed is already running.")
            return
        self._running = True
        self.engine._running = True
        self.engine._consecutive_zero_prices = 0
        historical = []
        try:
            historical = self.engine.feed.get_historical_klines(limit=200)
            if historical and len(historical) >= MIN_HISTORY_WINDOW:
                self.engine.ohlcv_history = historical
                logger.info(f"✅ Loaded {len(historical)} historical bars from relay for {self.engine.feed.active_symbol()} (provider={self.engine.feed.last_provider()})")
                self.engine._populate_indicator_matrix()
            else:
                logger.info(f"⏳ Relay returned {len(historical)} usable historical bars (need >= {MIN_HISTORY_WINDOW}). Engine will initialize organically.")
        except Exception as e:
            logger.warning(f"⚠️ Historical data fetch failed: {e}")
        try:
            self.engine.update_price_from_feed()
        except Exception:
            logger.exception("update_price_from_feed crashed during start_feed")
        if self._price_task is None or self._price_task.done():
            self._price_task = asyncio.create_task(self.price_feed_loop())
        hist_count = len(self.engine.ohlcv_history)
        init_mode = "Pre-seeded with history" if hist_count >= MIN_HISTORY_WINDOW else "Organic first-tick"
        reply_text = (
            f"✅ *Price feed started*\n"
            f"📈 *Symbol:* {SYMBOL}\n"
            f"🔄 *Update Interval:* {UPDATE_INTERVAL}s\n"
            f"📊 *Historical Data:* {hist_count} bars loaded\n"
            f"🛰️ *Provider:* `{self.engine.state.last_provider or '—'}`\n"
            f"📦 *𝒱:* `{self.engine.state.last_volume}`\n"
            f"🧠 *Initialization Mode:* {init_mode}\n"
            f"📈 *Indicator Passes:* {self.engine._indicator_populate_count}\n"
            f"🌌 *𝒫_arc:* `{self.engine.state.projection_meta.get('kind', '—') if self.engine.state.projection_meta else '—'}`\n"
            f"🔮 *Status:* Monitoring for signals..."
        )
        await self._safe_reply(update, reply_text)

    async def stop_feed(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        self._running = False
        self.engine._running = False
        if self._price_task and not self._price_task.done():
            self._price_task.cancel()
        await self._safe_reply(update, "⏹️ *Price feed stopped*")

    async def probe(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        info = self.engine.feed.probe()
        status = "✅ OK" if not info.get("empty") else "❌ EMPTY"
        lines = [
            "🔬 *Relay Probe*", "",
            f"*Status:* {status}",
            f"*Relay URL:* `{RELAY_URL or 'UNSET'}`",
            f"*Relay Gated:* {'🔐 yes' if RELAY_KEY else '🔓 no'}",
            f"*Primary symbol:* `{info.get('primary_symbol')}`",
            f"*Active symbol:* `{info.get('active_symbol')}`",
            f"*Provider:* `{info.get('provider') or '—'}`",
            f"*Last 𝒱:* `{info.get('last_volume') or '0'}`",
            f"*Chain index:* {info.get('chain_index')}",
            f"*Failure count:* {info.get('failure_count')}",
            f"*Fallback count:* {info.get('fallback_count')}",
            f"*Last update:* {info.get('last_update') or 'never'}",
        ]
        text = "\n".join(lines)
        await self._safe_reply(update, text)

    async def rebuild_yf(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        self.engine.feed._rebuild_ticker()
        self.engine.feed._fallback_count = 0
        self.engine._consecutive_zero_prices = 0
        if len(self.engine.feed._chain) > 1:
            self.engine.feed._advance_symbol_chain()
        active = self.engine.feed.active_symbol()
        text = (
            f"♻️ *Relay client rebuilt*\n"
            f"🔎 *Active symbol:* `{active}`\n"
            f"_Feed will use this symbol on next iteration._"
        )
        await self._safe_reply(update, text)

    async def symbol(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        args = context.args
        if not args:
            supported = ", ".join(list(SYMBOL_MAP.keys())[:10])
            await self._safe_reply(update,
                f"📈 *Current Symbol:* `{SYMBOL}`\n"
                "Use `/symbol <PAIR>` to change.\n"
                "Example: `/symbol GRAM-USD` or `/symbol TONUSDT` or `/symbol AAPL`\n\n"
                f"*Supported Symbols:*\n{supported}\n(and {len(SYMBOL_MAP) - 10} more)")
            return
        new_symbol = args[0].upper()
        result = self.engine.change_symbol(new_symbol)
        if result.get("ok"):
            await self._safe_reply(update,
                f"✅ *Symbol changed*\n"
                f"📈 *New Symbol:* `{result.get('symbol')}`\n"
                f"🛰️ *Provider:* `{result.get('provider') or '—'}`\n"
                f"🧠 *Engine reinitialized*\n"
                f"🌌 *𝒫_arc seeded for the new symbol*")
        else:
            detail = result.get("detail") or result.get("error") or "unknown"
            await self._safe_reply(update, f"❌ Error: {detail}")

    async def info(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        info = self.engine.feed.get_info()
        response = (
            "📊 *Ticker Information*\n"
            f"📈 *Symbol:* {SYMBOL}\n"
            f"📛 *Name:* {info.get('name', 'Unknown')}\n"
            f"💵 *Currency:* {info.get('currency', 'USD')}\n"
            f"🛰️ *Provider:* `{self.engine.state.last_provider or '—'}`\n"
            f"📦 *Last 𝒱:* `{self.engine.state.last_volume}`\n"
        )
        await self._safe_reply(update, response)

    async def webapp(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        url = self._resolve_webapp_url()
        if not url:
            await self._safe_reply(update,
                "⏳ *Mini App URL not yet available*\n"
                "The bridge is starting a public HTTPS tunnel. "
                "Please try again in ~30–45 seconds.\n"
                "Alternatively, set `TELEGRAM_WEBAPP_URL` in the environment.")
            return
        keyboard = InlineKeyboardMarkup([[InlineKeyboardButton("⚡ Open ÆEA Mini App", web_app=WebAppInfo(url=url))]])
        await self._safe_reply(update,
            "🌐 *ÆEA Telegram Mini App*\n"
            "Tap the button below to launch the full engine visualization.\n\n"
            "*Features inside the Mini App:*\n"
            "  📈 Interactive MT4-style candlestick chart\n"
            "  📊 Add/remove indicator sub-panels\n"
            "  📐 Draw ℱ_VGs with long-press\n"
            "  🎯 Place simulated orders\n"
            "  ⚙ Engine settings panel\n"
            "  📋 ℛ_regime map, log bar, signal markers\n"
            "  🌌 𝒫_arc price projection ahead of the current bar\n"
            "  ➡️ Scroll-ahead viewport to the projected take-profit level\n"
            "  🔔 Toast + Telegram push notifications on every execution\n"
            "  🔄 Live state polling\n"
            "  🪙 GRAM / TON and the full expanded symbol universe\n"
            "  📊 Crypto / Futures / Equities / Forex / Indices sections",
            reply_markup=keyboard)

    async def handle_group_mention(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        msg = update.effective_message
        if msg is None or not msg.text:
            return
        chat = update.effective_chat
        if chat is None or getattr(chat, "type", None) not in ("group", "supergroup"):
            return
        bot_username = (getattr(context.bot, "username", None) or self.bot_name or "").lstrip("@")
        if not bot_username:
            return
        handles = _re_bridge.findall(r"@([A-Za-z0-9_]+)", msg.text)
        if bot_username.lower() not in [h.lower() for h in handles]:
            return
        prev_chat_id = self.engine.state.chat_id
        prev_last_inbound = self.engine.state.last_inbound_message_id
        try:
            self._track_inbound_message(update)
        finally:
            self.engine.state.chat_id = prev_chat_id
            self.engine.state.last_inbound_message_id = prev_last_inbound
        url = self._resolve_webapp_url()
        thread_id = getattr(msg, "message_thread_id", None)
        if not url:
            text = (
                "⏳ Mini App URL not yet available\n"
                "The bridge is starting a public HTTPS tunnel. "
                "Please try again in ~30–45 seconds.\n"
                "Alternatively, set `TELEGRAM_WEBAPP_URL` in the environment."
            )
            try:
                await context.bot.send_message(chat_id=chat.id, text=text, message_thread_id=thread_id)
            except Exception as e1:
                logger.info(f"Group mention threaded reply failed: {e1}")
                if thread_id is not None:
                    try:
                        await context.bot.send_message(chat_id=chat.id, text=text)
                    except Exception as e2:
                        logger.warning(f"Group mention reply failed: {e2}")
            return
        keyboard = InlineKeyboardMarkup([[InlineKeyboardButton("⚡ Open ÆEA Mini App", web_app=WebAppInfo(url=url))]])
        text = "Click below to open the ÆEA Engine:"
        try:
            await context.bot.send_message(
                chat_id=chat.id, text=text, reply_markup=keyboard, message_thread_id=thread_id
            )
            return
        except Exception as e1:
            logger.info(f"Group mention threaded reply failed: {e1}")
        if thread_id is not None:
            try:
                await context.bot.send_message(chat_id=chat.id, text=text, reply_markup=keyboard)
                return
            except Exception as e2:
                logger.info(f"Group mention unthreaded reply failed: {e2}")
        try:
            await msg.reply_text(text, reply_markup=keyboard)
        except Exception as e3:
            logger.warning(f"Group mention reply failed: {e3}")

    async def webgui(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        scheme = "https" if BRIDGE_USE_TLS else "http"
        local_url = f"{scheme}://{BRIDGE_HOST}:{BRIDGE_PORT}/"
        public_url = self._resolve_webapp_url() or "⏳ (tunnel pending)"
        await self._safe_reply(update,
            f"🌐 *ÆEA Bridge Endpoints*\n"
            f"*Local URL:* `{local_url}`\n"
            f"*Public URL:* `{public_url}`\n"
            f"*State endpoint:* `{public_url.rstrip('/')}/state`\n"
            f"*Mini App State:* `{public_url.rstrip('/')}/miniapp-state`\n"
            f"*Projection endpoint:* `{public_url.rstrip('/')}/projection`\n"
            f"*Health endpoint:* `{public_url.rstrip('/')}/health`\n"
            f"*Probe endpoint:* `{public_url.rstrip('/')}/probe`\n"
            f"*Diagnostics endpoint:* `{public_url.rstrip('/')}/diagnostics`\n"
            f"*OHLCV endpoint:* `{public_url.rstrip('/')}/ohlcv`\n"
            f"*Signals endpoint:* `{public_url.rstrip('/')}/signals`\n"
            f"*Orders endpoint:* `{public_url.rstrip('/')}/orders`\n"
            f"*Regime map endpoint:* `{public_url.rstrip('/')}/regime-map`\n"
            f"*Log endpoint:* `{public_url.rstrip('/')}/log`\n"
            f"*Toasts endpoint:* `{public_url.rstrip('/')}/toasts`\n"
            f"*Settings endpoint:* `{public_url.rstrip('/')}/settings`\n"
            f"*Handshake endpoint:* `POST {public_url.rstrip('/')}/handshake`")

    async def whoami(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        self._track_inbound_message(update)
        user = update.effective_user
        chat = update.effective_chat
        user_id = user.id if user else None
        chat_id = chat.id if chat else None
        allowed = _is_allowed_user(user_id)
        banned = _is_banned_user(user_id)
        await self._safe_reply(update,
            f"🪪 *Identity*\n"
            f"*user_id:* `{user_id}`\n"
            f"*chat_id:* `{chat_id}`\n"
            f"*username:* @{user.username if user and user.username else '—'}\n"
            f"*first_name:* {user.first_name if user else '—'}\n"
            f"*Allowlist:* {sorted(ALLOWED_USER_IDS)}\n"
            f"*Banlist:* {sorted(BANNED_USER_IDS)}\n"
            f"*Ban:* {'🚫 banned' if banned else '✅ not banned'}\n"
            f"*Gate:* {'✅ allowed' if allowed else '❌ blocked'}\n"
            f"*Gate active:* {'yes' if ALLOWED_USER_IDS else 'no (open bot)'}")

    async def button_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        query = update.callback_query
        user = update.effective_user
        user_id = None
        if user is not None and getattr(user, "id", None) is not None:
            user_id = int(user.id)
        if user_id is not None and _is_banned_user(user_id):
            logger.info(f"🚫 Blocked callback from banned user_id={user_id}")
            try:
                await query.answer("Banned.", show_alert=True)
            except Exception:
                pass
            return
        if user_id is not None and not _is_allowed_user(user_id):
            logger.info(f"🚫 Blocked callback from unauthorized user_id={user_id}")
            try:
                await query.answer("Unauthorized.", show_alert=True)
            except Exception:
                pass
            return
        await query.answer()
        action = query.data
        if action == "status":
            await self.status(update, context)
        elif action == "regime":
            await self.regime(update, context)
        elif action == "signal":
            await self.signal(update, context)
        elif action == "indicators":
            await self.indicators(update, context)
        elif action == "chart":
            await self.chart(update, context)
        elif action == "projection":
            await self.projection(update, context)
        elif action == "start_feed":
            await self.start_feed(update, context)
        elif action == "stop_feed":
            await self.stop_feed(update, context)
        elif action == "info":
            await self.info(update, context)
        elif action == "reset":
            await self.reset(update, context)
        elif action == "probe":
            await self.probe(update, context)
        elif action == "rebuild_yf":
            await self.rebuild_yf(update, context)
        elif action == "diagnostics":
            await self.diagnostics(update, context)
        elif action == "webapp_pending":
            try:
                await query.edit_message_text("⏳ *Mini App tunnel is starting…*\nPlease retry `/webapp` in ~30–45 seconds.", parse_mode="Markdown")
            except Exception:
                try:
                    await query.edit_message_text("Mini App tunnel is starting. Please retry /webapp in ~30-45 seconds.", parse_mode=None)
                except Exception as e:
                    logger.warning(f"webapp_pending edit failed: {e}")

    async def error_handler(self, update: Update, context: ContextTypes.DEFAULT_TYPE):
        err = context.error
        if isinstance(err, PermissionError) and str(err) in ("private_bot_unauthorized_user", "banned_user"):
            # Private-bot gate / ban list already logged the block at info level.
            # Do not append to the user-visible log ring buffer.
            return
        err_str = f"{type(err).__name__}: {err}" if err is not None else "unknown error"
        try:
            with _LOG_LOCK:
                _LOG_BUFFER.append({
                    "ts": datetime.now().isoformat(),
                    "level": "error",
                    "msg": f"⚠️ handler error: {err_str}",
                })
        except Exception:
            pass
        logger.error(f"Update {update} caused error {err}")

    async def _post_init(self, application) -> None:
        try:
            self._loop = asyncio.get_running_loop()
            logger.info("🔁 Event loop captured for cross-thread send")
        except RuntimeError:
            self._loop = None
            logger.warning("⚠️ No running loop in _post_init; sends will be dropped")
        BRIDGE_ENGINE_REF["engine"] = self.engine
        BRIDGE_ENGINE_REF["bot"] = self
        self.engine.application = application
        logger.info("🔗 BRIDGE_ENGINE_REF populated in _post_init")
        
        if self._bridge_server is None:
            server = BridgeServer()
            server.start()
            self._bridge_server = server
            logger.info("🌐 BridgeServer started from _post_init")
            
        url = self._resolve_webapp_url()
        if not url:
            logger.info("⏳ MenuButtonWebApp deferred — no public URL yet")
            return
        try:
            await application.bot.set_chat_menu_button(menu_button=MenuButtonWebApp(text="ÆEA Mini App", web_app=WebAppInfo(url=url)))
            logger.info(f"✅ MenuButtonWebApp registered: {url}")
        except Exception as e:
            logger.warning(f"Failed to set menu button: {e}")

    def run(self):
        self.engine.OnInit()
        self.application = Application.builder().token(self.token).post_init(self._post_init).build()
        self.application.add_handler(CommandHandler("start", self.start))
        self.application.add_handler(CommandHandler("help", self.help))
        self.application.add_handler(CommandHandler("status", self.status))
        self.application.add_handler(CommandHandler("regime", self.regime))
        self.application.add_handler(CommandHandler("signal", self.signal))
        self.application.add_handler(CommandHandler("indicators", self.indicators))
        self.application.add_handler(CommandHandler("chart", self.chart))
        self.application.add_handler(CommandHandler("fvg", self.fvg))
        self.application.add_handler(CommandHandler("projection", self.projection))
        self.application.add_handler(CommandHandler("diagnostics", self.diagnostics))
        self.application.add_handler(CommandHandler("reset", self.reset))
        self.application.add_handler(CommandHandler("start_feed", self.start_feed))
        self.application.add_handler(CommandHandler("stop_feed", self.stop_feed))
        self.application.add_handler(CommandHandler("symbol", self.symbol))
        self.application.add_handler(CommandHandler("info", self.info))
        self.application.add_handler(CommandHandler("probe", self.probe))
        self.application.add_handler(CommandHandler("rebuild_yf", self.rebuild_yf))
        self.application.add_handler(CommandHandler("webapp", self.webapp))
        self.application.add_handler(CommandHandler("webgui", self.webgui))
        self.application.add_handler(CommandHandler("mini", self.webapp))
        self.application.add_handler(CommandHandler("whoami", self.whoami))
        self.application.add_handler(
            MessageHandler(filters.ChatType.GROUPS & filters.Entity("mention"), self.handle_group_mention)
        )
        self.application.add_handler(CallbackQueryHandler(self.button_handler))
        self.application.add_error_handler(self.error_handler)
        logger.info(f"🤖 {self.bot_name} starting...")
        logger.info("📊 Quantum-Financial Topology Engine (MQL4-parity port ).")
        logger.info(f"🧠 X_PERIOD (const) = {X_PERIOD}, Y_START (const) = {Y_START}")

        logger.info("⚡ 13D Hilbert-space projection populated per bar.")
        logger.info("📡 Bar-close detection uses relay timestamp.")
        logger.info("🎯 Signal logging enabled for all imbalance events.")
        logger.info("⚡ Telegram Mini App enabled (MT4/TradingView-style).")
        logger.info("💬 Group-topic mention enabled: @mention in a group topic replies in that topic with the Web App button.")
        logger.info(f"🚫 Ban list: {len(BANNED_USER_IDS)} ID(s) banned (BANNED_IDS) — ban wins over allowlist.")
        logger.info("🛑 𝒯_trail: real Ask−Bid spread + symbol-adaptive point size + STOP_LOSS minimum.")
        logger.info("🎯 δ gate: LOCAL m/n from authoritative H()/L() stamps.")
        logger.info("🔄 O() regime mutation applied via write-back (D-RES-1).")
        logger.info("📊 OnBar per-j HH/LL anchoring.")
        logger.info("🔍 OnTrack/OnStand MQL4 loop bounds kept (aliased S, not grown copy).")
        logger.info("🔒 Auth enforcement on all non-/health endpoints except GET / and GET /index.html, which serve static HTML with no state and no secrets.")
        logger.info("📈 Chart endpoint & signal history tracking enabled.")
        logger.info("📐 User FVGs stored in bridge registry only (non-destructive).")
        logger.info("🛰️ Multi-provider relay : Kraken → Binance → CoinGecko → Yahoo for crypto; Stooq → Yahoo for equities/futures; Yahoo for forex/indices.")
        logger.info("📦 Real volume carried through OBV, AD, Force, MFI projections.")
        logger.info("🌌 𝒫_arc projection computed on execution, init, symbol change, and manual refresh.")
        logger.info("🔔 Push notification on every signal, every execution, every FVG, every close.")
        logger.info("🔔 /toasts endpoint serves incremental signal+execution+fvg toasts with first_available_seq.")
        logger.info("⚙️ /settings GET+POST with exact-decimal parsing and FF-input validation max >= min + 2.")
        logger.info("🖱️ Scroll-ahead viewport: drag past the last bar to the projected TP.")
        logger.info("🎯 Execution-gated projection: recomputed on Bull/Bear/Hawk/Dove/Whisky/Wine/Watter/Blood/Diamond/Ruby.")
        logger.info("💬 Push threading: every push is a reply to the user's most recent inbound message.")
        logger.info("📮 Bounded push dispatch: single queue.Queue(maxsize=512) with one daemon consumer.")
        logger.info("🔁 Cross-thread send: enabled via asyncio.run_coroutine_threadsafe")
        logger.info("🛡️ Markdown escaping: _md_escape applied to every interpolated value (E-12).")
        logger.info("🛡️ Reply-target hardening: retry as standalone on stale reply id (E-11).")
        logger.info("🛡️ Plain-text fallback: parse_mode=None on parse errors (E-13).")
        logger.info(f"🪙  symbol universe: GRAM-USD (TON) + {len(SYMBOL_MAP)} total symbols across crypto, futures, equities, forex, and indices.")
        logger.info("AE TWA  — backend starting. One ordered feed, one formatter, one state.")
        logger.info("✅ Ready. Use /start to begin.")
        self.application.run_polling()

try:
    _bridge_attach_to_bot(AEI_Bot)
except Exception as _attach_exc:
    import logging as _l
    _l.basicConfig(level=_l.INFO)
    _l.getLogger(__name__).exception("Bridge attach failed: %s", _attach_exc)

# ============================================================================
# MAIN ENTRY POINT
# ============================================================================
def main():
    TOKEN = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
    if not TOKEN:
        logger.error("❌ Error: TELEGRAM_BOT_TOKEN not set.")
        logger.error("   export TELEGRAM_BOT_TOKEN='YOUR_BOT_TOKEN'")
        sys.exit(1)
    bot = AEI_Bot(TOKEN, "UpscaleTradeBot")
    bot.run()

if __name__ == "__main__":
    main()

# ============================================================================
# Q.E.D. — LOGOS = Φ = Truth = Path = Origin
# ============================================================================
