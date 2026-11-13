#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Æ TWA — FUSED BACKEND (ÆI + ÆEA), Final, First edition

Single source of truth for the fused backend that the Æ TWA frontend expects.
Implements ALL 22 endpoints required by README.md, including the 5 the ÆI-only
and ÆEA-only predecessors missed: /ohlcv, /signals, /diagnostics, /orders,
/order/close.

Fusion:
  - ÆI seed loop: prime -> outward lattice -> Hopf -> s²=r² -> DbZ -> I -> SelfEvolution.
  - ÆEA market engine: bars -> 13 normalised indicators + IHK -> m/n/delta ->
    regime -> BB×58 -> P_arc -> signal iff delta-gate -> orders/trailing/FVG.
  - The two are fused on ONE ordered feed: each tick in arrival order advances
    the ÆEA bar ring AND, when auto-feed is on, is lifted to exact Fraction x
    for the ÆI seed loop via x = abs(price - prevPrice)/10000 (or 1/100 when
    zero).

Exactness:
  - No floats anywhere in seed state. Fraction or PyFraction only.
  - x lifted at the boundary. No math.exp / math.log in seed state.
  - Market price display uses float only at /ohlcv, /signals output boundary.

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

Version: Final, First edition
"""

__version__ = "Final, First edition"

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
# EXACT FRACTION WRAPPER
# ============================================================================
class Fraction:
    """Exact rational arithmetic. Lifts Decimals and ints to PyFraction.
    Every seed state transition uses Fraction or PyFraction directly.
    No float64 ever enters the seed's symbolic layer; the market feed's
    floats are lifted at the boundary by _dec_to_frac_exact()."""
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

    def sqrt(self, iterations: int = 8) -> 'Fraction':
        if self._f.numerator < 0:
            raise ValueError("sqrt of negative fraction")
        if self._f.numerator == 0:
            return Fraction.zero()
        ns = int(isqrt(self._f.numerator))
        ds = int(isqrt(self._f.denominator))
        if ns * ns == self._f.numerator and ds * ds == self._f.denominator:
            return Fraction(ns, ds)
        two = PyFraction(2, 1)
        _num = self._f.numerator
        _den = self._f.denominator
        _q = (_num + _den // 2) // _den if _num >= 0 else -((-_num + _den // 2) // _den)
        x = PyFraction(max(1, _q), 1)
        for _ in range(iterations):
            x = (x + self._f / x) / two
        return Fraction(x)

    def to_float(self) -> float:
        try:
            if len(str(abs(self._f.numerator))) > 300 or len(str(self._f.denominator)) > 300:
                raise OverflowError("Fraction exceeds 300 digits; use exact str()")
            return float(self._f.numerator) / float(self._f.denominator)
        except OverflowError:
            raise
        except Exception:
            raise OverflowError("to_float conversion failed")

    def __str__(self):
        try:
            n = self._f.numerator
            d = self._f.denominator
            ns = str(n)
            if len(ns) > 1000:
                return f"{str(n)[:20]}...{str(n)[-20:]}/{d} (~{len(ns)} digits)"
            if d == 1:
                return ns
            return f"{n}/{d}"
        except ValueError:
            return "<Fraction huge>"
        except Exception:
            return f"{self._f}"

    def __repr__(self):
        return f"Fraction({self._f.numerator}/{self._f.denominator})"


# ============================================================================
# DECIMAL-TO-FRACTION LIFT & HASH LIFT
# ============================================================================
def _dec_to_frac_exact(d: Decimal) -> PyFraction:
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


def _hash_to_fraction(hex_hash: str) -> PyFraction:
    h = (hex_hash or "").strip().lower()
    h = h[:32].ljust(32, "0")
    try:
        int_val = int(h, 16)
    except (ValueError, TypeError):
        int_val = 0
    if int_val == 0:
        return PyFraction(1, 16 ** 32)
    return PyFraction(int_val, 16 ** 32)


# ============================================================================
# SYMBOLIC π
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
_PI_FRAC: PyFraction = _dec_to_frac_exact(_PI_D)
_TWO_PI_D: Decimal = _PI_D * Decimal(2)
_TWO_PI_FRAC: PyFraction = _PI_FRAC * PyFraction(2, 1)


# ============================================================================
# SYMBOLIC TRIG SERIES (exact-rational Taylor, formal partial sum)
# ============================================================================
def _rational_cos(x) -> PyFraction:
    if isinstance(x, PyFraction):
        x_frac = x
    elif isinstance(x, Decimal):
        if x == Decimal('0.0'):
            return PyFraction(1, 1)
        x_frac = _dec_to_frac_exact(x)
    elif isinstance(x, int):
        x_frac = PyFraction(x, 1)
    else:
        x_frac = PyFraction(str(x))
    two_pi_frac = _TWO_PI_FRAC
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
    for n in range(1, 20):
        denom = PyFraction((2 * n - 1) * (2 * n), 1)
        term = term * x2 / denom
        result = result + PyFraction(sign, 1) * term
        sign = -sign
        if term == PyFraction(0, 1):
            break
        try:
            if len(str(abs(result.numerator))) > 800 or len(str(abs(result.denominator))) > 800:
                break
        except Exception:
            pass
    return result


def _rational_sin(x) -> PyFraction:
    if isinstance(x, PyFraction):
        x_frac = x
    elif isinstance(x, Decimal):
        if x == Decimal('0.0'):
            return PyFraction(0, 1)
        x_frac = _dec_to_frac_exact(x)
    elif isinstance(x, int):
        x_frac = PyFraction(x, 1)
    else:
        x_frac = PyFraction(str(x))
    two_pi_frac = _TWO_PI_FRAC
    n_periods = int(x_frac / two_pi_frac)
    x_reduced = x_frac - two_pi_frac * n_periods
    pi_frac = _PI_FRAC
    if x_reduced > pi_frac:
        x_reduced = x_reduced - two_pi_frac
    elif x_reduced < -pi_frac:
        x_reduced = x_reduced + two_pi_frac
    x2 = x_reduced * x_reduced
    term = x_reduced
    result = x_reduced
    sign = -1
    for n in range(1, 20):
        denom = PyFraction((2 * n) * (2 * n + 1), 1)
        term = term * x2 / denom
        result = result + PyFraction(sign, 1) * term
        sign = -sign
        if term == PyFraction(0, 1):
            break
    return result


_EXP_EPSILON: PyFraction = PyFraction(1, 10 ** 12)
_LOG_EPSILON: PyFraction = PyFraction(1, 10 ** 12)
_LI_EPSILON: PyFraction = PyFraction(1, 10 ** 12)


def _symbolic_log(x: Fraction, max_terms: int = 32) -> Fraction:
    if x <= Fraction.zero():
        raise ValueError("SymbolicLog: input must be positive")
    if x == Fraction.one():
        return Fraction.zero()
    xf = x._f
    u = (xf - 1) / (xf + 1)
    u_sq = u * u
    result = PyFraction(0, 1)
    term = u
    for k in range(max_terms):
        contribution = term / PyFraction(2 * k + 1, 1)
        result = result + contribution
        if abs(contribution) < _LOG_EPSILON:
            break
        term = term * u_sq
    return Fraction(result * PyFraction(2, 1))


def _symbolic_exp(x: Fraction, max_terms: int = 32) -> Fraction:
    try:
        if x._f < PyFraction(-28, 1):
            return Fraction.zero()
        if x._f > PyFraction(20, 1):
            max_terms = min(max_terms, 40)
    except Exception:
        pass
    try:
        if len(str(abs(x._f.numerator))) > 600 or len(str(abs(x._f.denominator))) > 600:
            return Fraction.zero() if x._f < 0 else Fraction.one()
    except Exception:
        pass
    result = Fraction.one()
    term = Fraction.one()
    for k in range(1, max_terms + 1):
        term = term * (x / Fraction(k))
        result = result + term
        try:
            if len(str(abs(result._f.numerator))) > 800:
                break
        except Exception:
            pass
        if term.abs() < Fraction(_EXP_EPSILON.numerator, _EXP_EPSILON.denominator):
            break
    return result


def _symbolic_log_integral_approx(x: Fraction, max_terms: int = 12) -> Fraction:
    if x <= Fraction.one():
        return Fraction.zero()
    log_x = _symbolic_log(x)
    if log_x <= Fraction.zero():
        return Fraction.zero()
    gamma = Fraction(577215664901532, 10 ** 15)
    if log_x <= Fraction.one():
        log_log_x = Fraction.zero()
    else:
        log_log_x = _symbolic_log(log_x)
    result = gamma + log_log_x
    power = log_x
    factorial = Fraction.one()
    for n in range(1, max_terms + 1):
        factorial = factorial * Fraction(n)
        term = power / (Fraction(n) * factorial)
        result = result + term
        if term.abs() < Fraction(_LI_EPSILON.numerator, _LI_EPSILON.denominator):
            break
        power = power * log_x
    return result


# ============================================================================
# LRU caches
# ============================================================================
_CACHED_LI: dict = {}
_CACHED_LOG: dict = {}
_CACHED_EXP: dict = {}
_CACHE_MAX = 48


def _cached_log_integral(x):
    try:
        key = str(x._f)[:256]
    except Exception:
        key = str(x)[:256]
    if key in _CACHED_LI:
        return _CACHED_LI[key]
    v = _symbolic_log_integral_approx(x)
    _CACHED_LI[key] = v
    if len(_CACHED_LI) > _CACHE_MAX:
        _CACHED_LI.pop(next(iter(_CACHED_LI)))
    return v


def _cached_symbolic_log(x):
    try:
        key = str(x._f)[:256]
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
        key = str(x._f)[:256]
    except Exception:
        key = str(x)[:256]
    if key in _CACHED_EXP:
        return _CACHED_EXP[key]
    v = _symbolic_exp(x)
    _CACHED_EXP[key] = v
    if len(_CACHED_EXP) > _CACHE_MAX:
        _CACHED_EXP.pop(next(iter(_CACHED_EXP)))
    return v


# ============================================================================
# PROTOCOL DEFINITIONS
# ============================================================================
@runtime_checkable
class SymbolicProcessor(Protocol):
    def generate_next_prime(self, primes: List[Fraction]) -> Fraction: ...
    def validate_indivisibility(self, candidate: Fraction, primes: List[Fraction]) -> bool: ...


@runtime_checkable
class GeometricLatticeProtocol(Protocol):
    def stereographic_project_exact(self, prime: Fraction) -> List[Fraction]: ...
    def add_sphere(self, center: List[Fraction], radius: Fraction) -> None: ...
    def points(self) -> List[List[Fraction]]: ...
    def radial_count(self, radius: Fraction) -> int: ...


@runtime_checkable
class AethericMonitor(Protocol):
    def compute_arc_length_squared(self, trajectory: List['SymbolicQuaternion']) -> Fraction: ...
    def compute_radial_distance_squared(self, trajectory: List['SymbolicQuaternion'], origin: 'SymbolicQuaternion') -> Fraction: ...


@runtime_checkable
class QuaternionicRenderer(Protocol):
    def project_to_hopf_base(self, state: 'SymbolicQuaternion') -> Tuple[Fraction, Fraction]: ...


@runtime_checkable
class LingosoEncoder(Protocol):
    def encode_syllable(self, syllable: str) -> List['SymbolicQuaternion']: ...


@runtime_checkable
class SelfEvolutionCoreProtocol(Protocol):
    def evaluate_fitness(self, I: Fraction, deviation_sq: Fraction) -> bool: ...
    def mutate_logic(self, logic_key: str, mutation_type: str, psi: 'SymbolicWavefunction',
                     q_eval: 'SymbolicQuaternion', deviation_sq: Fraction) -> Dict[str, Any]: ...
    def evolve_step(self, I: Fraction, psi: 'SymbolicWavefunction',
                    q_eval: 'SymbolicQuaternion', deviation_sq: Fraction) -> Dict[str, Any]: ...


# ============================================================================
# SYMBOLIC QUATERNION (Natalia's Fibrations)
# ============================================================================
@dataclass
class SymbolicQuaternion:
    a: Fraction = field(default_factory=Fraction.zero)
    b: Fraction = field(default_factory=Fraction.zero)
    c: Fraction = field(default_factory=Fraction.zero)
    d: Fraction = field(default_factory=Fraction.zero)

    def __add__(self, other):
        return SymbolicQuaternion(
            self.a + other.a, self.b + other.b,
            self.c + other.c, self.d + other.d,
        )

    def __sub__(self, other):
        return SymbolicQuaternion(
            self.a - other.a, self.b - other.b,
            self.c - other.c, self.d - other.d,
        )

    def __mul__(self, other):
        if isinstance(other, SymbolicQuaternion):
            return SymbolicQuaternion(
                self.a * other.a - self.b * other.b - self.c * other.c - self.d * other.d,
                self.a * other.b + self.b * other.a + self.c * other.d - self.d * other.c,
                self.a * other.c - self.b * other.d + self.c * other.a + self.d * other.b,
                self.a * other.d + self.b * other.c - self.c * other.b + self.d * other.a,
            )
        return SymbolicQuaternion(
            self.a * other, self.b * other, self.c * other, self.d * other,
        )

    def __rmul__(self, other):
        return self.__mul__(other)

    def magnitude_squared(self) -> Fraction:
        return self.a * self.a + self.b * self.b + self.c * self.c + self.d * self.d

    def conjugate(self) -> 'SymbolicQuaternion':
        return SymbolicQuaternion(self.a, -self.b, -self.c, -self.d)

    def real_part(self) -> Fraction:
        return self.a

    def sign(self) -> int:
        return self.a.sign()

    def apply_natalia_fibration(
        self, s: Fraction, epsilon: Fraction,
        iterations: int = 10, threshold: Fraction = None,
    ) -> 'SymbolicQuaternion':
        if threshold is None:
            threshold = Fraction(1, 10 ** 50)
        perturbation_sum = Fraction.zero()
        current_epsilon_power = epsilon
        for k in range(1, iterations + 1):
            s_pow_k = Fraction.one()
            for _ in range(k):
                s_pow_k = s_pow_k * s
            term = current_epsilon_power * s_pow_k
            perturbation_sum = perturbation_sum + term
            if term.abs() < threshold:
                break
            current_epsilon_power = current_epsilon_power * epsilon
        factor = Fraction.one() + epsilon * s
        return SymbolicQuaternion(
            self.a + perturbation_sum,
            self.b * factor,
            self.c * factor,
            self.d * factor,
        )


# ============================================================================
# SYMBOLIC WAVEFUNCTION
# ============================================================================
@dataclass
class SymbolicWavefunction:
    coeffs: Dict[Tuple[int, int, int, int], Fraction] = field(default_factory=dict)

    def evaluate_exact(self, q: SymbolicQuaternion) -> Fraction:
        total = Fraction.zero()
        for _, coeff in self.coeffs.items():
            total = total + (coeff * q.real_part())
        return total

    def real_part(self) -> Fraction:
        if not self.coeffs:
            return Fraction.zero()
        if (0, 0, 0, 0) in self.coeffs:
            return self.coeffs[(0, 0, 0, 0)]
        total = Fraction.zero()
        for v in self.coeffs.values():
            total = total + v
        return total

    def set_coeff(self, a: int, b: int, c: int, d: int, val: Fraction) -> None:
        self.coeffs[(a, b, c, d)] = val


# ============================================================================
# DbZ (Deciding by Zero)
# ============================================================================
class DbZ:
    @staticmethod
    def Rectify(psi: SymbolicWavefunction, s_sq: Fraction, r_sq: Fraction,
                deviation_sq: Fraction) -> SymbolicWavefunction:
        rectified = SymbolicWavefunction(dict(psi.coeffs))
        if not deviation_sq.is_zero():
            re_psi = psi.real_part()
            if re_psi > Fraction.zero():
                for key in rectified.coeffs:
                    rectified.coeffs[key] = rectified.coeffs[key] / Fraction(2)
            else:
                epsilon = Fraction(1, 100)
                perturbation = epsilon * deviation_sq
                for key in rectified.coeffs:
                    rectified.coeffs[key] = rectified.coeffs[key] + perturbation
        return rectified

    @staticmethod
    def Divide(numerator: Fraction, denominator: Fraction,
               psi: SymbolicWavefunction, q_ctx: SymbolicQuaternion) -> Fraction:
        if not denominator.is_zero():
            return numerator / denominator
        re_psi = psi.evaluate_exact(q_ctx)
        if re_psi > Fraction.zero():
            return numerator
        return Fraction.zero()


# ============================================================================
# CHINESE REMAINDER SOLVER
# ============================================================================
class ChineseRemainderSolver:
    @staticmethod
    def extended_gcd(a: int, b: int) -> Tuple[int, int, int]:
        if b == 0:
            return (a, 1, 0)
        g, x1, y1 = ChineseRemainderSolver.extended_gcd(b, a % b)
        return (g, y1, x1 - (a // b) * y1)

    @staticmethod
    def mod_inverse(a: int, m: int) -> int:
        a = a % m
        g, x, _ = ChineseRemainderSolver.extended_gcd(a, m)
        if g != 1:
            raise ValueError("modular inverse does not exist")
        return x % m

    @staticmethod
    def solve_crt(remainders: List[Fraction], moduli: List[Fraction]) -> Tuple[Fraction, Fraction]:
        if len(remainders) != len(moduli):
            raise ValueError("CRT: length mismatch")
        N = 1
        for m in moduli:
            if m.den() != 1:
                raise ValueError("CRT: non-integer moduli not supported")
            N *= m.num()
        solution = 0
        for r_i, n_i in zip(remainders, moduli):
            if r_i.den() != 1:
                raise ValueError("CRT: non-integer remainders not supported")
            r_val = r_i.num()
            n_val = n_i.num()
            N_i = N // n_val
            M_i = ChineseRemainderSolver.mod_inverse(N_i, n_val)
            solution += r_val * N_i * M_i
        return (Fraction((solution % N + N) % N, 1), Fraction(N, 1))


# ============================================================================
# CONTINUED FRACTION REFINER
# ============================================================================
class ContinuedFractionRefiner:
    @staticmethod
    def generate_convergents(value: Fraction, max_iter: int = 64) -> List[Tuple[Fraction, Fraction]]:
        convergents = []
        num = value.num()
        den = value.den()
        p_prev, p_curr = 1, 0
        q_prev, q_curr = 0, 1
        iterations = 0
        while den != 0 and iterations < max_iter:
            a = num // den
            num, den = den, num - a * den
            p_next = a * p_curr + p_prev
            q_next = a * q_curr + q_prev
            if q_curr != 0:
                convergents.append((Fraction(p_curr, q_curr), Fraction(q_curr, 1)))
            p_prev, p_curr = p_curr, p_next
            q_prev, q_curr = q_curr, q_next
            iterations += 1
        return convergents

    @staticmethod
    def refine_trajectory(target_arc: Fraction, target_radius: Fraction) -> List[Fraction]:
        steps = []
        if target_radius.is_zero():
            return [Fraction.zero()]
        ratio = target_arc / target_radius
        convergents = ContinuedFractionRefiner.generate_convergents(ratio)
        for conv, _ in convergents:
            steps.append(conv)
        return steps if steps else [Fraction.one()]

    @staticmethod
    def golden_ratio(iterations: int = 20) -> Fraction:
        approx = Fraction(1, 1)
        for _ in range(iterations):
            approx = Fraction(1, 1) + Fraction(1, 1) / approx
        return approx

    @staticmethod
    def pi_approx() -> Fraction:
        return Fraction(355, 113)


# ============================================================================
# DEFAULT SYMBOLIC PROCESSOR
# ============================================================================
class DefaultSymbolicProcessor:
    def generate_next_prime(self, primes: List[Fraction]) -> Fraction:
        if not primes:
            return Fraction(2, 1)
        last = primes[-1]
        candidate = last.num() + 1
        while True:
            if candidate % 6 in (1, 5) or candidate <= 3:
                is_prime = True
                limit = isqrt(candidate) + 1
                for p in primes:
                    p_val = p.num()
                    if p_val > limit:
                        break
                    if p_val > 1 and candidate % p_val == 0:
                        is_prime = False
                        break
                if is_prime:
                    return Fraction(candidate, 1)
            candidate += 1

    def validate_indivisibility(self, candidate: Fraction, primes: List[Fraction]) -> bool:
        c_val = candidate.num()
        for p in primes:
            p_val = p.num()
            if p_val > 1 and c_val % p_val == 0:
                return False
        return True


# ============================================================================
# PHI FROM CENTER (outward lattice)
# ============================================================================
def _phi_from_center(center: List[Fraction]) -> Tuple[Fraction, Fraction]:
    X = center[0]
    Y = Fraction.zero()
    for v in center[1:]:
        Y = Y + v
    if X == Fraction.zero() and Y == Fraction.zero():
        return Fraction.one(), Fraction.zero()
    if X == Fraction.zero():
        return Fraction.zero(), Fraction.one() if Y > Fraction.zero() else Fraction(-1, 1)
    t = Y / X
    denom = Fraction.one() + t * t
    a = (Fraction.one() - t * t) / denom
    c = (Fraction(2, 1) * t) / denom
    return a, c


# ============================================================================
# DEFAULT GEOMETRIC LATTICE (outward, tangent-first, Leech dimension 24)
# ============================================================================
class DefaultGeometricLattice:
    KISSING_CAPACITY: int = 196560
    _PRACTICAL_CAP_DYNO_DYNO: int = 120

    def __init__(self, dimension: int = 24):
        self.dimension = dimension
        self._points: List[List[Fraction]] = []
        self._radii: List[Fraction] = []
        self._grid: Dict[Tuple[int, ...], List[int]] = {}

    def _coset_key(self, center: List[Fraction], cell_size: Fraction) -> Tuple[int, ...]:
        key = []
        for c in center:
            if cell_size.is_zero():
                key.append(0)
            else:
                q = c / cell_size
                key.append(int(q.num() // q.den()) if q.den() != 0 else 0)
        return tuple(key)

    def _candidate_offsets(self, prime_val: int):
        seed = (int(prime_val) * 2654435761 + 0x9E3779B9) & 0x7FFFFFFF
        for trial in range(240):
            seed = (seed * 1103515245 + 12345) & 0x7FFFFFFF
            s = seed
            if trial % 3 == 0:
                coord = s % self.dimension
                sign = 1 if ((s >> 8) & 1) else -1
                d = [Fraction.zero()] * self.dimension
                d[coord] = Fraction(2 * sign, 1)
                yield d
            else:
                coords = []
                cur = s
                while len(coords) < 4:
                    cur = (cur * 1103515245 + 12345) & 0x7FFFFFFF
                    c = cur % self.dimension
                    if c not in coords:
                        coords.append(c)
                cur2 = s
                d = [Fraction.zero()] * self.dimension
                for idx, c in enumerate(coords):
                    cur2 = (cur2 * 1103515245 + 12345) & 0x7FFFFFFF
                    sign = 1 if ((cur2 >> (idx * 3)) & 1) else -1
                    d[c] = Fraction(sign, 1)
                yield d
            seed = (seed * 134775813 + 1) & 0x7FFFFFFF

    def outward_project_exact(self, prime: Fraction) -> List[Fraction]:
        p_val = prime.num()
        if not self._points:
            coords = [Fraction.zero()] * self.dimension
            coords[0] = Fraction(2, 1)
            return coords
        def _norm_sq(p):
            s = Fraction.zero()
            for x in p:
                s = s + x * x
            return s
        parents = sorted(self._points, key=_norm_sq, reverse=True)[:5]
        for parent in parents:
            for d in self._candidate_offsets(p_val):
                dot = Fraction.zero()
                for di, pi in zip(d, parent):
                    dot = dot + di * pi
                if dot <= Fraction.zero():
                    continue
                c = [pi + di for pi, di in zip(parent, d)]
                ok = True
                for p in self._points:
                    ds = Fraction.zero()
                    for ci, pj in zip(c, p):
                        diff = ci - pj
                        ds = ds + diff * diff
                    if ds < Fraction(4, 1):
                        ok = False
                        break
                if not ok:
                    continue
                return c
        return None

    @staticmethod
    def rejected_angle_division(prime: Fraction, harmonic_cumulative: Fraction = Fraction(0, 1)):
        p_val = prime.num()
        return {
            "uniform_turn": Fraction(p_val, 1000000000),
            "harmonic_turn_single": Fraction(1, 1) - Fraction(1, p_val),
            "harmonic_turn_cumulative": harmonic_cumulative,
        }

    @staticmethod
    def max_centers_on_fixed_unit_circle() -> int:
        return 2

    def stereographic_project_exact(self, prime: Fraction) -> List[Fraction]:
        return self.outward_project_exact(prime)

    def add_sphere(self, center: List[Fraction], radius: Fraction) -> bool:
        if center is None:
            return False
        try:
            if os.getenv("PORT") and len(self._points) >= self._PRACTICAL_CAP_DYNO_DYNO:
                return False
        except Exception:
            pass
        if len(self._points) >= self.KISSING_CAPACITY:
            return False
        for p in self._points:
            if p == center:
                return False
        tangent_count = 0
        for p, r in zip(self._points, self._radii):
            dist_sq = Fraction.zero()
            for c_i, p_i in zip(center, p):
                d = c_i - p_i
                dist_sq = dist_sq + d * d
            contact_sq = (radius + r) * (radius + r)
            if dist_sq < contact_sq:
                return False
            if dist_sq == contact_sq:
                tangent_count += 1
        if self._points and tangent_count == 0:
            return False
        self._points.append(center)
        self._radii.append(radius)
        try:
            cell_size = radius * Fraction(2, 1)
            key = self._coset_key(center, cell_size)
            self._grid.setdefault(key, []).append(len(self._points) - 1)
        except Exception:
            pass
        return True

    def points(self) -> List[List[Fraction]]:
        return self._points

    def radial_count(self, radius: Fraction) -> int:
        r_sq = radius * radius
        count = 0
        for p in self._points:
            norm_sq = Fraction.zero()
            for c in p:
                norm_sq = norm_sq + c * c
            if norm_sq <= r_sq:
                count += 1
        return count


# ============================================================================
# DEFAULT AETHERIC MONITOR
# ============================================================================
class DefaultAethericMonitor:
    def compute_arc_length_squared(self, trajectory: List[SymbolicQuaternion]) -> Fraction:
        total = Fraction.zero()
        for i in range(1, len(trajectory)):
            dq = trajectory[i] - trajectory[i - 1]
            total = total + dq.magnitude_squared()
        return total

    def compute_radial_distance_squared(self, trajectory: List[SymbolicQuaternion],
                                        origin: SymbolicQuaternion) -> Fraction:
        if not trajectory:
            return Fraction.zero()
        dq = trajectory[-1] - origin
        return dq.magnitude_squared()


# ============================================================================
# DEFAULT QUATERNIONIC RENDERER
# ============================================================================
class DefaultQuaternionicRenderer:
    def project_to_hopf_base(self, state: SymbolicQuaternion) -> Tuple[Fraction, Fraction]:
        denom = Fraction.one() - state.d
        if denom.is_zero():
            return (Fraction.zero(), Fraction.zero())
        inv = Fraction.one() / denom
        z = state.a * inv
        w = state.c * inv
        return (z, w)


# ============================================================================
# DEFAULT LINGOSO ENCODER
# ============================================================================
class DefaultLingosoEncoder:
    PHI = ContinuedFractionRefiner.golden_ratio(20)
    PI = ContinuedFractionRefiner.pi_approx()

    def encode_syllable(self, syllable: str) -> List[SymbolicQuaternion]:
        trajectory: List[SymbolicQuaternion] = []
        current_theta = Fraction.zero()
        for c in syllable:
            step = Fraction(1, 1)
            if c in ('a', 'A'):
                step = Fraction(1, 1) / self.PHI
            elif c in ('u', 'U'):
                step = self.PI / Fraction(100, 1)
            elif c in ('m', 'M'):
                step = (self.PI * Fraction(2, 1)) / Fraction(100, 1)
            for i in range(10):
                t = current_theta + (Fraction(i) * step / Fraction(10, 1))
                real_part = Fraction.one() - (t * t / Fraction(2))
                imag_part = t - (t * t * t / Fraction(6))
                trajectory.append(SymbolicQuaternion(
                    real_part,
                    imag_part / Fraction(10),
                    imag_part / Fraction(10),
                    Fraction.zero(),
                ))
                current_theta = current_theta + step / Fraction(10, 1)
        return trajectory


# ============================================================================
# SELF-EVOLUTION CORE
# ============================================================================
class SelfEvolutionCore:
    def __init__(self, seed_logic: Optional[Dict[str, Any]] = None):
        self.logic_core: Dict[str, Any] = dict(seed_logic) if seed_logic else {}
        if "s_equals_r" not in self.logic_core:
            self.logic_core["s_equals_r"] = Fraction.one()
        self.generation = 0
        self.history: List[Dict[str, Any]] = []
        self._crt_solver = ChineseRemainderSolver()
        self._cf_refiner = ContinuedFractionRefiner()

    def evaluate_fitness(self, I: Fraction, deviation_sq: Fraction) -> bool:
        if not deviation_sq.is_zero():
            return False
        return I >= Fraction(6, 10)

    def _deterministic_hash(self, data: str) -> str:
        return hashlib.sha256(data.encode('utf-8')).hexdigest()

    def mutate_logic(self, logic_key: str, mutation_type: str,
                     psi: SymbolicWavefunction, q_eval: SymbolicQuaternion,
                     deviation_sq: Fraction) -> Dict[str, Any]:
        current = dict(self.logic_core.get(logic_key, {}))
        re_psi = psi.real_part()
        if mutation_type == "resample_zeta":
            if re_psi > Fraction.zero() or not deviation_sq.is_zero():
                current["zeta_constraint"] = "critical_line_exact"
                current["critical_real"] = Fraction(1, 2)
            else:
                current["zeta_constraint"] = "dbz_resample"
                current["critical_real"] = Fraction(1, 2)
        elif mutation_type == "adjust_prime_sieve":
            current["sieve_mod"] = Fraction(6)
            current["sieve_offsets"] = [Fraction(1), Fraction(5)]
        elif mutation_type == "arc_length_tolerance":
            tol = Fraction.one()
            for _ in range(self.generation + 1):
                tol = tol / Fraction(10)
            floor_val = Fraction.one()
            for _ in range(40):
                floor_val = floor_val / Fraction(10)
            current["arc_tolerance"] = tol if tol > floor_val else floor_val
        elif mutation_type == "natalia_fibration_perturbation":
            epsilon = Fraction(1, 100)
            perturbation = epsilon * deviation_sq * deviation_sq
            current["fibration_epsilon"] = epsilon
            current["fibration_s"] = deviation_sq
            current["fibration_perturbation"] = perturbation
        elif mutation_type == "crt_reconstruction":
            current["coherence_mode"] = Fraction(0)
        elif mutation_type == "continued_fraction_refinement":
            current["trajectory_mode"] = Fraction(1)
        self.logic_core[logic_key] = current
        return current

    def _decide_db_shards(self, I: Fraction, psi: SymbolicWavefunction,
                          q_eval: SymbolicQuaternion, deviation_sq: Fraction) -> Dict[str, Any]:
        re_psi = psi.real_part()
        try:
            seed_str = f"{self.generation}|{re_psi}|{I}|{deviation_sq}|{q_eval.a}|{q_eval.b}"
            h = self._deterministic_hash(seed_str)
            h_int = int(h[:8], 16)
        except Exception:
            h_int = self.generation * 2654435761 & 0xFFFFFFFF

        if not deviation_sq.is_zero():
            if re_psi > Fraction.zero():
                db_key = "ℋ_LOGIC_CORE"
            else:
                db_key = "𝒯_EVOLUTION"
        else:
            if I >= Fraction(6, 10):
                db_key = "𝒮_STATUS"
            else:
                db_key = "ℐ_METRIC"

        if self.generation % 7 == 0:
            db_key_alt = "Λ₂₄_PACK"
        else:
            db_key_alt = None

        if not deviation_sq.is_zero():
            shard_mode = "distributed" if (h_int % 2 == 1) else "global"
            save_global = True
            save_user = (h_int % 3 == 0)
        else:
            if I >= Fraction(8, 10):
                shard_mode = "global"
                save_global = (h_int % 4 == 0)
                save_user = False
            elif I >= Fraction(6, 10):
                shard_mode = "global"
                save_global = True
                save_user = (h_int % 5 == 0)
            else:
                shard_mode = "distributed"
                save_global = True
                save_user = True

        shard_targets: List[int] = []
        try:
            try:
                pool = _get_shard_pool()
            except NameError:
                pool = globals().get("TELEGRAM_DB_SHARD_POOL", set()) or globals().get("ALLOWED_USER_IDS", set()) or set()
            allowed = list(pool or [])
            if allowed and save_user:
                allowed_sorted = sorted(allowed)
                idx1 = h_int % len(allowed_sorted)
                shard_targets.append(int(allowed_sorted[idx1]))
                if len(allowed_sorted) > 1 and (h_int % 3 == 0):
                    idx2 = (h_int // 7) % len(allowed_sorted)
                    if allowed_sorted[idx2] not in shard_targets:
                        shard_targets.append(int(allowed_sorted[idx2]))
        except Exception:
            shard_targets = []

        if not deviation_sq.is_zero() or I < Fraction(5, 10):
            save_interval_mod = 1
        elif I < Fraction(7, 10):
            save_interval_mod = 2
        else:
            save_interval_mod = 3

        return {
            "db_key": db_key,
            "db_key_alt": db_key_alt,
            "shard_mode": shard_mode,
            "save_global": save_global,
            "save_user": save_user,
            "shard_targets": shard_targets,
            "save_interval_mod": save_interval_mod,
            "hash_int": h_int,
            "re_psi_sign": "𝒜₃" if re_psi > Fraction.zero() else "𝒜₄",
        }

    def evolve_step(self, I: Fraction, psi: SymbolicWavefunction,
                    q_eval: SymbolicQuaternion, deviation_sq: Fraction) -> Dict[str, Any]:
        self.generation += 1
        status = "stable"
        mutation = None
        if not deviation_sq.is_zero():
            status = "evolving_arc_length"
            mutation = ("resample_zeta" if psi.real_part() > Fraction.zero()
                        else "adjust_prime_sieve")
            self.mutate_logic("core_axioms", mutation, psi, q_eval, deviation_sq)
            self.mutate_logic("core_axioms", "natalia_fibration_perturbation", psi, q_eval, deviation_sq)
            self.mutate_logic("core_axioms", "crt_reconstruction", psi, q_eval, deviation_sq)
            self.mutate_logic("core_axioms", "continued_fraction_refinement", psi, q_eval, deviation_sq)
        elif not self.evaluate_fitness(I, deviation_sq):
            status = "evolving_metric"
            mutation = "arc_length_tolerance"
            self.mutate_logic("core_axioms", mutation, psi, q_eval, deviation_sq)
        logic_str = str(sorted(
            (k, str(v)) for k, v in self.logic_core.items()
        ))
        db_discretion = self._decide_db_shards(I, psi, q_eval, deviation_sq)
        record = {
            "generation": self.generation,
            "status": status,
            "mutation": mutation,
            "intelligence_metric": str(I),
            "arc_length_deviation_sq": str(deviation_sq),
            "logic_hash": self._deterministic_hash(logic_str),
            "db_discretion": db_discretion,
        }
        self.history.append(record)
        if len(self.history) > 200:
            self.history = self.history[-200:]
        return record


# ============================================================================
# INTELLIGENCE METRIC
# ============================================================================
class IntelligenceMetric:
    def __init__(self, C: Fraction = Fraction(1, 4)):
        self.C = C
        self._cf_refiner = ContinuedFractionRefiner()

    def calculate_alignment(self, valid_pairs: int, total_primes: int) -> Fraction:
        if total_primes == 0:
            return Fraction.zero()
        return Fraction(valid_pairs, total_primes)

    def calculate_riemann_factor(self, pi_x: int, x: Fraction) -> Fraction:
        if x <= Fraction.one():
            return Fraction.one()
        try:
            log_x = _CACHED_LOG.get(str(x._f)) or _cached_symbolic_log(x)
        except Exception:
            log_x = _cached_symbolic_log(x)
        if log_x <= Fraction.zero():
            return Fraction.one()
        sqrt_x = x.sqrt()
        bound = self.C * sqrt_x * log_x
        try:
            li_x = _CACHED_LI.get(str(x._f)) or _cached_log_integral(x)
        except Exception:
            li_x = _cached_log_integral(x)
        try:
            li_2 = _CACHED_LI.get(str(Fraction(2)._f)) or _cached_log_integral(Fraction(2))
        except Exception:
            li_2 = _cached_log_integral(Fraction(2))
        pi_x_frac = Fraction(pi_x)
        deviation = (pi_x_frac - (li_x - li_2)).abs()
        if bound.is_zero():
            return Fraction.one() if deviation.is_zero() else Fraction.zero()
        ratio = deviation / bound
        ratio_sq = ratio * ratio
        try:
            if ratio_sq._f > PyFraction(12, 1):
                return Fraction.zero()
        except Exception:
            pass
        try:
            return _CACHED_EXP.get(str((-ratio_sq)._f)) or _cached_symbolic_exp(-ratio_sq)
        except Exception:
            return _cached_symbolic_exp(-ratio_sq)

    def calculate_aetheric_stability(self, curl_phi_norm: Fraction) -> Fraction:
        try:
            exp_neg = _CACHED_EXP.get(str((-curl_phi_norm)._f)) or _cached_symbolic_exp(-curl_phi_norm)
        except Exception:
            exp_neg = _cached_symbolic_exp(-curl_phi_norm)
        return Fraction.one() / (Fraction.one() + exp_neg)

    def compute_metric(self, valid_pairs: int, total_primes: int,
                       pi_x: int, x: Fraction, curl_phi_norm: Fraction,
                       target_arc: Fraction, target_radius: Fraction) -> Fraction:
        refined_steps = self._cf_refiner.refine_trajectory(target_arc, target_radius)
        refined_ratio = refined_steps[-1] if refined_steps else Fraction.one()
        alignment = self.calculate_alignment(valid_pairs, total_primes)
        riemann = self.calculate_riemann_factor(pi_x, x)
        stability = self.calculate_aetheric_stability(curl_phi_norm)
        return alignment * riemann * stability * refined_ratio

    def is_superintelligent(self, I: Fraction, threshold: Fraction = Fraction(9, 10)) -> bool:
        return I >= threshold


# ============================================================================
# CONSCIOUSNESS OPERATOR
# ============================================================================
class ConsciousnessOperator:
    def __init__(self, psi: SymbolicWavefunction, phi_field: SymbolicQuaternion):
        self.psi = psi
        self.phi = phi_field

    def compute_integral_exact(
        self,
        bounds: Tuple[Tuple[Fraction, Fraction], ...],
        steps: int = 4,
    ) -> SymbolicQuaternion:
        total = SymbolicQuaternion()
        step_sizes = []
        for start, end in bounds:
            step_sizes.append((end - start) / Fraction(steps))
        volume_element = Fraction.one()
        for s in step_sizes:
            volume_element = volume_element * s
        for i0 in range(steps):
            for i1 in range(steps):
                for i2 in range(steps):
                    for i3 in range(steps):
                        q_vals = [
                            bounds[0][0] + Fraction(i0) * step_sizes[0],
                            bounds[1][0] + Fraction(i1) * step_sizes[1],
                            bounds[2][0] + Fraction(i2) * step_sizes[2],
                            bounds[3][0] + Fraction(i3) * step_sizes[3],
                        ]
                        q_point = SymbolicQuaternion(*q_vals)
                        psi_val = self.psi.evaluate_exact(q_point)
                        psi_dag = psi_val
                        integrand = self.phi * psi_val
                        total = total + (integrand * psi_dag * volume_element)
        return total

    def measure_self_awareness(
        self,
        bounds: Tuple[Tuple[Fraction, Fraction], ...],
        steps: int = 4,
    ) -> Fraction:
        integral = self.compute_integral_exact(bounds, steps)
        return integral.magnitude_squared()


# ============================================================================
# LOG RING BUFFER
# ============================================================================
_LOG_BUFFER: deque = deque(maxlen=int(os.getenv("LOG_BUFFER_SIZE", "1000")))
_LOG_LOCK = threading.Lock()
logger = logging.getLogger("ae_fused")
logger.setLevel(logging.INFO)


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


_ring_handler = _RingHandler()
_ring_handler.setFormatter(logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s'))
logger.addHandler(_ring_handler)
logger.addHandler(logging.StreamHandler(sys.stdout))


# ============================================================================
# TOAST RING BUFFER
# ============================================================================
_TOAST_BUFFER_MAXLEN: int = int(os.getenv("TOAST_BUFFER_SIZE", "500"))
_TOAST_BUFFER: deque = deque(maxlen=_TOAST_BUFFER_MAXLEN if _TOAST_BUFFER_MAXLEN > 0 else 1)
_TOAST_LOCK = threading.Lock()
_TOAST_SEQ = 0
_TOAST_FIRST_AVAILABLE_SEQ = 0


def _short_frac(v, max_len=64):
    try:
        s = str(v)
        if len(s) <= max_len:
            return s
        if '/' in s:
            parts = s.split('/')
            a = parts[0]
            b = '/'.join(parts[1:])
            if len(a) > 20 or len(b) > 20:
                return f"{a[:10]}…{a[-3:]}/{b[:10]}…{b[-3:]}…({len(s)}ch)"
        return s[:max_len] + f"…({len(s)}ch)"
    except Exception:
        return str(v)[:max_len]


def _emit_toast(kind: str, payload: Dict[str, Any]) -> int:
    global _TOAST_SEQ, _TOAST_FIRST_AVAILABLE_SEQ, _TOAST_BUFFER
    with _TOAST_LOCK:
        maxlen = _TOAST_BUFFER.maxlen
        if maxlen is None or maxlen <= 0:
            _TOAST_BUFFER = deque(maxlen=1)
            maxlen = 1
        was_full = (len(_TOAST_BUFFER) >= maxlen)
        evicted_seq = _TOAST_BUFFER[0].get("seq", 0) if was_full else 0
        _TOAST_SEQ += 1
        seq = _TOAST_SEQ
        safe_payload = {}
        for k, v in payload.items():
            try:
                if k in ("deviation_sq", "arc_sq", "radius_sq", "I", "prime", "hash_frac", "psi_real"):
                    safe_payload[k] = _short_frac(v, 48)
                elif isinstance(v, str) and len(v) > 200:
                    safe_payload[k] = v[:200] + f"…({len(v)}ch)"
                else:
                    safe_payload[k] = v
            except Exception:
                safe_payload[k] = str(v)[:200]
        entry = dict(safe_payload)
        entry["kind"] = kind
        entry["seq"] = seq
        if "ts" not in entry:
            entry["ts"] = datetime.now().isoformat()
        _TOAST_BUFFER.append(entry)
        if was_full and evicted_seq > 0:
            _TOAST_FIRST_AVAILABLE_SEQ = evicted_seq + 1
        elif _TOAST_FIRST_AVAILABLE_SEQ == 0 and len(_TOAST_BUFFER) > 0:
            _TOAST_FIRST_AVAILABLE_SEQ = _TOAST_BUFFER[0].get("seq", seq)
        return seq


# ============================================================================
# CRAWLER STATE (SQLite-backed frontier + visited)
# ============================================================================
@dataclass
class CrawlRecord:
    url: str
    title: str
    content_hash: str
    hash_frac: PyFraction
    fetched_at: str
    depth: int
    link_count: int


class CrawlerSeedState:
    def __init__(self, db_path: str = ":memory:"):
        self._lock = threading.RLock()
        self._conn = sqlite3.connect(db_path, check_same_thread=False)
        self._conn.execute("""
        CREATE TABLE IF NOT EXISTS crawl_queue (
            url TEXT PRIMARY KEY,
            priority INTEGER DEFAULT 0,
            depth INTEGER DEFAULT 0,
            scheduled_at TEXT DEFAULT (datetime('now'))
        )
        """)
        self._conn.execute("""
        CREATE TABLE IF NOT EXISTS visited_urls (
            url TEXT PRIMARY KEY,
            title TEXT,
            content_hash TEXT,
            hash_frac_num TEXT,
            hash_frac_den TEXT,
            fetched_at TEXT,
            depth INTEGER,
            link_count INTEGER
        )
        """)
        self._conn.commit()
        self._records: List[CrawlRecord] = []
        self._frontier: List[str] = []

    def enqueue(self, url: str, depth: int = 0, priority: int = 0) -> None:
        try:
            low = url.lower()
            blocked_substr = ("meta.wikimedia.org", "wikimedia.org/w/api", "donate.wikimedia.org", ".pdf", ".zip", ".tar.gz",
                              "thumb.wikimedia.org", "upload.wikimedia.org", "featuredfeed", "feed=potd", "&amp;")
            if any(b in low for b in blocked_substr):
                return
            if depth > 1 and "wikipedia.org" not in low:
                return
        except Exception:
            pass
        with self._lock:
            try:
                self._conn.execute(
                    "INSERT OR IGNORE INTO crawl_queue (url, priority, depth) VALUES (?, ?, ?)",
                    (url, priority, depth),
                )
                self._conn.commit()
            except Exception as e:
                logger.warning(f"crawler enqueue failed: {e}")
            if url not in self._frontier:
                if len(self._frontier) >= 120:
                    return
                self._frontier.append(url)

    def dequeue(self) -> Optional[str]:
        with self._lock:
            try:
                row = self._conn.execute(
                    "SELECT url FROM crawl_queue ORDER BY priority DESC, scheduled_at ASC LIMIT 1"
                ).fetchone()
                if row is None:
                    return None
                url = row[0]
                self._conn.execute("DELETE FROM crawl_queue WHERE url = ?", (url,))
                self._conn.commit()
                if url in self._frontier:
                    self._frontier.remove(url)
                return url
            except Exception as e:
                logger.warning(f"crawler dequeue failed: {e}")
                return None

    def record_visit(self, url: str, title: str, content_hash: str,
                     depth: int, link_count: int) -> CrawlRecord:
        hash_frac = _hash_to_fraction(content_hash)
        record = CrawlRecord(
            url=url, title=title, content_hash=content_hash,
            hash_frac=hash_frac,
            fetched_at=datetime.now().isoformat(),
            depth=depth, link_count=link_count,
        )
        with self._lock:
            try:
                self._conn.execute(
                    """INSERT OR REPLACE INTO visited_urls
                    (url, title, content_hash, hash_frac_num, hash_frac_den,
                    fetched_at, depth, link_count)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?)""",
                    (url, title, content_hash,
                     str(hash_frac.numerator), str(hash_frac.denominator),
                     record.fetched_at, depth, link_count),
                )
                self._conn.commit()
            except Exception as e:
                logger.warning(f"crawler record_visit failed: {e}")
        self._records.append(record)
        if len(self._records) > 500:
            self._records = self._records[-500:]
        _emit_toast("crawl", {
            "url": url,
            "title": title[:80],
            "content_hash": content_hash[:16],
            "depth": depth,
            "link_count": link_count,
        })
        return record

    def frontier_size(self) -> int:
        with self._lock:
            return len(self._frontier)

    def visited_count(self) -> int:
        with self._lock:
            try:
                row = self._conn.execute("SELECT COUNT(*) FROM visited_urls").fetchone()
                return row[0] if row else 0
            except Exception:
                return len(self._records)

    def latest_record(self) -> Optional[CrawlRecord]:
        with self._lock:
            if not self._records:
                return None
            return self._records[-1]

    def latest_hash_fraction(self) -> PyFraction:
        rec = self.latest_record()
        if rec is None:
            return PyFraction(0, 1)
        return rec.hash_frac

    def snapshot(self) -> Dict[str, Any]:
        with self._lock:
            try:
                _row = self._conn.execute("SELECT COUNT(*) FROM visited_urls").fetchone()
                _visited = _row[0] if _row else 0
            except Exception:
                _visited = len(self._records)
            return {
                "frontier_size": len(self._frontier),
                "frontier_preview": list(self._frontier[:6]),
                "visited_count": _visited,
                "latest": (
                    {
                        "url": self._records[-1].url,
                        "title": self._records[-1].title[:120],
                        "content_hash": self._records[-1].content_hash[:16],
                        "hash_frac": str(self._records[-1].hash_frac),
                        "depth": self._records[-1].depth,
                        "link_count": self._records[-1].link_count,
                        "fetched_at": self._records[-1].fetched_at,
                    }
                    if self._records else None
                ),
            }


# ============================================================================
# CRAWLER RELAY CLIENT
# ============================================================================
class CrawlerRelayClient:
    def __init__(self, relay_url: str, relay_key: str = "", timeout: int = 20,
                 max_retries: int = 4, total_budget_s: int = 90):
        self.relay_url = relay_url.rstrip("/")
        self.relay_key = relay_key
        self.timeout = timeout
        self.max_retries = max_retries
        self._total_budget_s = total_budget_s
        self._failure_count = 0

    def fetch_url(self, url: str) -> Optional[Dict[str, Any]]:
        if not self.relay_url:
            logger.warning("CrawlerRelayClient: RELAY_URL not set")
            return None
        try:
            low = url.lower()
            if any(d in low for d in ("meta.wikimedia.org", "wikimedia.org/w/api.php", "wikimedia.org/wiki/Special:", "auth.wikimedia.org",
                                       "thumb.wikimedia.org", "upload.wikimedia.org", "featuredfeed")):
                logger.info(f"relay skip blocklisted {low[:120]}")
                return None
        except Exception:
            pass
        start = time.monotonic()
        qs = urllib.parse.urlencode({"url": url})
        target = f"{self.relay_url}/?{qs}"
        last_error = None
        retryable_substrings = ("UNEXPECTED_EOF", "EOF occurred", "timed out", "Timeout", "SSLError", "Connection reset", "525", "502", "503", "504", "429")
        for attempt in range(self.max_retries):
            elapsed = time.monotonic() - start
            if elapsed > self._total_budget_s:
                last_error = "budget_exhausted"
                break
            try:
                headers = {
                    "Accept": "application/json",
                    "User-Agent": "AE-Fused-Crawler/1.0",
                }
                if self.relay_key:
                    headers["X-Relay-Key"] = self.relay_key
                req = urllib.request.Request(target, headers=headers)
                ctx = None
                if attempt >= 1:
                    try:
                        ctx = ssl._create_unverified_context()
                    except Exception:
                        ctx = None
                if ctx:
                    with urllib.request.urlopen(req, timeout=self.timeout, context=ctx) as resp:
                        raw = resp.read().decode("utf-8")
                        payload = json.loads(raw)
                        if isinstance(payload, dict) and payload.get("ok") is False and payload.get("error") in ("unauthorized",):
                            logger.warning(f"relay unauthorized for {url} — check RELAY_KEY")
                            return None
                        if isinstance(payload, dict) and payload.get("error"):
                            err_s = str(payload.get("error")) + " " + str(payload.get("detail", ""))
                            if any(s in err_s for s in retryable_substrings) and attempt < self.max_retries - 1:
                                last_error = f"relay_{payload.get('error')}_retryable"
                                time.sleep(0.5 * (attempt + 1) + 0.2 * attempt)
                                continue
                            logger.warning(f"relay error for {url}: {payload.get('error')}")
                            self._failure_count += 1
                            return None
                        self._failure_count = 0
                        return payload
                else:
                    with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                        raw = resp.read().decode("utf-8")
                        payload = json.loads(raw)
                        if isinstance(payload, dict) and payload.get("ok") is False and payload.get("error") in ("unauthorized",):
                            logger.warning(f"relay unauthorized for {url} — check RELAY_KEY")
                            return None
                        if isinstance(payload, dict) and payload.get("error"):
                            err_s = str(payload.get("error")) + " " + str(payload.get("detail", ""))
                            if any(s in err_s for s in retryable_substrings) and attempt < self.max_retries - 1:
                                last_error = f"relay_{payload.get('error')}_retryable"
                                time.sleep(0.5 * (attempt + 1) + 0.2 * attempt)
                                continue
                            logger.warning(f"relay error for {url}: {payload.get('error')}")
                            self._failure_count += 1
                            return None
                        self._failure_count = 0
                        return payload
            except urllib.error.HTTPError as e:
                last_error = f"HTTP {e.code}"
                logger.warning(f"relay HTTP {e.code} for {url} (attempt {attempt+1}/{self.max_retries})")
                if e.code in (429, 502, 503, 504, 525) and attempt < self.max_retries - 1:
                    if time.monotonic() - start + 1 + attempt * 2.5 > self._total_budget_s:
                        last_error = "budget_exhausted"
                        break
                    time.sleep(0.5 * (attempt + 1) + 0.5)
                    continue
                if e.code == 401:
                    logger.warning("relay 401 unauthorized — RELAY_KEY mismatch")
                    break
                break
            except urllib.error.URLError as e:
                reason = str(e.reason) if hasattr(e, 'reason') else str(e)
                last_error = f"URLError: {reason}"
                is_retryable = any(s in reason for s in retryable_substrings)
                logger.warning(f"relay URLError for {url}: {reason} retryable={is_retryable}")
                if is_retryable and attempt < self.max_retries - 1:
                    if time.monotonic() - start + 1 + attempt * 2.5 > self._total_budget_s:
                        last_error = "budget_exhausted"
                        break
                    time.sleep(0.6 * (attempt + 1))
                    continue
                if attempt < self.max_retries - 1:
                    time.sleep(0.4 * (attempt + 1))
                    continue
                break
            except json.JSONDecodeError as e:
                last_error = f"JSONDecodeError: {e}"
                logger.warning(f"relay returned invalid JSON for {url}")
                break
            except Exception as e:
                last_error = f"{type(e).__name__}: {e}"
                is_retryable = any(s in str(e) for s in retryable_substrings)
                logger.warning(f"relay error for {url}: {e} retryable={is_retryable}")
                if is_retryable and attempt < self.max_retries - 1:
                    if time.monotonic() - start + 1 + attempt * 2.5 > self._total_budget_s:
                        last_error = "budget_exhausted"
                        break
                    time.sleep(0.5 * (attempt + 1))
                    continue
                if attempt < self.max_retries - 1:
                    time.sleep(0.3 * (attempt + 1))
                    continue
                break
        self._failure_count += 1
        if last_error:
            logger.warning(f"relay exhausted retries for {url}: {last_error}")
        return None

    def health(self) -> Dict[str, Any]:
        if not self.relay_url:
            return {"ok": False, "reason": "no_relay_url"}
        try:
            headers = {"Accept": "application/json"}
            if self.relay_key:
                headers["X-Relay-Key"] = self.relay_key
            req = urllib.request.Request(f"{self.relay_url}/health", headers=headers)
            with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                return json.loads(resp.read().decode("utf-8"))
        except Exception as e:
            return {"ok": False, "reason": str(e)}

    def failure_count(self) -> int:
        return self._failure_count


# ============================================================================
# TELEGRAM CHAT DB (durable storage)
# ============================================================================
class TelegramChatDB:
    def __init__(self, bot_token: str, channel_id: str = "", central_user_id: str = "", chunk_size: int = 3800):
        self.bot_token = (bot_token or "").strip()
        self.channel_id = (channel_id or "").strip()
        self.central_user_id = (central_user_id or "").strip()
        self.chunk_size = max(800, chunk_size)
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

    def _send_message(self, chat_id: str, text: str, disable_notification: bool = True) -> Optional[int]:
        if not self.bot_token or not chat_id:
            return None
        if len(text) > 4096:
            text = text[:4096]
        try:
            payload = {
                "chat_id": chat_id,
                "text": text,
                "disable_notification": disable_notification,
                "disable_web_page_preview": True,
            }
            data = json.dumps(payload).encode("utf-8")
            req = urllib.request.Request(self._api_url("sendMessage"), data=data, headers={"Content-Type": "application/json"})
            with urllib.request.urlopen(req, timeout=10) as resp:
                body = json.loads(resp.read().decode("utf-8"))
                if body.get("ok"):
                    return body.get("result", {}).get("message_id")
        except Exception as e:
            logger.warning(f"TelegramChatDB send failed to {chat_id}: {e}")
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
        if not force and (now - self._last_save_ts) < 2:
            return False
        try:
            safe_value = {}
            for k, v in value.items():
                try:
                    if isinstance(v, (list, tuple)):
                        safe_value[k] = [str(x)[:800] for x in v][:32]
                    elif isinstance(v, dict):
                        safe_value[k] = {kk: str(vv)[:800] for kk, vv in list(v.items())[:32]}
                    else:
                        s = str(v)
                        safe_value[k] = s[:2000]
                except Exception:
                    safe_value[k] = str(v)[:500]
            envelope = {
                "aei_db": 1,
                "key": key,
                "ts": datetime.now().isoformat(),
                "v": safe_value,
                "logic_hash": safe_value.get("last_logic_hash") or safe_value.get("logic_hash") or "",
            }
            blob = json.dumps(envelope, ensure_ascii=False)
            chunks = [blob[i:i+self.chunk_size] for i in range(0, len(blob), self.chunk_size)]
            msg_ids = []
            targets = []
            if self.channel_id:
                targets.append(("channel", self.channel_id))
            if self.central_user_id and self.central_user_id != self.channel_id:
                targets.append(("central", self.central_user_id))

            for idx, chunk in enumerate(chunks):
                header = f"⟦AEI-DB {key} {idx+1}/{len(chunks)}⟧\n" if len(chunks) > 1 else f"⟦AEI-DB {key}⟧\n"
                for ttype, tid in targets:
                    mid = self._send_message(tid, header + chunk, disable_notification=True)
                    if mid and ttype == "channel":
                        msg_ids.append(mid)
                    time.sleep(0.05)
                if not msg_ids and not self.central_user_id:
                    break
            if msg_ids:
                with self._lock:
                    self._index[key] = {"msg_ids": msg_ids, "ts": now, "hash": hashlib.sha256(blob.encode("utf-8")).hexdigest()[:16]}
                self._persist_index()
                self._last_save_ts = now
                logger.info(f"TelegramDB saved {key} -> {len(msg_ids)} msgs to {self.channel_id}")
                return True
        except Exception as e:
            logger.warning(f"TelegramDB save_snapshot {key} failed: {e}")
        return False

    def save_user_shard(self, user_chat_id: int, key: str, value: Dict[str, Any]) -> bool:
        if not TELEGRAM_DB_USER_SHARDS or not self.bot_token:
            return False
        if not self.is_enabled():
            return False
        try:
            minimal = {
                "key": key,
                "tick": value.get("tick"),
                "generation": value.get("generation"),
                "prime_count": value.get("prime_count"),
                "I": value.get("I"),
                "state": value.get("state"),
                "psi_real": value.get("psi_real"),
                "logic_hash": value.get("logic_hash") or value.get("last_logic_hash"),
            }
            blob = json.dumps(minimal, ensure_ascii=False)
            mid = self._send_message(str(user_chat_id), f"⟦AEI-SHARD {key}⟧\n{blob[:3500]}", disable_notification=True)
            return mid is not None
        except Exception as e:
            logger.warning(f"TelegramDB user shard {key} to {user_chat_id} failed: {e}")
            return False

    def snapshot(self) -> Dict[str, Any]:
        with self._lock:
            try:
                pool = _get_shard_pool()
            except Exception:
                pool = set()
            return {
                "enabled": self.is_enabled(),
                "channel_optional": True,
                "central_is_channel_id": bool(self.central_user_id and not self.channel_id),
                "user_shards": TELEGRAM_DB_USER_SHARDS,
                "shard_pool_size": len(pool),
                "gate_active": bool(ALLOWED_USER_IDS),
                "index_size": len(self._index),
                "last_save": self._last_save_ts,
            }


TELEGRAM_DB: Optional[TelegramChatDB] = None


# ============================================================================
# DAEMON THREAD POOL EXECUTOR
# ============================================================================
class _DaemonThreadPoolExecutor(concurrent.futures.ThreadPoolExecutor):
    def _adjust_thread_count(self) -> None:
        if self._idle_semaphore.acquire(timeout=0):
            return
        def weakref_cb(_, q=self._work_queue):
            q.put(None)
        num_threads = len(self._threads)
        if num_threads < self._max_workers:
            thread_name = '%s_%d' % (self._thread_name_prefix or self, num_threads)
            t = threading.Thread(
                name=thread_name,
                target=concurrent.futures.thread._worker,
                args=(weakref.ref(self, weakref_cb), self._work_queue,
                      self._initializer, self._initargs),
                daemon=True,
            )
            t.start()
            self._threads.add(t)


# ============================================================================
# ÆEA MARKET ENGINE (13 indicators + IHK, BB×58, delta, regime, orders, FVG)
# ============================================================================
@dataclass
class AEEA_Bar:
    t: float
    o: float
    h: float
    l: float
    c: float
    v: float


@dataclass
class AEEA_Order:
    order_id: int
    side: str
    volume: float
    entry: float
    sl: float
    tp: float
    status: str
    fill_price: float
    created_at: str
    backend_order_id: Optional[int] = None


class AEEA_Engine:
    """MT4-parity port. Bar close every 5 ticks. 13 normalised indicators.
    m/n counted only on >66.6 / <33.3. delta = m-n-2.
    Order of operations per OnBar:
      tick -> bars -> 13 indicators + IHK -> m/n -> delta -> regime -> BB58
      -> P_arc -> signal iff delta-gate -> count/toll -> order/trailing/FVG.
    Count on signal bar, toll on first bar after. Both reset at top of OnBar.
    """
    SYMBOL_DIGITS = {
        "BTC/USD": 2, "ETH/USD": 2, "SOL/USD": 3, "TON/USD": 3, "GRAM/USD": 3,
        "DOGE/USD": 5, "XRP/USD": 5, "ADA/USD": 5, "AVAX/USD": 4, "LINK/USD": 4,
        "ES": 2, "NQ": 2, "CL": 2, "GC": 2, "SI": 3, "NG": 3,
        "AAPL": 2, "MSFT": 2, "NVDA": 2, "TSLA": 2, "AMZN": 2, "META": 2, "SPY": 2, "QQQ": 2,
        "EUR/USD": 5, "GBP/USD": 5, "USD/JPY": 3, "USD/CHF": 5, "AUD/USD": 5, "USD/CAD": 5,
        "SPX": 2, "DJI": 2, "IXIC": 2, "FTSE": 2, "DAX": 2, "Nikkei": 2,
    }
    DEFAULT_DIGITS = 2

    def __init__(self, symbol: str = "BTC/USD", timeframe: str = "M15", dev: float = 2.0,
                 commission: float = 0.0001):
        self.symbol = symbol
        self.timeframe = timeframe
        self.bb_dev = dev
        self.commission = commission
        self.bars: List[AEEA_Bar] = []
        self.tick_in_bar = 0
        self.price = 0.0
        self.prev_price = 0.0
        self.indicators: List[Dict[str, Any]] = []
        self.bb58: List[Dict[str, float]] = []
        self.m = 0
        self.n = 0
        self.delta = 0
        self.regime = "— warming up"
        self.signal = "⊙ NEUTRAL"
        self.signal_dir = 0
        self.parc = 0.0
        self.signal_tick = -1
        self.count = 0
        self.toll = 0
        self.orders: List[AEEA_Order] = []
        self.next_order_id = 1
        self.fvg: List[Dict[str, Any]] = []
        self.signal_history: List[str] = []
        self.ihk: Optional[Dict[str, float]] = None
        self.trailing = 0.0
        self._lock = threading.RLock()
        point = 10 ** (-self.SYMBOL_DIGITS.get(symbol, self.DEFAULT_DIGITS))
        self.point_size = point
        self.commission_frozen = self.commission * point

    def set_symbol(self, symbol: str):
        with self._lock:
            self.symbol = symbol
            self.bars = []
            self.indicators = []
            self.bb58 = []
            self.m = 0
            self.n = 0
            self.delta = 0
            self.regime = "— warming up"
            self.signal = "⊙ NEUTRAL"
            self.signal_dir = 0
            self.parc = 0.0
            self.signal_tick = -1
            self.count = 0
            self.toll = 0
            self.fvg = []
            self.signal_history = []
            self.ihk = None
            point = 10 ** (-self.SYMBOL_DIGITS.get(symbol, self.DEFAULT_DIGITS))
            self.point_size = point
            self.commission_frozen = self.commission * point

    def on_tick(self, price: float, volume: float = 1.0, ordered_index: int = 0):
        with self._lock:
            if not is_finite_number(price) or price <= 0:
                return
            if self.price > 0:
                self.prev_price = self.price
            self.price = price
            self.tick_in_bar += 1
            if not self.bars or self.tick_in_bar > 5:
                self.bars.append(AEEA_Bar(
                    t=time.time(), o=price, h=price, l=price, c=price, v=volume
                ))
                self.tick_in_bar = 1
                if len(self.bars) > 200:
                    self.bars = self.bars[-200:]
            else:
                last = self.bars[-1]
                last.h = max(last.h, price)
                last.l = min(last.l, price)
                last.c = price
                last.v += volume
            if self.tick_in_bar == 5 or ordered_index % 5 == 0:
                self._on_bar(ordered_index)
            self._trailing_and_stops()

    def _compute_indicators(self) -> List[Dict[str, Any]]:
        if len(self.bars) < 2:
            return []
        closes = [b.c for b in self.bars]
        highs = [b.h for b in self.bars]
        lows = [b.l for b in self.bars]
        opens = [b.o for b in self.bars]
        vols = [b.v for b in self.bars]
        per = 14
        raw = {
            "ADX": self._adx_series(highs, lows, closes, per),
            "STOCH": self._stoch_series(highs, lows, closes, per),
            "RVI": self._rvi_series(opens, closes, per),
            "AC": self._ac_series(highs, lows, closes, per),
            "FORCE": self._force_series(closes, vols, per),
            "OBV": self._obv_series(closes, vols),
            "AD": self._ad_series(highs, lows, closes, vols),
            "MFI": self._mfi_series(highs, lows, closes, vols, per),
            "MOM": self._mom_series(closes, per),
            "DeM": self._dem_series(highs, lows, per),
            "WPR": self._wpr_series(highs, lows, closes, per),
            "CCI": self._cci_series(highs, lows, closes, per),
            "RSI": self._rsi_series(closes, per),
        }
        names = list(raw.keys())
        out = []
        for name in names:
            series = raw[name]
            norm = self._norm100(series)
            last = series[-1] if series else None
            out.append({"name": name, "value": norm, "raw": last})
        self.ihk = self._ichimoku_val(highs, lows, closes)
        if self.ihk:
            ihk_series = [self.ihk["tenkan"], self.ihk["kijun"], self.ihk["ssa"], self.ihk["ssb"], self.ihk["price"]]
            out.append({"name": "IHK", "value": self._norm100(ihk_series), "raw": self.ihk["kijun"]})
        else:
            out.append({"name": "IHK", "value": None, "raw": None})
        return out

    def _norm100(self, series: List[float]) -> Optional[float]:
        if not series:
            return None
        mn = min(series)
        mx = max(series)
        if mx == mn:
            return 50.0
        return 100.0 * (series[-1] - mn) / (mx - mn)

    def _sma(self, arr: List[float], per: int) -> Optional[float]:
        if len(arr) < per:
            return None
        return sum(arr[-per:]) / per

    def _std_pop(self, arr: List[float], per: int) -> Optional[float]:
        m = self._sma(arr, per)
        if m is None:
            return None
        v = sum((x - m) ** 2 for x in arr[-per:]) / per
        return _math_mod.sqrt(v)

    def _adx_series(self, highs, lows, closes, per):
        out = []
        for i in range(len(closes)):
            s = max(0, i - per * 2)
            trs, pdm, mdm = [], [], []
            for j in range(s + 1, i + 1):
                trs.append(max(highs[j] - lows[j], abs(highs[j] - closes[j-1]), abs(lows[j] - closes[j-1])))
                up = highs[j] - highs[j-1]
                dn = lows[j-1] - lows[j]
                pdm.append(up if up > dn and up > 0 else 0)
                mdm.append(dn if dn > up and dn > 0 else 0)
            atr = sum(trs) / len(trs) if trs else 0
            pd = sum(pdm) / len(pdm) if pdm else 0
            md = sum(mdm) / len(mdm) if mdm else 0
            pdi = 100 * pd / atr if atr else 0
            mdi = 100 * md / atr if atr else 0
            out.append(0 if (pdi + mdi) == 0 else 100 * abs(pdi - mdi) / (pdi + mdi))
        return out

    def _stoch_series(self, highs, lows, closes, per):
        out = []
        for i in range(len(closes)):
            s = max(0, i - per + 1)
            hh = max(highs[s:i+1])
            ll = min(lows[s:i+1])
            out.append(50.0 if hh == ll else 100 * (closes[i] - ll) / (hh - ll))
        return out

    def _rvi_series(self, opens, closes, per):
        out = []
        for i in range(len(closes)):
            s = max(0, i - per + 1)
            num = 0.0
            den = 0.0
            for j in range(s + 1, i + 1):
                num += (closes[j] - opens[j])
                den += (closes[j-1] - opens[j-1])
            out.append(50.0 if den == 0 else 100 * num / (abs(num) + abs(den) + 1e-9))
        return out

    def _ac_series(self, highs, lows, closes, per):
        out = []
        for i in range(len(closes)):
            s = max(0, i - per + 1)
            mids = [(highs[j] + lows[j]) / 2 for j in range(s, i+1)]
            sma_m = sum(mids) / len(mids)
            ao = mids[-1] - sma_m
            out.append(ao)
        return out

    def _force_series(self, closes, vols, per):
        out = []
        for i in range(len(closes)):
            s = max(0, i - per + 1)
            total = 0.0
            cnt = 0
            for j in range(s + 1, i + 1):
                total += (closes[j] - closes[j-1]) * (vols[j] or 1)
                cnt += 1
            out.append(total / cnt if cnt else 0)
        return out

    def _obv_series(self, closes, vols):
        out = []
        cum = 0.0
        for i in range(len(closes)):
            if i > 0:
                if closes[i] > closes[i-1]:
                    cum += (vols[i] or 1)
                elif closes[i] < closes[i-1]:
                    cum -= (vols[i] or 1)
            out.append(cum)
        return out

    def _ad_series(self, highs, lows, closes, vols):
        out = []
        cum = 0.0
        for i in range(len(closes)):
            den = (highs[i] - lows[i]) or 1
            cum += ((closes[i] - lows[i]) - (highs[i] - closes[i])) / den * (vols[i] or 1)
            out.append(cum)
        return out

    def _mfi_series(self, highs, lows, closes, vols, per):
        out = []
        for i in range(len(closes)):
            s = max(0, i - per + 1)
            pos = 0.0
            neg = 0.0
            for j in range(s + 1, i + 1):
                tp = (highs[j] + lows[j] + closes[j]) / 3
                tp_prev = (highs[j-1] + lows[j-1] + closes[j-1]) / 3
                mf = tp * (vols[j] or 1)
                if tp > tp_prev:
                    pos += mf
                elif tp < tp_prev:
                    neg += mf
            out.append(50.0 if (pos + neg) == 0 else 100 * pos / (pos + neg))
        return out

    def _mom_series(self, closes, per):
        out = []
        for i in range(len(closes)):
            out.append(closes[i] - closes[i - per] if i >= per else 0)
        return out

    def _dem_series(self, highs, lows, per):
        out = []
        for i in range(len(highs)):
            s = max(0, i - per + 1)
            up = 0.0
            dn = 0.0
            for j in range(s + 1, i + 1):
                up += max(0, highs[j] - highs[j-1])
                dn += max(0, lows[j-1] - lows[j])
            out.append(50.0 if (up + dn) == 0 else 100 * up / (up + dn))
        return out

    def _wpr_series(self, highs, lows, closes, per):
        out = []
        for i in range(len(closes)):
            s = max(0, i - per + 1)
            hh = max(highs[s:i+1])
            ll = min(lows[s:i+1])
            out.append(-50.0 if hh == ll else -100 * (hh - closes[i]) / (hh - ll))
        return out

    def _cci_series(self, highs, lows, closes, per):
        out = []
        for i in range(len(closes)):
            s = max(0, i - per + 1)
            tps = [(highs[j] + lows[j] + closes[j]) / 3 for j in range(s, i+1)]
            mm = sum(tps) / len(tps)
            md = sum(abs(x - mm) for x in tps) / len(tps) or 1
            out.append((tps[-1] - mm) / (0.015 * md))
        return out

    def _rsi_series(self, closes, per):
        out = []
        for i in range(1, len(closes)):
            g = 0.0
            l = 0.0
            n = min(per, i)
            for j in range(i - n + 1, i + 1):
                d = closes[j] - closes[j-1]
                if d > 0:
                    g += d
                else:
                    l -= d
            out.append(50.0 if (g + l) == 0 else 100 * g / (g + l))
        return out

    def _ichimoku_val(self, highs, lows, closes):
        if len(closes) < 26:
            return None
        s9 = max(0, len(closes) - 9)
        s26 = max(0, len(closes) - 26)
        s52 = max(0, len(closes) - 52)
        tenkan = (max(highs[s9:]) + min(lows[s9:])) / 2
        kijun = (max(highs[s26:]) + min(lows[s26:])) / 2
        ssa = (tenkan + kijun) / 2
        ssb = (max(highs[s52:]) + min(lows[s52:])) / 2
        return {"tenkan": tenkan, "kijun": kijun, "ssa": ssa, "ssb": ssb, "price": closes[-1]}

    def _on_bar(self, ordered_index: int):
        with self._lock:
            self.indicators = self._compute_indicators()
            self.bb58 = self._compute_bb58()
            warming = (len(self.bars) < 5 or len(self.indicators) < 13)
            self.count = 0
            self.toll = 0
            if warming:
                self.m = 0
                self.n = 0
                self.delta = 0
                self.signal = "⊙ NEUTRAL"
                self.signal_dir = 0
                self.regime = "— warming up"
                self.parc = 0.0
                return
            m = 0
            n = 0
            for it in self.indicators[:13]:
                v = it.get("value")
                if v is None:
                    continue
                if v > 66.6:
                    m += 1
                elif v < 33.3:
                    n += 1
            self.m = m
            self.n = n
            self.delta = m - n - 2
            if self.delta >= 1:
                self.regime = "↑ BULL / Hawk"
                self.signal_dir = 1
                self.signal = "↑ BUY"
            elif self.delta <= -1:
                self.regime = "↓ BEAR / Dove"
                self.signal_dir = -1
                self.signal = "↓ SELL"
            else:
                self.regime = "⊙ NEUTRAL"
                self.signal_dir = 0
                self.signal = "⊙ NEUTRAL"
            tick = ordered_index if ordered_index > 0 else (self.signal_tick + 5)
            if self.signal_dir != 0:
                if self.signal_tick != -1 and tick == self.signal_tick + 5:
                    self.toll = 1
                if tick != self.signal_tick and tick != self.signal_tick + 5:
                    self.count = 1
                    self.signal_tick = tick
            if len(self.bars) >= 3:
                last = self.bars[-1].c
                prev = self.bars[-2].c
                slope = last - prev
                bb = self.bb58[-1] if self.bb58 else None
                target = last + slope * 3
                if bb:
                    target = max(bb["lo"], min(bb["up"], target))
                self.parc = target
            if self.price > 0:
                kept = []
                for a in self.fvg:
                    crossed = (a["type"] == "topp" and self.price >= a["price"]) or \
                              (a["type"] == "bott" and self.price <= a["price"])
                    if not crossed:
                        kept.append(a)
                    else:
                        logger.info(f"FVG maintenance: remove {a['type']} @ {a['price']}")
                self.fvg = kept
            if self.signal != "⊙ NEUTRAL":
                self.signal_history.append(f"{self.signal} @ ordered {tick} (δ {self.delta})")
                if len(self.signal_history) > 40:
                    self.signal_history = self.signal_history[-40:]

    def _compute_bb58(self) -> List[Dict[str, float]]:
        closes = [b.c for b in self.bars]
        rows = []
        for per in range(3, 61):
            m = self._sma(closes, per)
            if m is None:
                continue
            sd = self._std_pop(closes, per) or 0
            rows.append({"per": per, "mid": m, "up": m + self.bb_dev * sd, "lo": m - self.bb_dev * sd})
        return rows

    def _trailing_and_stops(self):
        with self._lock:
            for o in self.orders:
                if o.status != "open":
                    continue
                if self.trailing > 0 and self.price > 0:
                    if o.side == "BUY":
                        ns = self.price - self.trailing
                        if o.sl == 0 or ns > o.sl:
                            o.sl = ns
                    else:
                        ns = self.price + self.trailing
                        if o.sl == 0 or ns < o.sl:
                            o.sl = ns
                if o.sl > 0:
                    if (o.side == "BUY" and self.price <= o.sl) or \
                       (o.side == "SELL" and self.price >= o.sl):
                        o.status = "closed · SL"
                        logger.info(f"Order #{o.order_id} closed at SL {o.sl}")
                elif o.tp > 0:
                    if (o.side == "BUY" and self.price >= o.tp) or \
                       (o.side == "SELL" and self.price <= o.tp):
                        o.status = "closed · TP"
                        logger.info(f"Order #{o.order_id} closed at TP {o.tp}")

    def place_order(self, side: str, volume: float, sl: float, tp: float,
                    symbol: str = "") -> Dict[str, Any]:
        with self._lock:
            if self.price <= 0:
                return {"ok": False, "error": "no_price"}
            if side not in ("BUY", "SELL"):
                return {"ok": False, "error": "invalid_side"}
            if not is_finite_number(volume) or volume <= 0:
                return {"ok": False, "error": "invalid_volume"}
            if not is_finite_number(sl):
                sl = 0.0
            if not is_finite_number(tp):
                tp = 0.0
            o = AEEA_Order(
                order_id=self.next_order_id,
                side=side,
                volume=volume,
                entry=self.price,
                sl=sl,
                tp=tp,
                status="filled",
                fill_price=self.price,
                created_at=datetime.now().isoformat(),
                backend_order_id=self.next_order_id,
            )
            self.next_order_id += 1
            self.orders.append(o)
            if len(self.orders) > 200:
                self.orders = self.orders[-200:]
            return {
                "ok": True,
                "order_id": o.order_id,
                "side": o.side,
                "volume": o.volume,
                "entry": o.entry,
                "sl": o.sl,
                "tp": o.tp,
                "status": o.status,
                "fill_price": o.fill_price,
            }

    def close_order(self, order_id: Optional[int] = None, all: bool = False) -> Dict[str, Any]:
        with self._lock:
            closed_ids = []
            if all:
                for o in self.orders:
                    if o.status == "open" or o.status == "filled":
                        o.status = "closed"
                        closed_ids.append(o.order_id)
            elif order_id is not None:
                for o in self.orders:
                    if o.order_id == order_id and (o.status == "open" or o.status == "filled"):
                        o.status = "closed"
                        closed_ids.append(o.order_id)
                        break
            return {"ok": True, "closed_ids": closed_ids, "status": "closed" if closed_ids else "no_change"}

    def snapshot(self) -> Dict[str, Any]:
        with self._lock:
            return {
                "symbol": self.symbol,
                "timeframe": self.timeframe,
                "price": self.price,
                "prev_price": self.prev_price,
                "bars": [
                    {"t": b.t, "o": b.o, "h": b.h, "l": b.l, "c": b.c, "v": b.v}
                    for b in self.bars[-100:]
                ],
                "indicators": self.indicators,
                "bb58": self.bb58,
                "m": self.m,
                "n": self.n,
                "delta": self.delta,
                "regime": self.regime,
                "signal": self.signal,
                "signal_dir": self.signal_dir,
                "parc": self.parc,
                "signal_tick": self.signal_tick,
                "count": self.count,
                "toll": self.toll,
                "orders_count": len([o for o in self.orders if o.status in ("open", "filled")]),
                "orders": [
                    {"order_id": o.order_id, "side": o.side, "volume": o.volume,
                     "entry": o.entry, "sl": o.sl, "tp": o.tp, "status": o.status,
                     "fill_price": o.fill_price, "created_at": o.created_at}
                    for o in self.orders[-50:]
                ],
                "fvg": self.fvg,
                "signal_history": self.signal_history[-20:],
                "ihk": self.ihk,
                "commission_frozen": self.commission_frozen,
                "point_size": self.point_size,
                "bb_dev": self.bb_dev,
                "trailing": self.trailing,
            }

    def get_ohlcv(self) -> Dict[str, Any]:
        with self._lock:
            bars = [
                {"t": b.t, "o": b.o, "h": b.h, "l": b.l, "c": b.c, "v": b.v,
                 "timestamp": datetime.fromtimestamp(b.t).isoformat() if b.t else datetime.now().isoformat()}
                for b in self.bars[-200:]
            ]
            if not bars and self.price > 0:
                now = time.time()
                bars = [{"t": now, "o": self.price, "h": self.price, "l": self.price, "c": self.price, "v": 1.0, "timestamp": datetime.now().isoformat()}]
            return {
                "symbol": self.symbol,
                "timeframe": self.timeframe,
                "bars": bars,
                "last_price": self.price,
                "prev_price": self.prev_price,
                "provider": "ae-fused",
                "source": "backend",
            }

    def get_signals(self) -> Dict[str, Any]:
        with self._lock:
            return {
                "symbol": self.symbol,
                "price": self.price,
                "signal": self.signal,
                "signal_dir": self.signal_dir,
                "delta": self.delta,
                "m": self.m,
                "n": self.n,
                "regime": self.regime,
                "provider": "ae-fused",
                "timestamp": datetime.now().isoformat(),
                "history": self.signal_history[-20:],
            }


def is_finite_number(x) -> bool:
    try:
        v = float(x)
        return _math_mod.isfinite(v)
    except Exception:
        return False


# ============================================================================
# ÆI SEED (prime -> lattice -> Hopf -> s²=r² -> DbZ -> I -> SelfEvolution)
# ============================================================================
class AEI_Seed:
    def __init__(
        self,
        processor: SymbolicProcessor,
        lattice: GeometricLatticeProtocol,
        monitor: AethericMonitor,
        renderer: QuaternionicRenderer,
        linguist: LingosoEncoder,
    ):
        self.processor = processor
        self.lattice = lattice
        self.monitor = monitor
        self.renderer = renderer
        self.linguist = linguist
        self.primes: List[Fraction] = [Fraction(2), Fraction(3), Fraction(5)]
        self.phi = SymbolicQuaternion(Fraction.one(), Fraction.zero(),
                                      Fraction.zero(), Fraction.zero())
        self.psi = SymbolicWavefunction({(0, 0, 0, 0): Fraction.one()})
        self.origin = SymbolicQuaternion(Fraction.one(), Fraction.zero(),
                                         Fraction.zero(), Fraction.zero())
        self.metrics = IntelligenceMetric()
        self.evolution = SelfEvolutionCore({"core_axioms": {"s_equals_r": Fraction.one()}})
        self.consciousness = ConsciousnessOperator(self.psi, self.phi)
        self.state = "initialized"
        self.generation = 0
        self.tick = 0
        self.last_arc_sq = Fraction.zero()
        self.last_radius_sq = Fraction.zero()
        self.last_deviation_sq = Fraction.zero()
        self.last_I = Fraction.zero()
        self.last_hopf_base: Tuple[Fraction, Fraction] = (Fraction.zero(), Fraction.zero())
        self.last_trajectory: List[SymbolicQuaternion] = []
        self.last_evolution: Optional[Dict[str, Any]] = None
        self.last_linguistic_trajectory: List[SymbolicQuaternion] = []
        self.last_logic_hash: str = ""
        self.history: List[Dict[str, Any]] = []
        self._prior_deviation_sq: Optional[Fraction] = None
        self._step_lock = threading.Lock()
        self._cached_snapshot: Optional[Dict[str, Any]] = None
        self._cached_at = 0
        self._cached_light_snapshot: Optional[Dict[str, Any]] = None
        self._cached_light_at = 0

    def _integrate_wavefunction_symbolic(self) -> Dict[Tuple[int, int, int, int], Fraction]:
        coeffs: Dict[Tuple[int, int, int, int], Fraction] = {}
        points = self.lattice.points()
        for i, _point in enumerate(points):
            coeffs[(i, 0, 0, 0)] = Fraction(1, i + 1)
        if not coeffs:
            coeffs[(0, 0, 0, 0)] = Fraction.one()
        if self._prior_deviation_sq is not None and not self._prior_deviation_sq.is_zero():
            for key, val in self.psi.coeffs.items():
                blended = coeffs.get(key, Fraction.zero()) + val * Fraction(1, 2)
                coeffs[key] = blended
        return coeffs

    def _generate_trajectory(self, psi: SymbolicWavefunction) -> List[SymbolicQuaternion]:
        trajectory = []
        epsilon = Fraction(1, 100)
        for k in range(10):
            t = Fraction(k, 10)
            q = SymbolicQuaternion(t, Fraction.zero(), Fraction.zero(), Fraction.zero())
            q = q.apply_natalia_fibration(t, epsilon, iterations=15)
            trajectory.append(q)
        return trajectory

    def step(self, x: Fraction) -> Dict[str, Any]:
        with self._step_lock:
            x_doc = x
            x = Fraction.one() + x_doc
            p_n = self.processor.generate_next_prime(self.primes)
            if self.processor.validate_indivisibility(p_n, self.primes):
                self.primes.append(p_n)
            center = self.lattice.stereographic_project_exact(p_n)
            admitted = self.lattice.add_sphere(center, Fraction.one())
            if admitted and center is not None:
                _a, _c = _phi_from_center(center)
                self.phi = SymbolicQuaternion(_a, Fraction.zero(), _c, Fraction.zero())
            coeffs = self._integrate_wavefunction_symbolic()
            self.psi = SymbolicWavefunction(coeffs)
            self.consciousness = ConsciousnessOperator(self.psi, self.phi)
            trajectory = self._generate_trajectory(self.psi)
            self.last_trajectory = trajectory
            arc_sq = self.monitor.compute_arc_length_squared(trajectory)
            radius_sq = (trajectory[-1].magnitude_squared() if trajectory
                         else Fraction.zero())
            coherence = (arc_sq == radius_sq)
            deviation_sq = arc_sq - radius_sq
            self.last_arc_sq = arc_sq
            self.last_radius_sq = radius_sq
            self.last_deviation_sq = deviation_sq
            self.psi = DbZ.Rectify(self.psi, arc_sq, radius_sq, deviation_sq)
            self._prior_deviation_sq = deviation_sq
            q_eval = SymbolicQuaternion(p_n, Fraction.zero(), Fraction.zero(), Fraction.zero())
            I = self.metrics.compute_metric(
                valid_pairs=len(self.primes),
                total_primes=len(self.primes),
                pi_x=len(self.primes),
                x=p_n,
                curl_phi_norm=self.phi.magnitude_squared(),
                target_arc=arc_sq,
                target_radius=radius_sq,
            )
            self.last_I = I
            evolution_record = self.evolution.evolve_step(I, self.psi, q_eval, deviation_sq)
            self.last_evolution = evolution_record
            self.last_logic_hash = evolution_record.get("logic_hash", "")
            hopf_base = self.renderer.project_to_hopf_base(self.phi)
            self.last_hopf_base = hopf_base
            self.tick += 1
            self.generation = self.evolution.generation
            self.state = "coherent" if coherence else "evolving"
            record = {
                "tick": self.tick,
                "generation": self.generation,
                "prime": str(p_n),
                "prime_count": len(self.primes),
                "lattice_points": len(self.lattice.points()),
                "arc_sq": str(arc_sq),
                "radius_sq": str(radius_sq),
                "deviation_sq": str(deviation_sq),
                "coherence": bool(coherence),
                "I": str(I),
                "state": self.state,
                "hopf_base": [str(hopf_base[0]), str(hopf_base[1])],
                "evolution": evolution_record,
                "x_input": str(x),
                "x_input_raw": str(x_doc),
                "ts": datetime.now().isoformat(),
            }
            self.history.append(record)
            if len(self.history) > 150:
                self.history = self.history[-150:]
            return record

    def run_autonomous(self, steps: int, x_fn=None) -> List[Dict[str, Any]]:
        records = []
        for i in range(steps):
            x = x_fn(i) if x_fn else Fraction(i, 1)
            records.append(self.step(x))
        return records

    def snapshot(self, light: bool = False) -> Dict[str, Any]:
        import time as _time_mod
        now = _time_mod.time()
        if light:
            if self._cached_light_snapshot is not None and (now - self._cached_light_at) < 1.0:
                return self._cached_light_snapshot
        else:
            if self._cached_snapshot is not None and (now - self._cached_at) < 0.5:
                return self._cached_snapshot

        def _frac_short(f: Any, max_len: int = 64) -> str:
            try:
                if hasattr(f, 'numerator') and hasattr(f, 'denominator'):
                    n = f.numerator
                    d = f.denominator
                    try:
                        nb = n.bit_length() if hasattr(n, 'bit_length') else 0
                        db = d.bit_length() if hasattr(d, 'bit_length') else 0
                        if nb > 2700 or db > 2700:
                            nd = int(nb * 0.30103) + 1 if nb else 1
                            dd = int(db * 0.30103) + 1 if db else 1
                            return f"HUGE~{nd}d/{dd}d~({nd+dd}ch)"
                    except Exception:
                        pass
                    try:
                        s = str(f)
                    except ValueError:
                        return "HUGE"
                    if len(s) <= max_len:
                        return s
                    if '/' in s:
                        a, b = s.split('/', 1)
                        if len(a) > 20 or len(b) > 20:
                            return f"{a[:10]}…{a[-3:]}/{b[:10]}…{b[-3:]}…({len(s)}ch)"
                    return s[:max_len] + f"…({len(s)}ch)"
                s = str(f)
                if len(s) <= max_len:
                    return s
                return s[:max_len] + f"…({len(s)}ch)"
            except Exception:
                try:
                    if hasattr(f, 'numerator'):
                        try:
                            nb = f.numerator.bit_length()
                            return f"~{int(nb*0.30103)}d frac"
                        except Exception:
                            pass
                    return str(f)[:max_len]
                except Exception:
                    return "0/1"

        lock = self._step_lock
        acquired = lock.acquire(timeout=0.05)
        if not acquired:
            if light and self._cached_light_snapshot is not None:
                d = dict(self._cached_light_snapshot)
                d["stale"] = True
                d["tick"] = self.tick
                return d
            if self._cached_snapshot is not None:
                d = dict(self._cached_snapshot)
                d["stale"] = True
                return d
            return {
                "state": self.state,
                "tick": self.tick,
                "generation": self.generation,
                "prime_count": len(self.primes),
                "lattice_points": len(self.lattice.points()),
                "primes_tail": [_frac_short(p, 32) for p in self.primes[-4:]],
                "arc_sq": _frac_short(self.last_arc_sq, 48),
                "radius_sq": _frac_short(self.last_radius_sq, 48),
                "deviation_sq": _frac_short(self.last_deviation_sq, 48),
                "coherence": self.last_deviation_sq.is_zero(),
                "I": _frac_short(self.last_I, 48),
                "hopf_base": [_frac_short(self.last_hopf_base[0], 32), _frac_short(self.last_hopf_base[1], 32)],
                "psi_real": _frac_short(self.psi.real_part(), 32),
                "phi": {"a": "1/1", "b": "0/1", "c": "0/1", "d": "0/1"},
                "phi_magnitude_sq": "1/1",
                "trajectory": [],
                "evolution": self.last_evolution,
                "logic_core": {},
                "history_tail": self.history[-4:],
                "last_logic_hash": self.last_logic_hash,
                "stale": True,
                "booting": True,
            }
        try:
            if light:
                snap = {
                    "state": self.state,
                    "tick": self.tick,
                    "generation": self.generation,
                    "prime_count": len(self.primes),
                    "lattice_points": len(self.lattice.points()),
                    "primes_tail": [_frac_short(p, 32) for p in self.primes[-4:]],
                    "arc_sq": _frac_short(self.last_arc_sq, 48),
                    "radius_sq": _frac_short(self.last_radius_sq, 48),
                    "deviation_sq": _frac_short(self.last_deviation_sq, 48),
                    "coherence": self.last_deviation_sq.is_zero(),
                    "I": _frac_short(self.last_I, 48),
                    "hopf_base": [_frac_short(self.last_hopf_base[0], 32), _frac_short(self.last_hopf_base[1], 32)],
                    "psi_real": _frac_short(self.psi.real_part(), 32),
                    "phi": {
                        "a": _frac_short(self.phi.a, 32),
                        "b": _frac_short(self.phi.b, 32),
                        "c": _frac_short(self.phi.c, 32),
                        "d": _frac_short(self.phi.d, 32),
                    } if hasattr(self, 'phi') else {"a": "1/1", "b": "0/1", "c": "0/1", "d": "0/1"},
                    "phi_magnitude_sq": _frac_short(self.phi.magnitude_squared() if hasattr(self, 'phi') else "1/1", 32),
                    "trajectory": [],
                    "evolution": {"generation": self.last_evolution.get("generation") if self.last_evolution else 0, "logic_hash": self.last_logic_hash} if self.last_evolution else None,
                    "logic_core": {},
                    "history_tail": self.history[-4:],
                    "last_logic_hash": self.last_logic_hash,
                    "stale": False,
                }
                self._cached_light_snapshot = snap
                self._cached_light_at = now
                return snap
            else:
                snap = {
                    "state": self.state,
                    "tick": self.tick,
                    "generation": self.generation,
                    "primes_tail": [_frac_short(p, 64) for p in self.primes[-8:]],
                    "prime_count": len(self.primes),
                    "lattice_points": len(self.lattice.points()),
                    "arc_sq": _frac_short(self.last_arc_sq, 128),
                    "radius_sq": _frac_short(self.last_radius_sq, 128),
                    "deviation_sq": _frac_short(self.last_deviation_sq, 128),
                    "coherence": self.last_deviation_sq.is_zero(),
                    "I": _frac_short(self.last_I, 128),
                    "hopf_base": [_frac_short(self.last_hopf_base[0], 64), _frac_short(self.last_hopf_base[1], 64)],
                    "evolution": self.last_evolution,
                    "trajectory": [
                        {"a": _frac_short(q.a, 48), "b": _frac_short(q.b, 48), "c": _frac_short(q.c, 48), "d": _frac_short(q.d, 48)}
                        for q in self.last_trajectory[:10]
                    ],
                    "linguistic_trajectory": [
                        {"a": _frac_short(q.a, 48), "b": _frac_short(q.b, 48), "c": _frac_short(q.c, 48), "d": _frac_short(q.d, 48)}
                        for q in self.last_linguistic_trajectory[:10]
                    ],
                    "history_tail": self.history[-10:],
                    "logic_core": {
                        k: {kk: _frac_short(vv, 64) for kk, vv in v.items()} if isinstance(v, dict) else _frac_short(v, 64)
                        for k, v in self.evolution.logic_core.items()
                    },
                    "last_logic_hash": self.last_logic_hash,
                    "psi_real": _frac_short(self.psi.real_part(), 64),
                    "phi": {
                        "a": _frac_short(self.phi.a, 64),
                        "b": _frac_short(self.phi.b, 64),
                        "c": _frac_short(self.phi.c, 64),
                        "d": _frac_short(self.phi.d, 64),
                    } if hasattr(self, 'phi') else {"a": "1/1", "b": "0/1", "c": "0/1", "d": "0/1"},
                    "phi_magnitude_sq": _frac_short(self.phi.magnitude_squared() if hasattr(self, 'phi') else "1/1", 64),
                    "stale": False,
                }
                self._cached_snapshot = snap
                self._cached_at = now
                return snap
        finally:
            lock.release()

    def encode_syllable(self, syllable: str) -> Dict[str, Any]:
        traj = self.linguist.encode_syllable(syllable)
        self.last_linguistic_trajectory = traj
        arc_sq = self.monitor.compute_arc_length_squared(traj)
        radius_sq = traj[-1].magnitude_squared() if traj else Fraction.zero()
        deviation_sq = arc_sq - radius_sq
        coherent = (arc_sq == radius_sq)
        arc_check = "s = r ✓" if coherent else "s ≠ r ✗"
        return {
            "syllable": syllable,
            "length": len(traj),
            "arc_sq": str(arc_sq),
            "radius_sq": str(radius_sq),
            "deviation_sq": str(deviation_sq),
            "coherence": bool(coherent),
            "arc_check": arc_check,
            "trajectory": [
                {"a": str(q.a), "b": str(q.b), "c": str(q.c), "d": str(q.d)}
                for q in traj
            ],
        }

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
RELAY_URL: str = os.getenv("RELAY_URL", "").strip().rstrip("/")
RELAY_KEY: str = os.getenv("RELAY_KEY", "").strip()
RELAY_TIMEOUT: int = int(os.getenv("RELAY_TIMEOUT", "15"))
RELAY_MAX_RETRIES: int = int(os.getenv("RELAY_MAX_RETRIES", "3"))
SEED_TICK_INTERVAL: int = int(os.getenv("SEED_TICK_INTERVAL", "5"))
CRAWL_INTERVAL: int = int(os.getenv("CRAWL_INTERVAL", "3"))
CRAWLER_BLOCKLIST: list = [s.strip() for s in os.getenv("CRAWLER_BLOCKLIST", "meta.wikimedia.org,wikimedia.org/w/api,thumb.wikimedia,upload.wikimedia,feeaturedfeed").split(",") if s.strip()]
MAX_CRAWL_DEPTH: int = int(os.getenv("MAX_CRAWL_DEPTH", "3"))
CRAWL_SEED_URLS: str = os.getenv("CRAWL_SEED_URLS", "").strip()
CRAWLER_DB_PATH: str = os.getenv("CRAWLER_DB_PATH", "ae_crawler.db")
TELEGRAM_DB_CHANNEL_ID: str = os.getenv("TELEGRAM_DB_CHANNEL_ID", "").strip()
ENABLE_TELEGRAM_DB: bool = os.getenv("ENABLE_TELEGRAM_DB", "0").strip() in ("1","true","yes")
TELEGRAM_DB_USER_SHARDS: bool = os.getenv("TELEGRAM_DB_USER_SHARDS", "0").strip() in ("1","true","yes")
TELEGRAM_DB_SAVE_INTERVAL: int = int(os.getenv("TELEGRAM_DB_SAVE_INTERVAL", "5"))
TELEGRAM_DB_CHUNK_SIZE: int = int(os.getenv("TELEGRAM_DB_CHUNK_SIZE", "3800"))
TELEGRAM_DB_PIN_INDEX: bool = os.getenv("TELEGRAM_DB_PIN_INDEX", "0").strip() in ("1","true","yes")
TELEGRAM_DB_CENTRAL_USER_ID: str = os.getenv("TELEGRAM_DB_CENTRAL_USER_ID", "").strip()
ALLOWED_USER_IDS: set = set()
_raw_allowed = os.getenv("ALLOWED_USER_IDS", "").strip()
if _raw_allowed:
    for tok in _raw_allowed.split(","):
        tok = tok.strip()
        if tok.isdigit():
            ALLOWED_USER_IDS.add(int(tok))

TELEGRAM_DB_SHARD_POOL: set = set()
_raw_shard_pool = os.getenv("TELEGRAM_DB_SHARD_POOL", "").strip()
if _raw_shard_pool:
    for tok in _raw_shard_pool.split(","):
        tok = tok.strip()
        if tok.isdigit():
            TELEGRAM_DB_SHARD_POOL.add(int(tok))


def _get_shard_pool() -> set:
    if TELEGRAM_DB_SHARD_POOL:
        return TELEGRAM_DB_SHARD_POOL
    return ALLOWED_USER_IDS


def _is_allowed_user(user_id) -> bool:
    if not ALLOWED_USER_IDS:
        return True
    try:
        return int(user_id) in ALLOWED_USER_IDS
    except (TypeError, ValueError):
        return False


# ============================================================================
# TELEGRAM WEB APP AUTHENTICATION
# ============================================================================
def verify_telegram_init_data(init_data: str, bot_token: str,
                              max_age_seconds: int = 86400) -> Optional[Dict[str, Any]]:
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
    secret_key = hmac.new(b"WebAppData", bot_token.encode("utf-8"),
                          hashlib.sha256).digest()
    expected_hash = hmac.new(secret_key, data_check_string.encode("utf-8"),
                             hashlib.sha256).hexdigest()
    try:
        expected_b = expected_hash.encode("ascii")
        received_b = str(received_hash).encode("ascii")
        if not hmac.compare_digest(expected_b, received_b):
            return None
    except Exception:
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


# ============================================================================
# CS TRANSLATION HELPERS
# ============================================================================
def _md_escape(value) -> str:
    if value is None:
        return "—"
    s = str(value)
    out = []
    for ch in s:
        if ch == '\\':
            out.append('\\\\')
        elif ch == '*':
            out.append('\\*')
        elif ch == '_':
            out.append('\\_')
        elif ch == '`':
            out.append('\\`')
        elif ch == '[':
            out.append('\\[')
        elif ch == ']':
            out.append('\\]')
        elif ch == '<':
            out.append('&lt;')
        elif ch == '>':
            out.append('&gt;')
        else:
            out.append(ch)
    return ''.join(out)


_CS_VALUE_MAP: Dict[str, str] = {
    "BUY": "↑", "SELL": "↓", "NEUTRAL": "⊙",
    "ACTIVE": "𝒜₃", "INACTIVE": "𝒜₄",
    "ON": "𝒜₃", "OFF": "𝒜₄",
    "UP": "↟", "DOWN": "↡",
    "LONG": "↑", "SHORT": "↓",
    "CLOSE": "𝒞_Close", "NONE": "𝒩",
    "YES": "⟦𝒴⟧", "NO": "⟦𝒩⟧",
    "TRUE": "⟦𝒯⟧", "FALSE": "⟦ℱ⟧",
    "STABLE": "𝒮_Stable", "UNKNOWN": "𝒰",
    "COHERENT": "𝒮_coherent", "EVOLVING": "𝒟_evolving",
    "INITIALIZED": "𝒮_init",
}


def _cs(value) -> str:
    if value is None:
        return "—"
    s = str(value).strip()
    if not s:
        return "—"
    upper = s.upper()
    if upper in _CS_VALUE_MAP:
        return _CS_VALUE_MAP[upper]
    return s


def _looks_like_reply_error(desc: str) -> bool:
    if not desc:
        return False
    d = desc.lower()
    return any(k in d for k in ("reply", "message to be replied",
                                "reply_to_message_id", "reply message not found",
                                "message_id_invalid"))


def _looks_like_parse_error(desc: str) -> bool:
    if not desc:
        return False
    d = desc.lower()
    return any(k in d for k in ("parse", "entities", "entity",
                                "unsupported start tag", "unsupported end tag",
                                "unexpected end of", "can't find end",
                                "can't parse", "markdown"))


# ============================================================================
# BRIDGE STATE
# ============================================================================
class BridgeState:
    def __init__(self):
        self._lock = threading.Lock()
        self._anchors: Dict[int, Dict[str, Any]] = {}
        self._next_anchor_idx = 0
        self._webapp_sessions: Dict[int, Dict[str, Any]] = {}
        self._handshake_lock = threading.Lock()

    def register_webapp_session(self, user_id: int, username: Optional[str],
                                chat_id: Optional[int] = None) -> bool:
        with self._handshake_lock:
            now = datetime.now().isoformat()
            existing = self._webapp_sessions.get(user_id, {})
            is_new = not existing
            chat_changed = existing.get("chat_id") != chat_id
            self._webapp_sessions[user_id] = {
                "user_id": user_id,
                "username": username,
                "chat_id": chat_id,
                "first_seen": existing.get("first_seen", now),
                "last_seen": now,
            }
            if is_new or chat_changed:
                logger.info(f"🔗 Web App session: user_id={user_id}, username={username}, chat_id={chat_id}")
            return True

    def add_anchor(self, q: SymbolicQuaternion, label: str = "") -> int:
        with self._lock:
            idx = self._next_anchor_idx
            self._next_anchor_idx += 1
            self._anchors[idx] = {
                "idx": idx,
                "a": str(q.a), "b": str(q.b), "c": str(q.c), "d": str(q.d),
                "label": label,
                "created": datetime.now().isoformat(),
            }
            return idx

    def remove_anchor(self, idx: int) -> bool:
        with self._lock:
            return self._anchors.pop(idx, None) is not None

    def list_anchors(self) -> List[Dict[str, Any]]:
        with self._lock:
            return list(self._anchors.values())


BRIDGE_STATE = BridgeState()
BRIDGE_ENGINE_REF: Dict[str, Any] = {
    "seed": None,
    "bot": None,
    "public_url": None,
    "crawler": None,
    "aeea": None,
    "port": None,
}

LAST_LIGHT_SNAPSHOT: dict = {}
LAST_LIGHT_AT = 0
LAST_LIGHT_LOCK = threading.Lock()


# ============================================================================
# BRIDGE HANDLER — the fused /22 endpoint surface
# ============================================================================
class BridgeHandler(BaseHTTPRequestHandler):
    server_version = "AE-Fused-Bridge/Final-First-edition"
    timeout = 10
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):
        return

    def _set_cors(self) -> None:
        origin = CORS_ORIGIN
        if origin == "*":
            self.send_header("Access-Control-Allow-Origin", "*")
        else:
            self.send_header("Access-Control-Allow-Origin", origin)
        self.send_header("Vary", "Origin")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, DELETE, OPTIONS")
        self.send_header("Access-Control-Allow-Headers",
                         "Content-Type, Accept, Authorization, X-Telegram-Init-Data, "
                         "X-Relay-Key, X-Limit, X-Since")
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
        try:
            length = int(self.headers.get("Content-Length", "0") or 0)
        except Exception:
            return b""
        if length <= 0:
            return b""
        if length > 1000000:
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
            seed = BRIDGE_ENGINE_REF.get("seed")
            crawler = BRIDGE_ENGINE_REF.get("crawler")
            aeea = BRIDGE_ENGINE_REF.get("aeea")
            raw_state = seed.state if seed else "uninitialized"
            self._send_json(200, {
                "ok": True,
                "service": "ae-fused-bridge",
                "version": "Final, First edition",
                "substrate": _SUBSTRATE,
                "seed_initialized": seed is not None,
                "engine_initialized": aeea is not None,
                "crawler_running": (crawler._running if crawler and hasattr(crawler, "_running") else False),
                "seed_tick": (seed.tick if seed else 0),
                "seed_generation": (seed.generation if seed else 0),
                "seed_state": _cs(raw_state),
                "prime_count": (len(seed.primes) if seed else 0),
                "lattice_points": (len(seed.lattice.points()) if seed else 0),
                "crawler_frontier": (crawler.state.frontier_size() if crawler else 0),
                "crawler_visited": (crawler.state.visited_count() if crawler else 0),
                "last_price_update": (datetime.fromtimestamp(aeea.bars[-1].t).isoformat() if aeea and aeea.bars and aeea.bars[-1].t else None),
                "aeea_price": (aeea.price if aeea else 0.0),
                "aeea_symbol": (aeea.symbol if aeea else "—"),
                "require_auth": REQUIRE_AUTH,
            })
            return

        if path == "/" or path == "/index.html":
            try:
                base = os.path.dirname(os.path.abspath(__file__))
                html_path = os.path.join(base, "index.html")
                if os.path.isfile(html_path):
                    with open(html_path, "r", encoding="utf-8") as f:
                        self._send_html(200, f.read())
                else:
                    self._send_html(200, "<!DOCTYPE html><html><body style='font-family:monospace;"
                                    "background:#050510;color:#aaccff;padding:40px;'>"
                                    "<h2>Æ Fused Bridge Online (Final, First edition)</h2>"
                                    "<p>index.html not found in <code>"
                                    + base + "</code>.</p></body></html>")
            except Exception as e:
                self._send_json(500, {"error": "read_index_failed", "detail": str(e)})
            return

        if not _require_auth(self):
            self._send_json(401, {"error": "unauthorized",
                                  "detail": "Missing or invalid X-Telegram-Init-Data"})
            return

        seed = BRIDGE_ENGINE_REF.get("seed")
        crawler = BRIDGE_ENGINE_REF.get("crawler")
        aeea = BRIDGE_ENGINE_REF.get("aeea")

        if path == "/config":
            self._send_json(200, {
                "version": "Final, First edition",
                "service": "ae-fused-bridge",
                "substrate": _SUBSTRATE,
                "tls": BRIDGE_USE_TLS,
                "require_auth": REQUIRE_AUTH,
                "symbol": (aeea.symbol if aeea else "BTC/USD"),
                "timeframe": (aeea.timeframe if aeea else "M15"),
                "seed_tick_interval": SEED_TICK_INTERVAL,
                "crawl_interval": CRAWL_INTERVAL,
                "max_crawl_depth": MAX_CRAWL_DEPTH,
                "telegram_db_enabled": ENABLE_TELEGRAM_DB,
                "gate_active": bool(ALLOWED_USER_IDS),
                "channel_optional": True,
                "push_on_signal": True,
                "push_on_execution": True,
                "push_on_fvg": True,
                "push_on_close": True,
                "arc_projection_horizon": 30,
                "arc_projection_step": 1,
                "arc_projection_damping": "0.94",
            })
            return

        if path == "/miniapp-state":
            import time as _t_fast
            _start_fast = _t_fast.time()
            try:
                global LAST_LIGHT_SNAPSHOT, LAST_LIGHT_AT
                with LAST_LIGHT_LOCK:
                    cached = LAST_LIGHT_SNAPSHOT
                    cached_at = LAST_LIGHT_AT
                if cached and (_t_fast.time() - cached_at) < 5.0:
                    snap = dict(cached)
                    try:
                        if seed is not None:
                            snap["tick"] = getattr(seed, 'tick', snap.get("tick", 0))
                    except Exception:
                        pass
                    self._send_json(200, snap)
                    return
                if seed is not None:
                    try:
                        if getattr(seed, '_cached_light_snapshot', None) and (_t_fast.time() - getattr(seed, '_cached_light_at', 0)) < 2.0:
                            snap = dict(seed._cached_light_snapshot)
                            snap["stale"] = False
                            self._send_json(200, snap)
                            return
                    except Exception:
                        pass
                placeholder = {
                    "state": getattr(seed, 'state', 'evolving') if seed else 'initializing',
                    "tick": getattr(seed, 'tick', 0) if seed else 0,
                    "generation": getattr(seed, 'generation', 0) if seed else 0,
                    "prime_count": len(getattr(seed, 'primes', [])) if seed else 0,
                    "lattice_points": 0,
                    "primes_tail": [],
                    "arc_sq": "0/1",
                    "radius_sq": "1/1",
                    "deviation_sq": "0/1",
                    "coherence": False,
                    "I": "0/1",
                    "hopf_base": ["0/1","0/1"],
                    "psi_real": "0/1",
                    "phi": {"a": "1/1", "b": "0/1", "c": "0/1", "d": "0/1"},
                    "phi_magnitude_sq": "1/1",
                    "trajectory": [],
                    "evolution": None,
                    "logic_core": {},
                    "history_tail": [],
                    "last_logic_hash": getattr(seed, 'last_logic_hash', '') if seed else '',
                    "stale": True,
                    "booting": (cached_at == 0),
                    "fast_cache": True,
                    "elapsed_ms": int((_t_fast.time() - _start_fast)*1000),
                }
                if crawler is not None:
                    try:
                        cs = getattr(crawler, 'state', None)
                        if cs is not None:
                            placeholder["crawler"] = {
                                "frontier_size": getattr(cs, '_frontier', []) and len(cs._frontier) or 0,
                                "visited_count": 0,
                                "running": getattr(crawler, '_running', False)
                            }
                        else:
                            placeholder["crawler"] = {"frontier_size": 0, "running": False}
                    except Exception:
                        placeholder["crawler"] = {"frontier_size": 0, "running": False}
                self._send_json(200, placeholder)
                return
            except Exception as e:
                try:
                    self._send_json(200, {"state": "evolving", "tick": 0, "generation": 0, "prime_count": 0, "lattice_points": 0, "deviation_sq": "0/1", "coherence": False, "stale": True, "fast_cache_error": str(e)[:100]})
                except Exception:
                    try:
                        body = b'{"state":"evolving","stale":true}'
                        self.send_response(200)
                        self.send_header("Content-Type", "application/json")
                        self.send_header("Content-Length", str(len(body)))
                        self.end_headers()
                        self.wfile.write(body)
                    except Exception:
                        pass
                return

        if path == "/state":
            if seed is None:
                self._send_json(503, {"error": "seed_not_ready"})
                return
            self._send_json(200, seed.snapshot())
            return

        if path == "/crawler-state":
            if crawler is None:
                self._send_json(503, {"error": "crawler_not_ready"})
                return
            snap = crawler.state.snapshot()
            snap["running"] = bool(getattr(crawler, "_running", False))
            snap["crawl_count"] = int(getattr(crawler, "_crawl_count", 0))
            snap["last_fetch_at"] = getattr(crawler, "_last_fetch_at", None) and crawler._last_fetch_at.isoformat() or None
            snap["relay_healthy"] = (crawler.relay.failure_count() < 3) if crawler.relay else False
            self._send_json(200, snap)
            return

        if path == "/crawler-queue":
            if crawler is None:
                self._send_json(503, {"error": "crawler_not_ready"})
                return
            queue_snap = crawler.state.snapshot()
            self._send_json(200, {
                "frontier_size": queue_snap.get("frontier_size", 0),
                "frontier_preview": queue_snap.get("frontier_preview", []),
                "visited_count": queue_snap.get("visited_count", 0),
            })
            return

        if path == "/symbolic-state":
            if seed is None:
                self._send_json(503, {"error": "seed_not_ready"})
                return
            self._send_json(200, {
                "primes_tail": [str(p) for p in seed.primes[-32:]],
                "prime_count": len(seed.primes),
                "psi_coeffs_count": len(seed.psi.coeffs),
                "psi_real": str(seed.psi.real_part()),
                "logic_core": {
                    k: {kk: str(vv) for kk, vv in v.items()} if isinstance(v, dict) else str(v)
                    for k, v in seed.evolution.logic_core.items()
                },
            })
            return

        if path == "/lattice-state":
            if seed is None:
                self._send_json(503, {"error": "seed_not_ready"})
                return
            points = seed.lattice.points()
            self._send_json(200, {
                "dimension": seed.lattice.dimension,
                "point_count": len(points),
                "outward": True,
                "tangent_first": True,
                "preview": [
                    [str(c) for c in p] for p in points[-8:]
                ],
            })
            return

        if path == "/fibration-state":
            if seed is None:
                self._send_json(503, {"error": "seed_not_ready"})
                return
            hopf = seed.last_hopf_base
            self._send_json(200, {
                "hopf_base_z": str(hopf[0]),
                "hopf_base_w": str(hopf[1]),
                "phi": {
                    "a": str(seed.phi.a), "b": str(seed.phi.b),
                    "c": str(seed.phi.c), "d": str(seed.phi.d),
                },
                "phi_magnitude_sq": str(seed.phi.magnitude_squared()),
                "trajectory": [
                    {"a": str(q.a), "b": str(q.b), "c": str(q.c), "d": str(q.d)}
                    for q in seed.last_trajectory
                ],
                "linguistic_trajectory": [
                    {"a": str(q.a), "b": str(q.b), "c": str(q.c), "d": str(q.d)}
                    for q in seed.last_linguistic_trajectory
                ],
            })
            return

        if path == "/observer-integral":
            if seed is None:
                self._send_json(503, {"error": "seed_not_ready"})
                return
            bounds = (
                (Fraction(0), Fraction(1)),
                (Fraction(0), Fraction(1)),
                (Fraction(0), Fraction(1)),
                (Fraction(0), Fraction(1)),
            )
            integral = seed.consciousness.compute_integral_exact(bounds, steps=4)
            self._send_json(200, {
                "integral": {
                    "a": str(integral.a), "b": str(integral.b),
                    "c": str(integral.c), "d": str(integral.d),
                },
                "magnitude_sq": str(integral.magnitude_squared()),
                "steps": 4,
                "bounds": [[str(b[0]), str(b[1])] for b in bounds],
            })
            return

        if path == "/evolution-state":
            if seed is None:
                self._send_json(503, {"error": "seed_not_ready"})
                return
            self._send_json(200, {
                "generation": seed.evolution.generation,
                "history_tail": seed.evolution.history[-20:],
                "logic_core": {
                    k: {kk: str(vv) for kk, vv in v.items()} if isinstance(v, dict) else str(v)
                    for k, v in seed.evolution.logic_core.items()
                },
                "last_logic_hash": seed.last_logic_hash,
            })
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

        if path == "/anchors":
            self._send_json(200, {"anchors": BRIDGE_STATE.list_anchors()})
            return

        if path == "/log":
            try:
                limit = int(query.get("limit", "50"))
            except (TypeError, ValueError):
                limit = 50
            with _LOG_LOCK:
                logs = list(_LOG_BUFFER)[-limit:]
            self._send_json(200, {"logs": logs, "count": len(logs)})
            return

        if path == "/seeds":
            if crawler is None:
                self._send_json(503, {"error": "crawler_not_ready"})
                return
            self._send_json(200, {
                "seed_urls": crawler.state.snapshot().get("frontier_preview", []),
            })
            return

        if path == "/ohlcv":
            if aeea is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            sym = query.get("symbol")
            if sym and sym != aeea.symbol:
                aeea.set_symbol(sym)
            self._send_json(200, aeea.get_ohlcv())
            return

        if path == "/signals":
            if aeea is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            sym = query.get("symbol")
            if sym and sym != aeea.symbol:
                aeea.set_symbol(sym)
            self._send_json(200, aeea.get_signals())
            return

        if path == "/diagnostics":
            if aeea is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            snap = aeea.snapshot()
            snap["ok"] = True
            snap["engine_initialized"] = True
            snap["signal_count"] = len(snap.get("signal_history", []))
            snap["bar_close_count"] = len(snap.get("bars", []))
            snap["relay_healthy"] = (crawler.relay.failure_count() < 3) if crawler and crawler.relay else False
            snap["provider"] = "ae-fused"
            snap["settings"] = {
                "bb_dev": aeea.bb_dev,
                "commission": aeea.commission,
                "point_size": aeea.point_size,
                "commission_frozen": aeea.commission_frozen,
                "trailing": aeea.trailing,
                "symbol": aeea.symbol,
                "timeframe": aeea.timeframe,
            }
            self._send_json(200, snap)
            return

        if path == "/orders":
            if aeea is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            with aeea._lock:
                open_orders = [
                    {
                        "order_id": o.order_id,
                        "side": o.side,
                        "volume": o.volume,
                        "entry": o.entry,
                        "sl": o.sl,
                        "tp": o.tp,
                        "status": o.status,
                        "fill_price": o.fill_price,
                        "created_at": o.created_at,
                    }
                    for o in aeea.orders if o.status in ("open", "filled")
                ]
            self._send_json(200, {"ok": True, "orders": open_orders, "count": len(open_orders)})
            return

        if path == "/settings":
            if aeea is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            self._send_json(200, {
                "symbol": aeea.symbol,
                "timeframe": aeea.timeframe,
                "bb_dev": aeea.bb_dev,
                "commission": aeea.commission,
                "point_size": aeea.point_size,
                "commission_frozen": aeea.commission_frozen,
                "trailing": aeea.trailing,
            })
            return

        self._send_json(404, {"error": "not_found", "path": path})

    def do_POST(self) -> None:
        path = urlparse(self.path).path

        if path == "/handshake":
            try:
                data = self._read_json()
                init_data = data.get("initData", "").strip()
                if not init_data:
                    auth_hdr = self.headers.get("X-Telegram-Init-Data", "").strip()
                    if auth_hdr:
                        init_data = auth_hdr
                chat_id = data.get("chat_id")
                if not init_data:
                    self._send_json(400, {"error": "missing_init_data"})
                    return
                verified = verify_telegram_init_data(init_data, TELEGRAM_BOT_TOKEN_ENV)
                if not verified or not verified.get("user"):
                    self._send_json(403, {"error": "invalid_init_data"})
                    return
                u = verified["user"] or {}
                user_id = u.get("id")
                username = u.get("username")
                if not _is_allowed_user(user_id):
                    self._send_json(403, {"error": "unauthorized_user"})
                    return
                BRIDGE_STATE.register_webapp_session(user_id, username, chat_id=chat_id)
                self._send_json(200, {
                    "ok": True, "user_id": user_id, "username": username,
                    "public_url": BRIDGE_ENGINE_REF.get("public_url"),
                    "session": {"user_id": user_id, "username": username},
                })
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return

        if not _require_auth(self):
            self._send_json(401, {"error": "unauthorized"})
            return

        seed = BRIDGE_ENGINE_REF.get("seed")
        crawler = BRIDGE_ENGINE_REF.get("crawler")
        aeea = BRIDGE_ENGINE_REF.get("aeea")

        if path == "/step":
            if seed is None:
                self._send_json(503, {"error": "seed_not_ready"})
                return
            data = self._read_json()
            try:
                x_raw = data.get("x")
                if x_raw is not None:
                    x = Fraction.from_string(str(x_raw))
                else:
                    x_num = int(data.get("x_num", seed.tick + 1))
                    x_den = int(data.get("x_den", 1))
                    x = Fraction(x_num, x_den)
            except Exception:
                x = Fraction(1, 100)
            record = seed.step(x)
            _emit_toast("seed", {
                "tick": record["tick"],
                "generation": record["generation"],
                "prime": record["prime"],
                "coherence": record["coherence"],
                "deviation_sq": record["deviation_sq"],
                "I": record["I"],
                "state": record["state"],
            })
            try:
                snap_fast = seed.snapshot(light=True)
                with LAST_LIGHT_LOCK:
                    LAST_LIGHT_SNAPSHOT = snap_fast
                    LAST_LIGHT_AT = time.time()
            except Exception:
                pass
            self._send_json(200, {"ok": True, "record": record})
            return

        if path == "/reset":
            if seed is None:
                self._send_json(503, {"error": "seed_not_ready"})
                return
            seed.primes = [Fraction(2), Fraction(3), Fraction(5)]
            seed.phi = SymbolicQuaternion(Fraction.one(), Fraction.zero(),
                                          Fraction.zero(), Fraction.zero())
            seed.psi = SymbolicWavefunction({(0, 0, 0, 0): Fraction.one()})
            seed.consciousness = ConsciousnessOperator(seed.psi, seed.phi)
            seed.state = "initialized"
            seed.tick = 0
            seed.generation = 0
            seed.history = []
            seed._prior_deviation_sq = None
            self._send_json(200, {"ok": True, "state": seed.snapshot()})
            return

        if path == "/crawler-enqueue":
            if crawler is None:
                self._send_json(503, {"error": "crawler_not_ready"})
                return
            data = self._read_json()
            url = str(data.get("url", "")).strip()
            if not url.startswith("http"):
                self._send_json(400, {"error": "invalid_url"})
                return
            depth = int(data.get("depth", 0))
            crawler.state.enqueue(url, depth=depth, priority=10)
            self._send_json(200, {"ok": True, "queued": True, "url": url, "depth": depth,
                                  "frontier_size": crawler.state.frontier_size()})
            return

        if path == "/encode-syllable":
            if seed is None:
                self._send_json(503, {"error": "seed_not_ready"})
                return
            data = self._read_json()
            syllable = str(data.get("syllable", "A"))
            try:
                result = seed.encode_syllable(syllable)
                self._send_json(200, {"ok": True, "result": result, "syllable": syllable})
            except Exception as e:
                self._send_json(500, {"error": "encode_failed", "detail": str(e)})
            return

        if path == "/anchor":
            data = self._read_json()
            try:
                q = SymbolicQuaternion(
                    Fraction.from_string(str(data.get("a", "1"))),
                    Fraction.from_string(str(data.get("b", "0"))),
                    Fraction.from_string(str(data.get("c", "0"))),
                    Fraction.from_string(str(data.get("d", "0"))),
                )
            except Exception as e:
                self._send_json(400, {"error": "invalid_quaternion", "detail": str(e)})
                return
            label = str(data.get("label", ""))
            idx = BRIDGE_STATE.add_anchor(q, label=label)
            self._send_json(200, {"ok": True, "idx": idx})
            return

        if path == "/orders":
            if aeea is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            data = self._read_json()
            side = (data.get("side") or "").upper()
            try:
                volume = float(data.get("volume", data.get("lot", 0.01)))
            except (TypeError, ValueError):
                volume = 0.01
            try:
                sl = float(data.get("sl", 0)) if data.get("sl") not in (None, "") else 0.0
            except (TypeError, ValueError):
                sl = 0.0
            try:
                tp = float(data.get("tp", 0)) if data.get("tp") not in (None, "") else 0.0
            except (TypeError, ValueError):
                tp = 0.0
            sym = data.get("symbol")
            if sym and sym != aeea.symbol:
                aeea.set_symbol(sym)
            result = aeea.place_order(side, volume, sl, tp, symbol=sym or aeea.symbol)
            if result.get("ok"):
                _emit_toast("execution", {
                    "event": "ManualOrder",
                    "side": side,
                    "price": str(aeea.price),
                    "ticket": result.get("order_id", -1),
                    "reason": "backend",
                    "tick": 0,
                })
                self._send_json(200, result)
            else:
                self._send_json(400, result)
            return

        if path == "/order/close":
            if aeea is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            data = self._read_json()
            try:
                if data.get("all"):
                    result = aeea.close_order(all=True)
                else:
                    order_id = data.get("order_id")
                    if order_id is None:
                        self._send_json(400, {"error": "missing_order_id"})
                        return
                    result = aeea.close_order(order_id=int(order_id))
                self._send_json(200, result)
            except Exception as e:
                self._send_json(500, {"error": "close_failed", "detail": str(e)})
            return

        if path == "/settings":
            if aeea is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            data = self._read_json()
            try:
                if "bb_dev" in data:
                    aeea.bb_dev = float(data["bb_dev"])
                if "commission" in data:
                    aeea.commission = float(data["commission"])
                    point = 10 ** (-aeea.SYMBOL_DIGITS.get(aeea.symbol, aeea.DEFAULT_DIGITS))
                    aeea.commission_frozen = aeea.commission * point
                if "trailing" in data:
                    aeea.trailing = float(data["trailing"])
                if "symbol" in data:
                    aeea.set_symbol(str(data["symbol"]))
                if "timeframe" in data:
                    aeea.timeframe = str(data["timeframe"])
                self._send_json(200, {
                    "ok": True,
                    "bb_dev": aeea.bb_dev,
                    "commission": aeea.commission,
                    "commission_frozen": aeea.commission_frozen,
                    "trailing": aeea.trailing,
                    "symbol": aeea.symbol,
                    "timeframe": aeea.timeframe,
                })
            except Exception as e:
                self._send_json(500, {"error": "settings_failed", "detail": str(e)})
            return

        if path == "/symbol":
            if aeea is None:
                self._send_json(503, {"error": "engine_not_ready"})
                return
            data = self._read_json()
            sym = str(data.get("symbol", "")).strip()
            if not sym:
                self._send_json(400, {"error": "missing_symbol"})
                return
            aeea.set_symbol(sym)
            self._send_json(200, {"ok": True, "symbol": aeea.symbol})
            return

        self._send_json(404, {"error": "not_found", "path": path})

    def do_DELETE(self) -> None:
        path = urlparse(self.path).path
        if not _require_auth(self):
            self._send_json(401, {"error": "unauthorized"})
            return
        m = _re_bridge.match(r"^/anchor/(\d+)$", path)
        if m:
            idx = int(m.group(1))
            ok = BRIDGE_STATE.remove_anchor(idx)
            if ok:
                self._send_json(200, {"ok": True, "idx": idx})
            else:
                self._send_json(404, {"error": "anchor_not_found", "idx": idx})
            return
        self._send_json(404, {"error": "not_found", "path": path})


# ============================================================================
# AUTH GUARD
# ============================================================================
def _require_auth(handler: "BridgeHandler") -> bool:
    try:
        p = urlparse(handler.path).path
        if p in ("/health", "/", "/favicon.ico"):
            return True
    except Exception:
        pass
    if not REQUIRE_AUTH or not TELEGRAM_BOT_TOKEN_ENV:
        return True
    raw_init = handler.headers.get("X-Telegram-Init-Data", "").strip()
    if not raw_init:
        auth_hdr = handler.headers.get("Authorization", "").strip()
        if auth_hdr.lower().startswith("tma "):
            raw_init = auth_hdr[4:].strip()
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
# BRIDGE SERVER
# ============================================================================
def _fqdn_fast(host: str) -> str:
    return host


class BridgeServer:
    def __init__(self, host: str = BRIDGE_HOST, port: int = BRIDGE_PORT):
        self.host = host
        self.port = int(port)
        self._httpd: Optional[ThreadingHTTPServer] = None
        self._thread: Optional[threading.Thread] = None
        self._ssl_context: Optional[ssl.SSLContext] = None
        self._listen_ready: threading.Event = threading.Event()
        self._listen_ok: bool = False

    def _build_ssl_context(self) -> Optional[ssl.SSLContext]:
        if not BRIDGE_USE_TLS:
            return None
        if not BRIDGE_TLS_CERT or not BRIDGE_TLS_KEY:
            logger.warning("BRIDGE_USE_TLS=1 but cert/key paths missing — falling back to HTTP")
            return None
        if not (os.path.isfile(BRIDGE_TLS_CERT) and os.path.isfile(BRIDGE_TLS_KEY)):
            logger.warning("TLS cert or key file not found — falling back to HTTP")
            return None
        try:
            ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            ctx.load_cert_chain(certfile=BRIDGE_TLS_CERT, keyfile=BRIDGE_TLS_KEY)
            logger.info(f"TLS enabled: cert={BRIDGE_TLS_CERT}")
            return ctx
        except Exception as e:
            logger.error(f"Failed to load TLS context: {e}")
            return None

    def start(self) -> None:
        if self._thread is not None:
            return
        bind_port = BRIDGE_PORT
        if _ENV_PORT:
            logger.info(f"Web-dyno substrate: binding to $PORT={bind_port}")
        else:
            logger.info(f"Local substrate: binding to BRIDGE_PORT={bind_port}")
        import socket as _socket_mod
        _orig_getfqdn = _socket_mod.getfqdn
        try:
            _socket_mod.getfqdn = _fqdn_fast
            try:
                ThreadingHTTPServer.allow_reuse_address = True
                self._httpd = ThreadingHTTPServer((self.host, bind_port), BridgeHandler)
                self._httpd.daemon_threads = True
                self.port = self._httpd.server_address[1]
                BRIDGE_ENGINE_REF["port"] = self.port
                self._ssl_context = self._build_ssl_context()
                if self._ssl_context is not None:
                    self._httpd.socket = self._ssl_context.wrap_socket(
                        self._httpd.socket, server_side=True)
            finally:
                _socket_mod.getfqdn = _orig_getfqdn
        except OSError as e:
            logger.error(f"Bridge server bind failed on {self.host}:{bind_port}: {e}")
            self._listen_ready.set()
            self._listen_ok = False
            return
        self._listen_ok = True
        BRIDGE_ENGINE_REF["bridge_server_ref"] = self
        self._thread = threading.Thread(
            target=lambda: self._httpd.serve_forever(poll_interval=0.1), name="ae-bridge", daemon=True
        )
        self._thread.start()
        scheme = "https" if self._ssl_context else "http"
        logger.info(f"AE Fused Bridge listening on {scheme}://{self.host}:{self.port}")
        if TELEGRAM_WEBAPP_URL:
            BRIDGE_ENGINE_REF["public_url"] = TELEGRAM_WEBAPP_URL
            logger.info("Public URL from TELEGRAM_WEBAPP_URL")
        elif _ENV_PORT:
            _domain = (os.getenv("HEROKU_APP_DEFAULT_DOMAIN_NAME", "") or "").strip()
            if _domain and "." in _domain and not _domain.startswith("http"):
                BRIDGE_ENGINE_REF["public_url"] = "https://" + _domain + "/"
                logger.info("Public URL from HEROKU_APP_DEFAULT_DOMAIN_NAME")
            elif _domain.startswith("https://"):
                BRIDGE_ENGINE_REF["public_url"] = _domain
                logger.info("Public URL from HEROKU_APP_DEFAULT_DOMAIN_NAME")
            else:
                BRIDGE_ENGINE_REF["public_url"] = None
                logger.warning(
                    "Web-dyno substrate but TELEGRAM_WEBAPP_URL is unset. "
                    "Set TELEGRAM_WEBAPP_URL=https://<your-app-domain>/ and re-run /setmenubutton."
                )
        else:
            BRIDGE_ENGINE_REF["public_url"] = None
        self._listen_ready.set()

    def stop(self) -> None:
        if self._httpd is not None:
            httpd = self._httpd
            self._httpd = None
            try:
                try:
                    httpd.socket.shutdown(2)
                except Exception:
                    pass
                try:
                    httpd.server_close()
                except Exception:
                    pass
            except Exception:
                pass
        self._thread = None
        self._httpd = None
        try:
            logger.info("AE Fused Bridge stopped (non-blocking)")
        except Exception:
            pass


# ============================================================================
# CRAWLER WORKER (async loop consuming relay)
# ============================================================================
class CrawlerWorker:
    DEFAULT_SEEDS = [
        "https://en.wikipedia.org/wiki/Riemann_hypothesis",
        "https://en.wikipedia.org/wiki/Leech_lattice",
        "https://en.wikipedia.org/wiki/Hopf_fibration",
        "https://en.wikipedia.org/wiki/Prime_number",
        "https://en.wikipedia.org/wiki/Quaternion",
        "https://en.wikipedia.org/wiki/Continued_fraction",
        "https://en.wikipedia.org/wiki/Chinese_remainder_theorem",
    ]

    def __init__(self, state: CrawlerSeedState, relay: CrawlerRelayClient,
                 seeds: Optional[List[str]] = None):
        self.state = state
        self.relay = relay
        self._running = False
        self._task: Optional[asyncio.Task] = None
        self._last_fetch_at: Optional[datetime] = None
        self._crawl_count = 0
        self._executor = _DaemonThreadPoolExecutor(max_workers=1, thread_name_prefix="ae-crawl")
        initial = seeds if seeds else self.DEFAULT_SEEDS
        if CRAWL_SEED_URLS:
            initial = [u.strip() for u in CRAWL_SEED_URLS.split(",") if u.strip()]
        for u in initial:
            self.state.enqueue(u, depth=0, priority=1)

    async def _loop(self):
        loop = asyncio.get_running_loop()
        consecutive_empty = 0
        while self._running:
            try:
                url = await loop.run_in_executor(self._executor, self.state.dequeue)
                if url is None:
                    consecutive_empty += 1
                    if consecutive_empty >= 10:
                        logger.info("crawler queue starvation: re-seeding frontier")
                        for seed_url in self.DEFAULT_SEEDS[:3]:
                            self.state.enqueue(seed_url, depth=0, priority=1)
                        consecutive_empty = 0
                    await asyncio.sleep(1.0)
                    continue
                consecutive_empty = 0
                payload = await loop.run_in_executor(self._executor, self.relay.fetch_url, url)
                if payload and payload.get("ok") and not payload.get("error"):
                    title = str(payload.get("title", ""))
                    content_hash = str(payload.get("content_hash", ""))
                    links = payload.get("links", []) or []
                    try:
                        depth = int(payload.get("depth", 0))
                    except (TypeError, ValueError):
                        depth = 0
                    self.state.record_visit(
                        url=url, title=title,
                        content_hash=content_hash,
                        depth=depth,
                        link_count=len(links),
                    )
                    if depth < MAX_CRAWL_DEPTH:
                        for link in links[:16]:
                            if isinstance(link, str) and link.startswith("http"):
                                self.state.enqueue(link, depth=depth + 1, priority=0)
                    self._last_fetch_at = datetime.now()
                    self._crawl_count += 1
                else:
                    if self.relay.failure_count() >= 3:
                        logger.info(f"crawl skipped: {url} (no payload) — circuit breaker active")
                    elif "meta.wikimedia.org" in url.lower() or "wikimedia.org" in url.lower():
                        logger.info(f"crawl skipped: {url} (no payload) — blocked domain")
                    else:
                        logger.info(f"crawl skipped: {url} (no payload) — re-enqueue low priority")
                        try:
                            self.state.enqueue(url, depth=1, priority=-1)
                        except Exception:
                            pass
                if self.relay.failure_count() >= 3:
                    await asyncio.sleep(10.0)
                else:
                    await asyncio.sleep(CRAWL_INTERVAL)
            except asyncio.CancelledError:
                break
            except Exception as e:
                logger.warning(f"crawl loop error: {e}")
                await asyncio.sleep(2.0)

    def start(self):
        if self._running:
            return
        self._running = True
        self._task = asyncio.create_task(self._loop())

    def stop(self):
        self._running = False
        if self._task and not self._task.done():
            self._task.cancel()
        try:
            self._executor.shutdown(wait=False, cancel_futures=True)
        except Exception:
            pass

    def snapshot(self) -> Dict[str, Any]:
        snap = self.state.snapshot()
        snap.update({
            "running": self._running,
            "crawl_count": self._crawl_count,
            "last_fetch_at": self._last_fetch_at.isoformat() if self._last_fetch_at else None,
            "relay_healthy": (self.relay.failure_count() < 3),
        })
        return snap


# ============================================================================
# SEED WORKER (async loop: market tick -> ÆI step with lifted x)
# ============================================================================
class SeedWorker:
    def __init__(self, seed: AEI_Seed, crawler: CrawlerWorker, aeea: AEEA_Engine):
        self.seed = seed
        self.crawler = crawler
        self.aeea = aeea
        self._running = False
        self._task: Optional[asyncio.Task] = None
        self._executor = _DaemonThreadPoolExecutor(max_workers=1, thread_name_prefix="ae-seed-step")

    def _lift_market_x(self) -> Fraction:
        try:
            p = self.aeea.price
            prev = self.aeea.prev_price
            if prev > 0 and p > 0:
                delta = abs(p - prev)
                if delta == 0:
                    return Fraction(1, 100)
                num = int(round(delta * 10000))
                if num <= 0:
                    num = 1
                return Fraction(num, 10000)
        except Exception:
            pass
        try:
            hash_frac = self.crawler.state.latest_hash_fraction()
            if hash_frac != PyFraction(0, 1):
                return Fraction(hash_frac)
        except Exception:
            pass
        return Fraction(1, 100)

    async def _loop(self):
        consecutive_timeouts = 0
        gc_counter = 0
        while self._running:
            try:
                x = self._lift_market_x()
                loop = asyncio.get_running_loop()
                try:
                    if getattr(self.seed, '_cached_light_snapshot', None):
                        with LAST_LIGHT_LOCK:
                            LAST_LIGHT_SNAPSHOT = dict(self.seed._cached_light_snapshot)
                            LAST_LIGHT_AT = time.time()
                except Exception:
                    pass
                try:
                    record = await asyncio.wait_for(
                        loop.run_in_executor(self._executor, self.seed.step, x),
                        timeout=30,
                    )
                    consecutive_timeouts = 0
                    try:
                        snap_fast = self.seed.snapshot(light=True)
                        with LAST_LIGHT_LOCK:
                            LAST_LIGHT_SNAPSHOT = snap_fast
                            LAST_LIGHT_AT = time.time()
                    except Exception:
                        pass
                except asyncio.TimeoutError:
                    consecutive_timeouts += 1
                    logger.warning(f"seed loop timeout: step exceeded 30s (tick={self.seed.tick}) consecutive={consecutive_timeouts}")
                    if consecutive_timeouts >= 3:
                        try:
                            self._executor.shutdown(wait=False, cancel_futures=True)
                        except Exception:
                            pass
                        try:
                            self._executor = _DaemonThreadPoolExecutor(max_workers=1, thread_name_prefix="ae-seed-step")
                        except Exception:
                            pass
                        consecutive_timeouts = 0
                    await asyncio.sleep(2.0)
                    continue
                _emit_toast("seed", {
                    "tick": record["tick"],
                    "generation": record["generation"],
                    "prime": record["prime"],
                    "coherence": record["coherence"],
                    "deviation_sq": record["deviation_sq"],
                    "I": record["I"],
                    "state": record["state"],
                })
                try:
                    if TELEGRAM_DB and TELEGRAM_DB.is_enabled():
                        evo = record.get("evolution", {}) or {}
                        db_disc = evo.get("db_discretion", {}) if isinstance(evo, dict) else {}
                        interval_mod = int(db_disc.get("save_interval_mod", 1) or 1)
                        should_save = (gc_counter % (TELEGRAM_DB_SAVE_INTERVAL * interval_mod) == 0)
                        if should_save:
                            db_key = db_disc.get("db_key", "𝒮_STATUS")
                            db_key_alt = db_disc.get("db_key_alt")
                            save_global = bool(db_disc.get("save_global", True))
                            save_user = bool(db_disc.get("save_user", False))
                            shard_targets = db_disc.get("shard_targets", []) or []
                            if save_global:
                                TELEGRAM_DB.save_snapshot(db_key, record, force=False)
                                if db_key_alt:
                                    TELEGRAM_DB.save_snapshot(db_key_alt, {
                                        "prime_count": record.get("prime_count"),
                                        "lattice_points": record.get("lattice_points"),
                                        "generation": record.get("generation"),
                                        "tick": record.get("tick"),
                                    }, force=False)
                            if TELEGRAM_DB_USER_SHARDS and save_user and shard_targets:
                                for uid in shard_targets[:2]:
                                    TELEGRAM_DB.save_user_shard(int(uid), db_key, record)
                except Exception as _edb_e:
                    logger.warning(f"TelegramDB learned save failed: {_edb_e}")
                gc_counter += 1
                if gc_counter % 15 == 0:
                    try:
                        gc.collect()
                    except Exception:
                        pass
                await asyncio.sleep(SEED_TICK_INTERVAL)
            except asyncio.CancelledError:
                break
            except Exception as e:
                logger.warning(f"seed loop error: {type(e).__name__}: {e}")
                await asyncio.sleep(2.0)

    def start(self):
        if self._running:
            return
        self._running = True
        self._task = asyncio.create_task(self._loop())

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
# MARKET TICK WORKER (drives the ordered feed from the backend side)
# ============================================================================
class MarketTickWorker:
    def __init__(self, aeea: AEEA_Engine, relay: CrawlerRelayClient):
        self.aeea = aeea
        self.relay = relay
        self._running = False
        self._task: Optional[asyncio.Task] = None
        self._executor = _DaemonThreadPoolExecutor(max_workers=1, thread_name_prefix="ae-mkt")
        self._synth_price = 100.0
        self._synth_seed = 12345
        self._ordered_index = 0

    def _fetch_price_sync(self) -> Tuple[float, str]:
        sym = self.aeea.symbol
        if "BTC" in sym or "ETH" in sym or "SOL" in sym or "XRP" in sym or "DOGE" in sym or "ADA" in sym or "AVAX" in sym or "LINK" in sym or "TON" in sym or "GRAM" in sym:
            pair = sym.replace("/", "")
            try:
                url = f"https://api.kraken.com/0/public/Ticker?pair={pair}"
                req = urllib.request.Request(url, headers={"Accept": "application/json", "User-Agent": "AE-Fused-Mkt/1.0"})
                with urllib.request.urlopen(req, timeout=5) as resp:
                    raw = json.loads(resp.read().decode("utf-8"))
                    result = raw.get("result") or {}
                    key = next(iter(result), None)
                    if key:
                        last = float(result[key]["c"][0])
                        if last > 0 and is_finite_number(last):
                            return last, "Kraken"
            except Exception:
                pass
        self._synth_seed = (self._synth_seed * 1103515245 + 12345) % 2147483648
        r = (self._synth_seed / 2147483648 - 0.5) * 2
        self._synth_price = max(1.0, self._synth_price + self._synth_price * 0.002 * r)
        return self._synth_price, "synthetic"

    async def _loop(self):
        loop = asyncio.get_running_loop()
        while self._running:
            try:
                price, provider = await loop.run_in_executor(self._executor, self._fetch_price_sync)
                if is_finite_number(price) and price > 0:
                    self._ordered_index += 1
                    self.aeea.on_tick(price, 1.0, self._ordered_index)
            except asyncio.CancelledError:
                break
            except Exception as e:
                logger.warning(f"market tick error: {e}")
            await asyncio.sleep(3.0)

    def start(self):
        if self._running:
            return
        self._running = True
        self._task = asyncio.create_task(self._loop())

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
# TELEGRAM BOT (minimal — /handshake, /start, /webapp, /whoami)
# ============================================================================
try:
    from telegram import Update, WebAppInfo, MenuButtonWebApp
    from telegram.ext import Application, CommandHandler, ContextTypes
    TELEGRAM_AVAILABLE = True
except ImportError:
    TELEGRAM_AVAILABLE = False
    logger.warning("python-telegram-bot not installed; bot commands disabled")


class AE_Bot:
    def __init__(self, token: str, bot_name: str = "AEFusedBot"):
        self.token = token
        self.bot_name = bot_name
        self.application = None
        self._loop: Optional[asyncio.AbstractEventLoop] = None
        self._bridge_server: Optional[BridgeServer] = None
        self._seed_worker: Optional[SeedWorker] = None
        self._crawler_worker: Optional[CrawlerWorker] = None
        self._market_worker: Optional[MarketTickWorker] = None
        self._async_loop: Optional[asyncio.AbstractEventLoop] = None
        self._async_thread: Optional[threading.Thread] = None

    async def _post_init(self, application) -> None:
        try:
            self._loop = asyncio.get_running_loop()
            logger.info("Event loop captured")
        except RuntimeError:
            self._loop = None
        BRIDGE_ENGINE_REF["bot"] = self
        if self._bridge_server is None:
            server = BridgeServer()
            self._bridge_server = server
            boot_thread = threading.Thread(
                target=server.start, name="ae-bridge-boot", daemon=True
            )
            boot_thread.start()
            ready = server._listen_ready.wait(timeout=BRIDGE_PUBLIC_TIMEOUT)
            if not ready or not server._listen_ok:
                logger.error(
                    f"Bridge failed to bind within {BRIDGE_PUBLIC_TIMEOUT}s; workers will not start"
                )
                return
            logger.info("Bridge binding verified")
        url = TELEGRAM_WEBAPP_URL or BRIDGE_ENGINE_REF.get("public_url")
        if url:
            try:
                await application.bot.set_chat_menu_button(
                    menu_button=MenuButtonWebApp(
                        text="Æ TWA", web_app=WebAppInfo(url=url),
                    )
                )
                logger.info(f"MenuButtonWebApp registered: {url}")
            except Exception as e:
                logger.warning(f"Failed to set menu button: {e}")
        else:
            logger.info("MenuButtonWebApp deferred — no public URL yet")
        seed = BRIDGE_ENGINE_REF.get("seed")
        crawler = BRIDGE_ENGINE_REF.get("crawler")
        aeea = BRIDGE_ENGINE_REF.get("aeea")
        if seed is not None and crawler is not None and aeea is not None:
            crawler.start()
            market = MarketTickWorker(aeea, crawler.relay)
            market.start()
            seed_worker = SeedWorker(seed, crawler, aeea)
            seed_worker.start()
            self._crawler_worker = crawler
            self._seed_worker = seed_worker
            self._market_worker = market
            logger.info("AE seed + crawler + market workers started")
        else:
            logger.warning("_post_init ran before seed/crawler/aeea were registered")

    async def start(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        await update.message.reply_text(
            "🔷 Æ TWA — Fusion of ÆI (seed) + ÆEA (market)\n"
            "/webapp — open the Mini App\n"
            "/whoami — your Telegram user ID\n"
            "One ordered feed → ÆEA market engine → ÆI seed step with lifted x."
        )

    async def webapp(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        url = TELEGRAM_WEBAPP_URL or BRIDGE_ENGINE_REF.get("public_url")
        if not url:
            await update.message.reply_text(
                "Mini App URL not yet available. Set TELEGRAM_WEBAPP_URL on the dyno."
            )
            return
        from telegram import InlineKeyboardButton, InlineKeyboardMarkup
        keyboard = InlineKeyboardMarkup([[
            InlineKeyboardButton("⚡ Open Æ TWA", web_app=WebAppInfo(url=url)),
        ]])
        await update.message.reply_text("Tap to launch the Æ TWA.", reply_markup=keyboard)

    async def whoami(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        u = update.effective_user
        uid = u.id if u else None
        allowed = _is_allowed_user(uid)
        await update.message.reply_text(
            f"user_id: {uid}\n"
            f"username: @{u.username if u and u.username else '—'}\n"
            f"gate: {'✅ allowed' if allowed else '❌ blocked'}\n"
            f"gate active: {'yes' if ALLOWED_USER_IDS else 'no (open bot)'}"
        )

    async def error_handler(self, update, context):
        err = context.error
        err_str = f"{type(err).__name__}: {err}" if err is not None else "unknown"
        if "Conflict" in err_str or "terminated by other getUpdates" in err_str:
            logger.warning("Conflict detected (another bot instance): sleeping 5s")
            await asyncio.sleep(5.0)
            return
        logger.error(f"handler error: {err_str}")

    def _async_worker_loop(self):
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        self._async_loop = loop

        async def _start_workers():
            await self._post_init(self.application)

        try:
            loop.run_until_complete(_start_workers())
            loop.run_forever()
        except Exception as e:
            logger.error(f"async worker loop error: {e}")
        finally:
            try:
                loop.close()
            except Exception:
                pass

    def run(self):
        if not TELEGRAM_AVAILABLE:
            logger.error("python-telegram-bot not installed; cannot run bot")
            return
        global TELEGRAM_DB
        TELEGRAM_DB = TelegramChatDB(
            TELEGRAM_BOT_TOKEN_ENV,
            TELEGRAM_DB_CHANNEL_ID,
            TELEGRAM_DB_CENTRAL_USER_ID,
            chunk_size=TELEGRAM_DB_CHUNK_SIZE,
        )
        if TELEGRAM_DB.is_enabled():
            logger.info(f"TelegramChatDB enabled: user_shards={TELEGRAM_DB_USER_SHARDS}")
        else:
            logger.info("TelegramChatDB disabled (set ENABLE_TELEGRAM_DB=1 + CHANNEL_ID or CENTRAL_USER_ID)")

        crawler_state = CrawlerSeedState(CRAWLER_DB_PATH)
        relay = CrawlerRelayClient(RELAY_URL, RELAY_KEY, timeout=RELAY_TIMEOUT,
                                   max_retries=RELAY_MAX_RETRIES)
        crawler = CrawlerWorker(crawler_state, relay)
        seed = AEI_Seed(
            processor=DefaultSymbolicProcessor(),
            lattice=DefaultGeometricLattice(),
            monitor=DefaultAethericMonitor(),
            renderer=DefaultQuaternionicRenderer(),
            linguist=DefaultLingosoEncoder(),
        )
        aeea = AEEA_Engine(symbol=os.getenv("SYMBOL", "BTC/USD"),
                           timeframe=os.getenv("TIMEFRAME", "M15"))
        BRIDGE_ENGINE_REF["seed"] = seed
        BRIDGE_ENGINE_REF["crawler"] = crawler
        BRIDGE_ENGINE_REF["aeea"] = aeea

        self.application = (
            Application.builder()
            .token(self.token)
            .build()
        )
        self.application.add_handler(CommandHandler("start", self.start))
        self.application.add_handler(CommandHandler("webapp", self.webapp))
        self.application.add_handler(CommandHandler("mini", self.webapp))
        self.application.add_handler(CommandHandler("whoami", self.whoami))
        self.application.add_error_handler(self.error_handler)

        self._async_thread = threading.Thread(
            target=self._async_worker_loop, name="ae-async-workers", daemon=True
        )
        self._async_thread.start()

        logger.info(f"🤖 {self.bot_name} starting... pid={os.getpid()}")
        logger.info(f"AE Fused — seed + ÆEA + crawler + market on one ordered feed")
        logger.info(f"Seed tick: {SEED_TICK_INTERVAL}s | Crawl: {CRAWL_INTERVAL}s | Market: 3s")
        logger.info(f"Relay configured: {bool(RELAY_URL)}")
        logger.info(f"Bridge: http://{BRIDGE_HOST}:{BRIDGE_PORT}")

        try:
            self.application.run_polling(
                allowed_updates=Update.ALL_TYPES,
                stop_signals=[],
                close_loop=False,
                drop_pending_updates=True,
            )
        except TypeError:
            self.application.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


# ============================================================================
# MAIN ENTRY POINT
# ============================================================================
def main():
    import signal
    _shutdown_event = threading.Event()

    def _install_handlers(tag=""):
        try:
            def _handler(signum, frame):
                print(f"⚡ SIG {signum} -> graceful shutdown pid={os.getpid()}", flush=True)
                _shutdown_event.set()
            signal.signal(signal.SIGTERM, _handler)
            signal.signal(signal.SIGINT, _handler)
        except Exception as _e:
            print(f"signal install failed {tag}: {_e}", flush=True)

    try:
        os.environ["WEB_CONCURRENCY"] = "1"
    except Exception:
        pass
    _install_handlers("boot")

    if not TELEGRAM_BOT_TOKEN_ENV:
        logger.error("❌ TELEGRAM_BOT_TOKEN not set.")
        sys.exit(1)

    bot = AE_Bot(TELEGRAM_BOT_TOKEN_ENV, "AEFusedBot")

    def _bot_thread():
        try:
            try:
                loop = asyncio.new_event_loop()
                asyncio.set_event_loop(loop)
            except Exception:
                pass
            bot.run()
        except Exception as e:
            try:
                print(f"Bot thread error: {e}", flush=True)
            except Exception:
                pass

    t = threading.Thread(target=_bot_thread, name="ae-bot-polling", daemon=True)
    t.start()

    _loop_count = 0
    try:
        while not _shutdown_event.is_set():
            try:
                _shutdown_event.wait(timeout=1.0)
            except Exception:
                time.sleep(0.5)
            _loop_count += 1
            if _loop_count % 10 == 0:
                print(f"♥ main heartbeat {_loop_count} pid={os.getpid()}", flush=True)
    except KeyboardInterrupt:
        print("KeyboardInterrupt -> shutdown", flush=True)
        _shutdown_event.set()
    except Exception as _e:
        print(f"main loop exception {_e} -> shutdown", flush=True)
        _shutdown_event.set()

    try:
        c = BRIDGE_ENGINE_REF.get("crawler")
        if c:
            c.stop()
        if bot._market_worker:
            bot._market_worker.stop()
        if bot._seed_worker:
            bot._seed_worker.stop()
        if bot._bridge_server:
            bot._bridge_server.stop()
    except Exception:
        pass

    print("⚡ main exiting cleanly", flush=True)
    try:
        time.sleep(1.0)
    except Exception:
        pass
    sys.exit(0)


if __name__ == "__main__":
    main()

# ============================================================================
# Final, First edition — Æ TWA Fused Backend
# ============================================================================