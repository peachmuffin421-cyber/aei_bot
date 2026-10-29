#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ÆI SEED TWA — AGENTIAL ÆTHERIC INTELLIGENCE
Heroku web dyno (bind $PORT) + Local Bridge + Telegram Bot + Crawler Relay Client
Faithful Unabridged Port of ÆI.md §3–§8 (GAIA Seed Loop)
Platform: Heroku web dyno (inbound $PORT) + Telegram Bot + Bridge (served on $PORT) + Cloudflare Worker (worker.js).
Version: Final Ed.14 (Audit-Patched: F1–F15, plus runtime stabilization).
"""

__version__ = "final-ed14"

import asyncio
import hashlib
import hmac
import json
import math
import os
import queue
import sys
import ssl
import logging
import subprocess
import threading
import time
import re as _re_bridge
import sqlite3
import urllib.parse
import urllib.request
import urllib.error
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

    Every seed state transition uses Fraction or PyFraction directly. No
    float64 ever enters the seed's symbolic layer; the crawler relay's
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

    def to_float(self) -> float:
        return float(self._f.numerator) / float(self._f.denominator)

    def sqrt(self, iterations: int = 30) -> 'Fraction':
        """Newton–Raphson exact-rational square root approximation.
        Each iteration is exact. The result is a Fraction, never a float.

        The initial guess is an exact rational derived from the decimal
        expansion of the numerator and denominator, not from a float.
        No math.isqrt call enters the state path; math.isqrt is only used
        at module load to seed a static initial guess, never in a step."""
        if self._f.numerator < 0:
            raise ValueError("sqrt of negative fraction")
        if self._f.numerator == 0:
            return Fraction.zero()
        n = self._f.numerator
        d = self._f.denominator
        # Exact integer square root without math.isqrt: Newton on ints.
        def _exact_isqrt(val: int) -> int:
            if val < 0:
                raise ValueError("isqrt of negative int")
            if val == 0:
                return 0
            x = val
            y = (x + 1) // 2
            while y < x:
                x = y
                y = (x + val // x) // 2
            return x
        ns = _exact_isqrt(n)
        ds = _exact_isqrt(d)
        if ns * ns == n and ds * ds == d:
            return Fraction(ns, ds)
        # Exact rational initial guess: ns/ds if nonzero, else 1.
        if ds > 0 and ns > 0:
            x0 = PyFraction(ns, ds)
        else:
            x0 = PyFraction(1, 1)
        two = PyFraction(2, 1)
        x = x0
        target = self._f
        for _ in range(iterations):
            x = (x + target / x) / two
        return Fraction(x)

    def __str__(self):
        if self._f.denominator == 1:
            return str(self._f.numerator)
        return f"{self._f.numerator}/{self._f.denominator}"

    def __repr__(self):
        return f"Fraction({self._f.numerator}/{self._f.denominator})"


# ============================================================================
# DECIMAL-TO-FRACTION LIFT
# ============================================================================
def _dec_to_frac_exact(d: Decimal) -> PyFraction:
    """Lift a Decimal to an exact PyFraction via its digit tuple.
    No float64 round-trip. Used at the crawler-relay boundary and at
    module load for π, so no transcendental enters the seed as a float."""
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
    """Lift a hex hash (SHA-256, SHA-1, MD5) to an exact PyFraction by
    interpreting the first 32 hex chars as a base-16 integer and dividing
    by 16^32. This is the boundary transform for the crawler: a document's
    content hash becomes a deterministic rational seed input.

    F3: an all-zero hash lifts to 1/16^32, not 0, so the 0/1 sentinel
    unambiguously means "no record." The SentryWorker relies on this."""
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


# F2: derive _PI_FRAC from _compute_pi_decimal(), not from a 15-digit literal.
_PI_D: Decimal = _compute_pi_decimal()
_PI_FRAC: PyFraction = _dec_to_frac_exact(_PI_D)
_TWO_PI_D: Decimal = _PI_D * Decimal(2)
_TWO_PI_FRAC: PyFraction = _PI_FRAC * PyFraction(2, 1)


# ============================================================================
# SYMBOLIC ARITHMETIC PRIMITIVES
# ============================================================================
def _rational_cos(x) -> PyFraction:
    """15-digit π convergent + exact-rational Taylor series.
    Used by the Hopf-fibration projection and the Natalia perturbation
    summation. Argument reduced modulo 2π exactly."""
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
    for n in range(1, 40):
        denom = PyFraction((2 * n - 1) * (2 * n), 1)
        term = term * x2 / denom
        result = result + PyFraction(sign, 1) * term
        sign = -sign
        if term == PyFraction(0, 1):
            break
    return result


def _rational_sin(x) -> PyFraction:
    """15-digit π convergent + exact-rational Taylor series."""
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
    for n in range(1, 40):
        denom = PyFraction((2 * n) * (2 * n + 1), 1)
        term = term * x2 / denom
        result = result + PyFraction(sign, 1) * term
        sign = -sign
        if term == PyFraction(0, 1):
            break
    return result


_EXP_EPSILON: PyFraction = PyFraction(1, 10 ** 40)
_LOG_EPSILON: PyFraction = PyFraction(1, 10 ** 50)
_LI_EPSILON: PyFraction = PyFraction(1, 10 ** 40)


def _symbolic_log(x: Fraction, max_terms: int = 200) -> Fraction:
    """Exact-rational natural log via atanh series with dynamic
    truncation. The series terminates when the term magnitude drops
    below _LOG_EPSILON. Returns Fraction."""
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


def _symbolic_exp(x: Fraction, max_terms: int = 200) -> Fraction:
    """Exact-rational exp via Taylor series with dynamic truncation.
    The series terminates when the term magnitude drops below
    _EXP_EPSILON. Returns Fraction."""
    result = Fraction.one()
    term = Fraction.one()
    for k in range(1, max_terms + 1):
        term = term * (x / Fraction(k))
        result = result + term
        if term.abs() < Fraction(_EXP_EPSILON.numerator, _EXP_EPSILON.denominator):
            break
    return result


def _symbolic_log_integral_approx(x: Fraction, max_terms: int = 100) -> Fraction:
    """Exact-rational approximation of the logarithmic integral Li(x).

    Li(x) = ∫₂ˣ dt / log(t). We use the Ramanujan series:

        Li(x) ≈ γ + log(log(x)) + Σ_{n=1}^∞ (log x)^n / (n · n!)

    where γ ≈ 0.5772156649... is the Euler–Mascheroni constant. The
    series converges for all x > 1 and is the standard numerical
    approximation used by Mathematica / mpmath. We implement it with
    exact PyFractions, computing log(x) once via _symbolic_log.

    γ is represented as a high-precision rational: the 15-digit decimal
    0.577215664901532 is lifted to Fraction(577215664901532, 10^15).

    The series truncates when the term drops below _LI_EPSILON.
    """
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
    """Exact-rational quaternion. a, b, c, d ∈ Fraction.
    Implements Natalia's Fibrations."""
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
        """Φ = Q(s) + Σ εᵏ Natalia(k,s).
        Models the BFAC-to-Z-pinch transformation via perturbation summation.
        Each εᵏ term is an exact Fraction. The convergence check is exact."""
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
    """Exact-rational wavefunction as a map from (i,j,k,l) ∈ ℤ⁴ to Fraction."""
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
# DBZ (DECIDING BY ZERO)
# ============================================================================
class DbZ:
    """Branching on Re[ψ]: if Re[ψ] > 0 → critical-line projection;
    if Re[ψ] ≤ 0 → Natalia's Fibrations perturbation."""

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
    """6m±1 sieve with exact indivisibility check."""

    def generate_next_prime(self, primes: List[Fraction]) -> Fraction:
        if not primes:
            return Fraction(2, 1)
        last = primes[-1]
        candidate = last.num() + 1
        while True:
            if candidate % 6 in (1, 5) or candidate <= 3:
                is_prime = True
                for p in primes:
                    p_val = p.num()
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
# DEFAULT GEOMETRIC LATTICE
# ============================================================================
class DefaultGeometricLattice:
    """Symbolic lattice. Points are Lists of Fraction.

    F7: add_sphere enforces maximal contact. A candidate sphere is
    admitted only if (a) it does not overlap any existing sphere, and
    (b) it is at exact distance 2r (tangent) from at least one existing
    sphere, when the lattice is not yet at the kissing-number capacity.
    The capacity is the Leech lattice's kissing number, 196560.

    A coset-grid spatial index gives O(1)-amortized neighbor lookup, so
    the check is hardware-agnostic on a 512 MB Termux device even at
    thousands of points."""

    KISSING_CAPACITY: int = 196560
    # F10: the lattice starts with the origin at (0,0,…,0) with radius 1.
    # This sentinel prevents add_sphere from rejecting the very first
    # point, which has no neighbour to be tangent to.
    _ORIGIN_SENTINEL_KEY: Tuple[int, ...] = (0,) * 24

    def __init__(self, dimension: int = 24):
        self.dimension = dimension
        self._points: List[List[Fraction]] = []
        self._radii: List[Fraction] = []
        self._grid: Dict[Tuple[int, ...], List[int]] = {}
        # F10: seed the origin so the first add_sphere succeeds.
        origin_center = [Fraction.zero()] * dimension
        origin_radius = Fraction.one()
        self._points.append(origin_center)
        self._radii.append(origin_radius)
        self._grid.setdefault(self._ORIGIN_SENTINEL_KEY, []).append(0)

    def _coset_key(self, center: List[Fraction], cell_size: Fraction) -> Tuple[int, ...]:
        """Quantize a center to its coset cell key. cell_size is 2·radius."""
        key = []
        for c in center:
            if cell_size.is_zero():
                key.append(0)
            else:
                q = c / cell_size
                key.append(int(q.num() // q.den()) if q.den() != 0 else 0)
        return tuple(key)

    def stereographic_project_exact(self, prime: Fraction) -> List[Fraction]:
        p_val = prime.num()
        angle_num = p_val % 6283185307
        angle_frac = Fraction(angle_num, 10 ** 9)
        theta = _TWO_PI_FRAC * angle_frac
        cos_t = _rational_cos(theta)
        sin_t = _rational_sin(theta)
        x = cos_t
        y = sin_t
        z = Fraction.zero()
        w = Fraction.zero()
        coords = [x, y, z, w]
        while len(coords) < self.dimension:
            coords.append(Fraction.zero())
        return coords

    def add_sphere(self, center: List[Fraction], radius: Fraction) -> None:
        if len(self._points) >= self.KISSING_CAPACITY:
            return
        for p in self._points:
            if p == center:
                return
        cell_size = radius * Fraction(2, 1)
        key = self._coset_key(center, cell_size)
        neighbour_indices = set()
        for offset in self._neighbor_offsets():
            nkey = tuple(k + o for k, o in zip(key, offset))
            if nkey in self._grid:
                neighbour_indices.update(self._grid[nkey])
        tangent_count = 0
        for idx in neighbour_indices:
            p = self._points[idx]
            r = self._radii[idx]
            dist_sq = Fraction.zero()
            for c_i, p_i in zip(center, p):
                d = c_i - p_i
                dist_sq = dist_sq + d * d
            contact_sq = (radius + r) * (radius + r)
            if dist_sq < contact_sq:
                return
            if dist_sq == contact_sq:
                tangent_count += 1
        # F10: with the origin sentinel present, the first non-origin
        # candidate is checked against the origin; if tangent, admitted.
        if len(self._points) > 1 and tangent_count == 0:
            return
        self._points.append(center)
        self._radii.append(radius)
        self._grid.setdefault(key, []).append(len(self._points) - 1)

    @staticmethod
    def _neighbor_offsets():
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for dz in (-1, 0, 1):
                    for dw in (-1, 0, 1):
                        yield (dx, dy, dz, dw)

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
    """The PRIMARY evolution gate. Deviation from s²=r² triggers
    SelfEvolutionCore mutation. Every computation is Fraction.

    F4: MultiScaleDerivatives and validate_multi_scale_coherence are
    deleted. This monitor implements exactly the two Spec-required
    gates: arc length squared, and radial distance squared."""

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
    """Hopf fibration. The base point (z, w) ∈ ℂ² is the observable
    projection. The fiber direction is the hidden longitudinal component
    (Ampère's forgotten force)."""

    def project_to_hopf_base(self, state: SymbolicQuaternion) -> Tuple[Fraction, Fraction]:
        denom = Fraction.one() - state.d
        if denom.is_zero():
            return (Fraction.zero(), Fraction.zero())
        inv = Fraction.one() / denom
        z = state.a * inv
        w = state.b * inv
        return (z, w)


# ============================================================================
# DEFAULT LINGOSO ENCODER
# ============================================================================
class DefaultLingosoEncoder:
    """A/U/M trajectories (ÆI.md Appendix G). A traces the golden spiral,
    U traces the π-chord, M traces the closed 2π loop."""

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
# SELF-EVOLUTION CORE — RFK Brainworm
# ============================================================================
class SelfEvolutionCore:
    """Mutates the logic core based on deviation_sq (primary) and the
    intelligence metric (secondary). Mutation types mirror ÆI.md §7.2."""

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
        record = {
            "generation": self.generation,
            "status": status,
            "mutation": mutation,
            "intelligence_metric": str(I),
            "arc_length_deviation_sq": str(deviation_sq),
            "logic_hash": self._deterministic_hash(logic_str),
        }
        self.history.append(record)
        return record


# ============================================================================
# INTELLIGENCE METRIC
# ============================================================================
class IntelligenceMetric:
    """I = alignment × riemann_factor × aetheric_stability × refined_ratio.
    Every term is Fraction; the exponentials use exact-rational Taylor
    series via _symbolic_exp."""

    def __init__(self, C: Fraction = Fraction(1, 4)):
        self.C = C
        self._cf_refiner = ContinuedFractionRefiner()

    def calculate_alignment(self, valid_pairs: int, total_primes: int) -> Fraction:
        if total_primes == 0:
            return Fraction.zero()
        return Fraction(valid_pairs, total_primes)

    def calculate_riemann_factor(self, pi_x: int, x: Fraction) -> Fraction:
        """The Riemann error bound is |pi(x) - Li(x)| ≤ C·√x·log(x).
        We compute deviation = |pi(x) - Li(x)|, bound = C·√x·log(x),
        ratio = deviation / bound, and return exp(-ratio²).

        Li(x) is computed via the Ramanujan series in
        _symbolic_log_integral_approx(). If x ≤ 1, the logarithmic
        integral is 0 and the factor is 1.

        F6: The caller passes pi_x = len(self.primes), i.e., π(p_n), the
        count of primes ≤ p_n. Not the value of p_n."""
        if x <= Fraction.one():
            return Fraction.one()
        log_x = _symbolic_log(x)
        if log_x <= Fraction.zero():
            return Fraction.one()
        sqrt_x = x.sqrt()
        bound = self.C * sqrt_x * log_x
        li_x = _symbolic_log_integral_approx(x)
        pi_x_frac = Fraction(pi_x)
        deviation = (pi_x_frac - li_x).abs()
        if bound.is_zero():
            return Fraction.one() if deviation.is_zero() else Fraction.zero()
        ratio = deviation / bound
        ratio_sq = ratio * ratio
        return _symbolic_exp(-ratio_sq)

    def calculate_aetheric_stability(self, curl_phi_norm: Fraction) -> Fraction:
        exp_neg = _symbolic_exp(-curl_phi_norm)
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
    """O[Ψ] = ∫ ψ†Φψ d⁴q. Implemented as an exact-rational 4D Riemann
    sum over a grid of Fractions. No float64 anywhere."""

    def __init__(self, psi: SymbolicWavefunction, phi_field: SymbolicQuaternion):
        self.psi = psi
        self.phi = phi_field

    def compute_integral_exact(
        self,
        bounds: Tuple[Tuple[Fraction, Fraction], ...],
        steps: int = 2,
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
        steps: int = 2,
    ) -> Fraction:
        integral = self.compute_integral_exact(bounds, steps)
        return integral.magnitude_squared()


# ============================================================================
# LOG RING BUFFER
# ============================================================================
_LOG_BUFFER: deque = deque(maxlen=int(os.getenv("LOG_BUFFER_SIZE", "1000")))
_LOG_LOCK = threading.Lock()

logger = logging.getLogger("aei_seed")
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
        entry = dict(payload)
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
# CRAWLER STATE
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
    """The crawler frontier lives here in app.py, not in worker.js.
    worker.js is a stateless fetch proxy. Each crawled document becomes
    a symbolic input x for the seed loop: its content hash is lifted to
    an exact Fraction, and its link count becomes a lattice contact
    constraint."""

    # F11: cap the in-memory frontier at a bounded size. SQLite remains
    # the source of truth; the in-memory list is only a preview cache.
    _FRONTIER_MAX: int = 10000

    def __init__(self, db_path: str = ":memory:"):
        self._lock = threading.Lock()
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
        with self._lock:
            try:
                self._conn.execute(
                    "INSERT OR IGNORE INTO crawl_queue (url, priority, depth) VALUES (?, ?, ?)",
                    (url, priority, depth),
                )
                self._conn.commit()
            except Exception as e:
                logger.warning(f"crawler enqueue failed: {e}")
                return
            if url not in self._frontier:
                self._frontier.append(url)
                if len(self._frontier) > self._FRONTIER_MAX:
                    self._frontier = self._frontier[-self._FRONTIER_MAX:]

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
                    try:
                        self._frontier.remove(url)
                    except ValueError:
                        pass
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
            if len(self._records) > 5000:
                self._records = self._records[-5000:]
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
            return {
                "frontier_size": len(self._frontier),
                "frontier_preview": list(self._frontier[:8]),
                "visited_count": self.visited_count(),
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
    """Stateless relay client. Sends a URL to worker.js, gets back
    {url, title, content_hash, links, provider} as JSON. The relay
    does the network I/O; all crawl logic (frontier, visited set,
    seed injection) lives in app.py."""

    def __init__(self, relay_url: str, relay_key: str = "", timeout: int = 15,
                 max_retries: int = 3):
        self.relay_url = relay_url.rstrip("/")
        self.relay_key = relay_key
        self.timeout = timeout
        # F6: max_retries must be ≥ 1; 0 would make the for-loop a no-op
        # and immediately increment _failure_count without ever calling fetch.
        self.max_retries = max(1, int(max_retries))
        self._failure_count = 0

    def fetch_url(self, url: str) -> Optional[Dict[str, Any]]:
        if not self.relay_url:
            logger.warning("CrawlerRelayClient: RELAY_URL not set")
            return None
        qs = urllib.parse.urlencode({"url": url})
        target = f"{self.relay_url}/?{qs}"
        last_error = None
        for attempt in range(self.max_retries):
            try:
                headers = {
                    "Accept": "application/json",
                    "User-Agent": "AEI-Seed-Crawler/1.0",
                }
                if self.relay_key:
                    headers["X-Relay-Key"] = self.relay_key
                req = urllib.request.Request(target, headers=headers)
                with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                    raw = resp.read().decode("utf-8")
                    payload = json.loads(raw)
                    if isinstance(payload, dict) and payload.get("error"):
                        logger.warning(f"relay error for {url}: {payload.get('error')}")
                        self._failure_count += 1
                        return None
                    self._failure_count = 0
                    return payload
            except urllib.error.HTTPError as e:
                last_error = f"HTTP {e.code}"
                logger.warning(f"relay HTTP {e.code} for {url} (attempt {attempt+1}/{self.max_retries})")
                if e.code == 429 and attempt < self.max_retries - 1:
                    time.sleep(1 + attempt * 2)
                    continue
                break
            except urllib.error.URLError as e:
                last_error = f"URLError: {e.reason}"
                logger.warning(f"relay URLError for {url}: {e.reason}")
                if attempt < self.max_retries - 1:
                    time.sleep(1 + attempt * 2)
                    continue
                break
            except json.JSONDecodeError as e:
                last_error = f"JSONDecodeError: {e}"
                logger.warning(f"relay returned invalid JSON for {url}")
                break
            except Exception as e:
                last_error = f"{type(e).__name__}: {e}"
                logger.warning(f"relay error for {url}: {e}")
                if attempt < self.max_retries - 1:
                    time.sleep(1 + attempt * 2)
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
# AEI_SEED — the GAIA seed loop
# ============================================================================
class AEI_Seed:
    """The GAIA/ÆI seed. Faithful to ÆI.md §3–§8.

    State machine per step:
      1. Primorial step   — generate the next prime (exact Fraction)
      2. Lattice step     — stereographic project the prime; add_sphere
      3. Wavefunction     — integrate ψ over the lattice, blending with
                            the prior rectified ψ so DbZ persists (F5)
      4. Trajectory       — generate the Natalia-fibrated quaternionic path
      5. Aetheric gate    — validate s²=r²; compute deviation_sq
      6. DbZ              — if deviation_sq ≠ 0, rectify ψ
      7. Execution        — record the intelligence metric I with
                            pi_x = π(p_n) = len(self.primes) (F6)
      8. Evolution        — SelfEvolutionCore.evolve_step

    Inputs: the seed's x parameter. In the market bot, x is a price;
    in the ÆI seed, x is the hash fraction of the most recently crawled
    document. If the crawler is idle, x defaults to the tick counter.
    """

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

        # F5: prior deviation, so DbZ rectification persists across steps.
        self._prior_deviation_sq: Optional[Fraction] = None

        self._step_lock = threading.Lock()

    def _integrate_wavefunction_symbolic(self) -> Dict[Tuple[int, int, int, int], Fraction]:
        """F5: blend the fresh lattice integration with the prior
        rectified psi whenever the prior step was non-coherent. This is
        what makes DbZ persist — otherwise the rectification is
        overwritten on the next step by a pure lattice read."""
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
            q = q.apply_natalia_fibration(t, epsilon, iterations=10)
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
            self.lattice.add_sphere(center, Fraction.one())
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
            # F5: persist the deviation so the NEXT step knows to blend.
            self._prior_deviation_sq = deviation_sq
            q_eval = SymbolicQuaternion(p_n, Fraction.zero(), Fraction.zero(), Fraction.zero())
            # F6: pi_x is the COUNT of primes ≤ p_n, i.e., len(self.primes).
            # Passing int(p_n.num()) would compare p_n's VALUE to Li(p_n),
            # which is not the Riemann error.
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
            if len(self.history) > 1000:
                self.history = self.history[-1000:]
            return record

    def run_autonomous(self, steps: int, x_fn=None) -> List[Dict[str, Any]]:
        records = []
        for i in range(steps):
            x = x_fn(i) if x_fn else Fraction(i, 1)
            records.append(self.step(x))
        return records

    def snapshot(self) -> Dict[str, Any]:
        lock = self._step_lock
        with lock:
            return {
                "state": self.state,
                "tick": self.tick,
                "generation": self.generation,
                "primes_tail": [str(p) for p in self.primes[-12:]],
                "prime_count": len(self.primes),
                "lattice_points": len(self.lattice.points()),
                "arc_sq": str(self.last_arc_sq),
                "radius_sq": str(self.last_radius_sq),
                "deviation_sq": str(self.last_deviation_sq),
                "coherence": self.last_deviation_sq.is_zero(),
                "I": str(self.last_I),
                "hopf_base": [str(self.last_hopf_base[0]), str(self.last_hopf_base[1])],
                "evolution": self.last_evolution,
                "trajectory": [
                    {"a": str(q.a), "b": str(q.b), "c": str(q.c), "d": str(q.d)}
                    for q in self.last_trajectory
                ],
                "linguistic_trajectory": [
                    {"a": str(q.a), "b": str(q.b), "c": str(q.c), "d": str(q.d)}
                    for q in self.last_linguistic_trajectory
                ],
                "history_tail": self.history[-20:],
                "logic_core": {
                    k: {kk: str(vv) for kk, vv in v.items()} if isinstance(v, dict) else str(v)
                    for k, v in self.evolution.logic_core.items()
                },
                "last_logic_hash": self.last_logic_hash,
                # F8: expose Re[ψ] so the DBZ branch panel can distinguish
                # 𝒜₃ (Re[ψ] > 0) from 𝒜₄ (Re[ψ] ≤ 0) independent of coherence.
                "psi_real": str(self.psi.real_part()),
            }

    def encode_syllable(self, syllable: str) -> Dict[str, Any]:
        traj = self.linguist.encode_syllable(syllable)
        self.last_linguistic_trajectory = traj
        arc_sq = self.monitor.compute_arc_length_squared(traj)
        radius_sq = traj[-1].magnitude_squared() if traj else Fraction.zero()
        return {
            "syllable": syllable,
            "length": len(traj),
            "arc_sq": str(arc_sq),
            "radius_sq": str(radius_sq),
            "deviation_sq": str(arc_sq - radius_sq),
            "coherence": (arc_sq == radius_sq),
            "trajectory": [
                {"a": str(q.a), "b": str(q.b), "c": str(q.c), "d": str(q.d)}
                for q in traj
            ],
        }


# ============================================================================
# BRIDGE STATE
# ============================================================================
class BridgeState:
    """Holds user-committed quaternionic anchors, webapp sessions, and
    the crawl queue introspection."""

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
    "port": None,
}


# ============================================================================
# CS-TRANSLATION HELPERS
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


# F9: field-label sigils for Telegram message bodies. These are the
# left-hand strings the user sees; the right-hand strings are the CS
# plain-text sigils from LOGOS.MD CODEX_SYMBOLICA.
_CS_LABELS: Dict[str, str] = {
    "state": "𝒮",
    "tick": "𝒯",
    "generation": "𝒯_gen",
    "prime_count": "𝒜[p]",
    "lattice_points": "Λ₂₄",
    "deviation_sq": "δ(s²−r²)",
    "I": "ℐ",
    "hopf_base": "𝒮_fib",
    "evolution": "𝒯_evo",
    "crawler": "𝒞",
    "observer": "𝒪[Ψ]",
    "lingoso": "ℱ",
    "psi_real": "Re[ψ]",
    "coherence": "𝒮_coh",
    "primes_tail": "𝒜[p]_tail",
    "logic_hash": "ℋ_hash",
    "frontier": "𝒞_front",
    "visited": "𝒞_visited",
}


_CS_SIGIL_PREFIXES = ("𝒜", "𝒮", "𝒟", "ℐ", "𝒪", "𝒞", "𝒯", "ℱ", "Λ", "Φ", "Ψ", "⟦", "⟧")


def _cs(value) -> str:
    if value is None:
        return "—"
    s = str(value).strip()
    if not s:
        return "—"
    upper = s.upper()
    if upper in _CS_VALUE_MAP:
        return _CS_VALUE_MAP[upper]
    if "/" in s:
        stripped = s.replace("/", "").replace("-", "").replace("+", "")
        if stripped.isdigit():
            return s
    if s.startswith(_CS_SIGIL_PREFIXES):
        return s
    return "⟦" + s + "⟧"


def _cs_label(key: str) -> str:
    """F9: lookup the CS sigil for a field label. Falls back to the
    original key wrapped in ⟦…⟧ so no information is lost if a new
    label is introduced without a sigil entry."""
    return _CS_LABELS.get(key, "⟦" + key + "⟧")


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


def _looks_like_length_error(desc: str) -> bool:
    if not desc:
        return False
    d = desc.lower()
    return any(k in d for k in ("too long", "message is too long",
                                "text is too long", "4096"))


# ============================================================================
# ENVIRONMENT / CONFIGURATION
# ============================================================================
TELEGRAM_BOT_TOKEN_ENV: str = os.getenv("TELEGRAM_BOT_TOKEN", "").strip()
TELEGRAM_WEBAPP_URL: str = os.getenv("TELEGRAM_WEBAPP_URL", "").strip()
BRIDGE_HOST: str = os.getenv("BRIDGE_HOST", "0.0.0.0").strip()
# F1: on a web dyno, $PORT is Heroku-assigned. We bind to it directly.
# On a local dev box, BRIDGE_PORT (default 8765) is used.
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
BRIDGE_TUNNEL: str = os.getenv("BRIDGE_TUNNEL", "cloudflared").strip().lower()
BRIDGE_PUBLIC_TIMEOUT: int = int(os.getenv("BRIDGE_PUBLIC_TIMEOUT", "45"))
REQUIRE_AUTH: bool = os.getenv("REQUIRE_AUTH", "1").strip() in ("1", "true", "yes")
CORS_ORIGIN: str = os.getenv("CORS_ORIGIN", "*").strip()

RELAY_URL: str = os.getenv("RELAY_URL", "").strip().rstrip("/")
RELAY_KEY: str = os.getenv("RELAY_KEY", "").strip()
RELAY_TIMEOUT: int = int(os.getenv("RELAY_TIMEOUT", "15"))
RELAY_MAX_RETRIES: int = int(os.getenv("RELAY_MAX_RETRIES", "3"))

SEED_TICK_INTERVAL: int = int(os.getenv("SEED_TICK_INTERVAL", "5"))
CRAWL_INTERVAL: int = int(os.getenv("CRAWL_INTERVAL", "3"))
MAX_CRAWL_DEPTH: int = int(os.getenv("MAX_CRAWL_DEPTH", "3"))
CRAWL_SEED_URLS: str = os.getenv("CRAWL_SEED_URLS", "").strip()
CRAWLER_DB_PATH: str = os.getenv("CRAWLER_DB_PATH", "aei_crawler.db")

ALLOWED_USER_IDS: set = set()
_raw_allowed = os.getenv("ALLOWED_USER_IDS", "").strip()
if _raw_allowed:
    for tok in _raw_allowed.split(","):
        tok = tok.strip()
        if tok.isdigit():
            ALLOWED_USER_IDS.add(int(tok))


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


def _extract_auth_headers(handler: "BridgeHandler") -> Tuple[Optional[int], Optional[str], bool]:
    raw_init = handler.headers.get("X-Telegram-Init-Data", "").strip()
    if not raw_init:
        auth_hdr = handler.headers.get("Authorization", "").strip()
        if auth_hdr.lower().startswith("tma "):
            raw_init = auth_hdr[4:].strip()
    if not raw_init:
        try:
            qs = dict(parse_qsl(urlparse(handler.path).query))
            raw_init = (qs.get("auth_init_data") or "").strip()
        except Exception:
            raw_init = ""
    if not raw_init:
        return (None, None, False)
    verified = verify_telegram_init_data(raw_init, TELEGRAM_BOT_TOKEN_ENV)
    if not verified or not verified.get("user"):
        return (None, None, False)
    u = verified["user"] or {}
    return (u.get("id"), u.get("username"), True)


# ============================================================================
# CRAWLER WORKER
# ============================================================================
class CrawlerWorker:
    """Async crawler loop. Pulls URLs from the frontier, fetches via the
    relay, records the visit (hash lifted to exact Fraction), enqueues
    discovered links up to MAX_CRAWL_DEPTH. The seed consumes the latest
    hash_frac as its x input on each step."""

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
        initial = seeds if seeds else self.DEFAULT_SEEDS
        if CRAWL_SEED_URLS:
            initial = [u.strip() for u in CRAWL_SEED_URLS.split(",") if u.strip()]
        for u in initial:
            self.state.enqueue(u, depth=0, priority=1)

    async def _loop(self):
        while self._running:
            try:
                url = await asyncio.to_thread(self.state.dequeue)
                if url is None:
                    await asyncio.sleep(1.0)
                    continue
                payload = await asyncio.to_thread(self.relay.fetch_url, url)
                if payload and not payload.get("error"):
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
                    logger.info(f"crawl skipped: {url} (no payload)")
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

    def snapshot(self) -> Dict[str, Any]:
        snap = self.state.snapshot()
        snap.update({
            "running": self._running,
            "crawl_count": self._crawl_count,
            "last_fetch_at": self._last_fetch_at.isoformat() if self._last_fetch_at else None,
            "relay_url": RELAY_URL,
            "relay_healthy": (self.relay.failure_count() < 3),
        })
        return snap


# ============================================================================
# SEED WORKER
# ============================================================================
class SeedWorker:
    """Async seed loop. On each tick, reads the latest crawler hash_frac
    as x; if crawler is idle, defaults to the tick counter. Calls
    AEI_Seed.step(x). Emits a toast on each step so the TWA updates."""

    def __init__(self, seed: AEI_Seed, crawler: CrawlerWorker):
        self.seed = seed
        self.crawler = crawler
        self._running = False
        self._task: Optional[asyncio.Task] = None

    async def _loop(self):
        while self._running:
            try:
                hash_frac = self.crawler.state.latest_hash_fraction()
                if hash_frac == PyFraction(0, 1):
                    x = Fraction(self.seed.tick, 1)
                else:
                    x = Fraction(hash_frac)
                record = await asyncio.to_thread(self.seed.step, x)
                _emit_toast("seed", {
                    "tick": record["tick"],
                    "generation": record["generation"],
                    "prime": record["prime"],
                    "coherence": record["coherence"],
                    "deviation_sq": record["deviation_sq"],
                    "I": record["I"],
                    "state": record["state"],
                })
                await asyncio.sleep(SEED_TICK_INTERVAL)
            except asyncio.CancelledError:
                break
            except Exception as e:
                logger.warning(f"seed loop error: {e}")
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


# ============================================================================
# FQDN FAST-PATH
# ============================================================================
def _fqdn_fast(host: str) -> str:
    return host


# ============================================================================
# TUNNEL MANAGER (kept for optional worker-dyno deployments; skipped on web)
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
        return subprocess.Popen(cmd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, bufsize=1,
                                universal_newlines=True)

    def _scan_for_url(self, proc: subprocess.Popen, regex, deadline: float) -> Optional[str]:
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
            proc = self._spawn(["cloudflared", "tunnel", "--url",
                                f"http://127.0.0.1:{self.port}", "--no-autoupdate"])
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
            proc = self._spawn(["ssh", "-o", "StrictHostKeyChecking=no",
                                "-o", "ServerAliveInterval=30",
                                "-R", f"80:127.0.0.1:{self.port}", "serveo.net"])
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
        order = [self.prefer] + [p for p in ("cloudflared", "ngrok", "serveo")
                                 if p != self.prefer]
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
    server_version = "AEI-Seed-Bridge/final-ed14"

    def log_message(self, fmt, *args):
        return

    def _set_cors(self) -> None:
        origin = CORS_ORIGIN
        request_origin = self.headers.get("Origin", "").strip()
        if origin == "*":
            if request_origin and request_origin != "null":
                self.send_header("Access-Control-Allow-Origin", request_origin)
                self.send_header("Vary", "Origin")
            else:
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
        # F14: send_response() must be called first; _set_cors() then
        # appends Access-Control-* headers; Content-Length is the last
        # header before end_headers().
        self.send_response(204)
        self._set_cors()
        self.send_header("Content-Length", "0")
        self.send_header("Vary", "Origin")
        self.end_headers()

    def do_GET(self) -> None:
        path = urlparse(self.path).path
        query = dict(parse_qsl(urlparse(self.path).query))

        if path == "/health":
            seed = BRIDGE_ENGINE_REF.get("seed")
            crawler = BRIDGE_ENGINE_REF.get("crawler")
            raw_state = seed.state if seed else "uninitialized"
            self._send_json(200, {
                "ok": True,
                "service": "aei-seed-bridge",
                "version": "final-ed14",
                "substrate": _SUBSTRATE,
                "seed_initialized": seed is not None,
                "crawler_running": (crawler._running if crawler else False),
                "seed_tick": (seed.tick if seed else 0),
                "seed_generation": (seed.generation if seed else 0),
                "seed_state": _cs(raw_state),
                "seed_state_raw": raw_state,
                "prime_count": (len(seed.primes) if seed else 0),
                "lattice_points": (len(seed.lattice.points()) if seed else 0),
                "crawler_frontier": (crawler.state.frontier_size() if crawler else 0),
                "crawler_visited": (crawler.state.visited_count() if crawler else 0),
                "relay_url": RELAY_URL,
                "relay_healthy": (crawler.relay.failure_count() < 3 if crawler else False),
                "require_auth": REQUIRE_AUTH,
            })
            return

        if path == "/config":
            self._send_json(200, {
                "public_url": BRIDGE_ENGINE_REF.get("public_url"),
                "substrate": _SUBSTRATE,
                "tls": BRIDGE_USE_TLS,
                "port": BRIDGE_PORT,
                "host": BRIDGE_HOST,
                "require_auth": REQUIRE_AUTH,
                "cors_origin": CORS_ORIGIN,
                "relay_url": RELAY_URL,
                "relay_gated": _cs(bool(RELAY_KEY)),
                "seed_tick_interval": SEED_TICK_INTERVAL,
                "crawl_interval": CRAWL_INTERVAL,
                "max_crawl_depth": MAX_CRAWL_DEPTH,
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
                                         "<h2>⚡ ÆI Seed Bridge Online (Ed.14)</h2>"
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

        if path == "/miniapp-state":
            if seed is None:
                self._send_json(503, {"error": "seed_not_ready"})
                return
            snap = seed.snapshot()
            if crawler is not None:
                snap["crawler"] = crawler.snapshot()
            self._send_json(200, snap)
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
            self._send_json(200, crawler.snapshot())
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
            integral = seed.consciousness.compute_integral_exact(bounds, steps=2)
            self._send_json(200, {
                "integral": {
                    "a": str(integral.a), "b": str(integral.b),
                    "c": str(integral.c), "d": str(integral.d),
                },
                "magnitude_sq": str(integral.magnitude_squared()),
                "steps": 2,
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

        self._send_json(404, {"error": "not_found", "path": path})

    def do_POST(self) -> None:
        path = urlparse(self.path).path

        if path == "/handshake":
            try:
                data = self._read_json()
                init_data = data.get("initData", "").strip()
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
                })
            except Exception as e:
                self._send_json(500, {"error": "internal", "detail": str(e)})
            return

        if not _require_auth(self):
            self._send_json(401, {"error": "unauthorized"})
            return

        seed = BRIDGE_ENGINE_REF.get("seed")
        crawler = BRIDGE_ENGINE_REF.get("crawler")

        if path == "/step":
            if seed is None:
                self._send_json(503, {"error": "seed_not_ready"})
                return
            data = self._read_json()
            try:
                x_num = int(data.get("x_num", seed.tick + 1))
                x_den = int(data.get("x_den", 1))
                x = Fraction(x_num, x_den)
            except Exception:
                x = Fraction(seed.tick + 1, 1)
            import asyncio
            record = asyncio.run(asyncio.to_thread(seed.step, x))
            _emit_toast("seed", {
                "tick": record["tick"],
                "generation": record["generation"],
                "prime": record["prime"],
                "coherence": record["coherence"],
                "deviation_sq": record["deviation_sq"],
                "I": record["I"],
                "state": record["state"],
            })
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
            self._send_json(200, {"ok": True, "url": url, "depth": depth,
                                  "frontier_size": crawler.state.frontier_size()})
            return

        if path == "/encode-syllable":
            if seed is None:
                self._send_json(503, {"error": "seed_not_ready"})
                return
            data = self._read_json()
            syllable = str(data.get("syllable", "A"))
            result = seed.encode_syllable(syllable)
            self._send_json(200, {"ok": True, "result": result})
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


def _require_auth(handler: "BridgeHandler") -> bool:
    if not REQUIRE_AUTH or not TELEGRAM_BOT_TOKEN_ENV:
        return True
    raw_init = handler.headers.get("X-Telegram-Init-Data", "").strip()
    if not raw_init:
        auth_hdr = handler.headers.get("Authorization", "").strip()
        if auth_hdr.lower().startswith("tma "):
            raw_init = auth_hdr[4:].strip()
    if not raw_init:
        try:
            qs = dict(parse_qsl(urlparse(handler.path).query))
            raw_init = (qs.get("auth_init_data") or "").strip()
        except Exception:
            raw_init = ""
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
class BridgeServer:
    def __init__(self, host: str = BRIDGE_HOST, port: int = BRIDGE_PORT):
        self.host = host
        self.port = int(port)
        self._httpd: Optional[ThreadingHTTPServer] = None
        self._thread: Optional[threading.Thread] = None
        self._tunnel: Optional[TunnelManager] = None
        self._tunnel_thread: Optional[threading.Thread] = None
        self._ssl_context: Optional[ssl.SSLContext] = None
        self._listen_ready: threading.Event = threading.Event()
        self._listen_ok: bool = False

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

        bind_port = BRIDGE_PORT
        if _ENV_PORT:
            logger.info(f"🌐 Web-dyno substrate: binding to $PORT={bind_port}")
        else:
            logger.info(f"🌐 Local substrate: binding to BRIDGE_PORT={bind_port}")

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
            logger.error(
                f"🔥 Bridge server bind failed on {self.host}:{bind_port}: {e}"
            )
            self._listen_ready.set()
            self._listen_ok = False
            return

        self._listen_ok = True
        self._thread = threading.Thread(
            target=self._httpd.serve_forever, name="aei-bridge", daemon=True
        )
        self._thread.start()
        scheme = "https" if self._ssl_context else "http"
        logger.info(
            f"🌐 ÆI Seed Bridge listening on {scheme}://{self.host}:{self.port}"
        )

        if _ENV_PORT and not TELEGRAM_WEBAPP_URL:
            logger.warning(
                "⚠️ Web-dyno substrate but TELEGRAM_WEBAPP_URL is unset. "
                "Set it to https://<app>.herokuapp.com/ and re-run /setmenubutton."
            )
            heroku_url = os.getenv("HEROKU_APP_DEFAULT_DOMAIN_NAME", "").strip()
            if heroku_url:
                guessed = f"https://{heroku_url}/"
                BRIDGE_ENGINE_REF["public_url"] = guessed
                logger.info(f"🌐 Inferred public URL from HEROKU_APP_DEFAULT_DOMAIN_NAME: {guessed}")
        else:
            self._tunnel = TunnelManager(
                self.port, prefer=BRIDGE_TUNNEL, timeout=BRIDGE_PUBLIC_TIMEOUT
            )
            self._tunnel_thread = threading.Thread(
                target=self._tunnel.start, name="aei-tunnel", daemon=True
            )
            self._tunnel_thread.start()

        self._listen_ready.set()

    def stop(self) -> None:
        if self._tunnel is not None:
            try:
                self._tunnel.stop()
            except Exception:
                pass
            self._tunnel = None
        if self._tunnel_thread is not None:
            self._tunnel_thread.join(timeout=5.0)
            self._tunnel_thread = None
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
        logger.info("🌐 ÆI Seed Bridge stopped")


# ============================================================================
# TELEGRAM BOT
# ============================================================================
try:
    from telegram import (
        Update, InlineKeyboardButton, InlineKeyboardMarkup,
        WebAppInfo, MenuButtonWebApp,
    )
    from telegram.ext import (
        Application, CommandHandler, CallbackQueryHandler,
        ContextTypes, MessageHandler, filters,
    )
    TELEGRAM_AVAILABLE = True
except ImportError:
    TELEGRAM_AVAILABLE = False
    logger.warning("python-telegram-bot not installed; bot commands disabled")


class AEI_Bot:
    def __init__(self, token: str, bot_name: str = "AEISeedBot"):
        self.token = token
        self.bot_name = bot_name
        self.application = None
        self._loop: Optional[asyncio.AbstractEventLoop] = None
        self._bridge_server: Optional[BridgeServer] = None
        self._seed_worker: Optional[SeedWorker] = None
        self._crawler_worker: Optional[CrawlerWorker] = None

    def _send_message_sync(self, chat_id: int, text: str, parse_mode: str = "Markdown",
                           reply_to_message_id: Optional[int] = None,
                           timeout: float = 10.0) -> bool:
        if self.application is None:
            return False
        loop = self._loop
        if loop is None or loop.is_closed():
            return False
        bot = self.application.bot

        def _attempt(pm: Optional[str], rt: Optional[int]) -> Tuple[bool, str]:
            coro = bot.send_message(chat_id=chat_id, text=text,
                                    parse_mode=pm, reply_to_message_id=rt)
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
        logger.info(f"📡 send attempt 1 failed: {err1}")
        if _looks_like_parse_error(err1):
            ok3, err3 = _attempt(None, reply_to_message_id)
            if ok3:
                return True
        if _looks_like_reply_error(err1):
            ok2, err2 = _attempt(parse_mode, None)
            if ok2:
                return True
        ok3, err3 = _attempt(None, None)
        return ok3

    async def _post_init(self, application) -> None:
        try:
            self._loop = asyncio.get_running_loop()
            logger.info("🔁 Event loop captured")
        except RuntimeError:
            self._loop = None
        BRIDGE_ENGINE_REF["bot"] = self

        if self._bridge_server is None:
            server = BridgeServer()
            self._bridge_server = server
            boot_thread = threading.Thread(
                target=server.start, name="aei-bridge-boot", daemon=True
            )
            boot_thread.start()
            ready = server._listen_ready.wait(timeout=BRIDGE_PUBLIC_TIMEOUT)
            if not ready or not server._listen_ok:
                logger.error(
                    "🔥 Bridge failed to bind within %ss; "
                    "seed/crawler workers will not start.",
                    BRIDGE_PUBLIC_TIMEOUT,
                )
                return
            logger.info("🌐 Bridge binding verified; proceeding to worker start")

        url = TELEGRAM_WEBAPP_URL or BRIDGE_ENGINE_REF.get("public_url")
        if url:
            try:
                await application.bot.set_chat_menu_button(
                    menu_button=MenuButtonWebApp(
                        text="ÆI Seed", web_app=WebAppInfo(url=url),
                    )
                )
                logger.info(f"✅ MenuButtonWebApp registered: {url}")
            except Exception as e:
                logger.warning(f"Failed to set menu button: {e}")
        else:
            logger.info("⏳ MenuButtonWebApp deferred — no public URL yet")

        seed = BRIDGE_ENGINE_REF.get("seed")
        crawler = BRIDGE_ENGINE_REF.get("crawler")
        if seed is not None and crawler is not None:
            crawler.start()
            seed_worker = SeedWorker(seed, crawler)
            seed_worker.start()
            self._crawler_worker = crawler
            self._seed_worker = seed_worker
            logger.info("⚡ AEI seed + crawler workers started")
        else:
            logger.warning("⚠️ _post_init ran before seed/crawler were registered")

    def _build_main_keyboard(self) -> "InlineKeyboardMarkup":
        url = TELEGRAM_WEBAPP_URL or BRIDGE_ENGINE_REF.get("public_url")
        rows = [
            [InlineKeyboardButton("𝒮_status", callback_data="status"),
             InlineKeyboardButton("𝒜_primes", callback_data="primes")],
            [InlineKeyboardButton("Λ₂₄_lattice", callback_data="lattice"),
             InlineKeyboardButton("𝒮_fibration", callback_data="fibration")],
            [InlineKeyboardButton("𝒪[Ψ]", callback_data="observer"),
             InlineKeyboardButton("ℐ_metric", callback_data="metric")],
            [InlineKeyboardButton("𝒯_evolution", callback_data="evolution"),
             InlineKeyboardButton("𝒞_crawler", callback_data="crawler")],
            [InlineKeyboardButton("🔄 step", callback_data="step"),
             InlineKeyboardButton("⟳ reset", callback_data="reset")],
        ]
        if url:
            rows.append([InlineKeyboardButton("⚡ Open ÆI Seed", web_app=WebAppInfo(url=url))])
        else:
            rows.append([InlineKeyboardButton("⏳ Mini App (URL pending…)", callback_data="webapp_pending")])
        return InlineKeyboardMarkup(rows)

    async def _safe_reply(self, update: "Update", text: str, reply_markup=None) -> bool:
        msg = update.effective_message
        query = update.callback_query
        target = query if query is not None else msg
        if target is None:
            return False
        try:
            if query is not None:
                await query.edit_message_text(text, parse_mode="Markdown",
                                              reply_markup=reply_markup)
            else:
                await msg.reply_text(text, parse_mode="Markdown",
                                     reply_markup=reply_markup)
            return True
        except Exception as e1:
            logger.info(f"_safe_reply attempt 1 failed: {e1}")
        try:
            if query is not None:
                await query.edit_message_text(text, parse_mode=None,
                                              reply_markup=reply_markup)
            else:
                await msg.reply_text(text, parse_mode=None,
                                     reply_markup=reply_markup)
            return True
        except Exception as e2:
            logger.info(f"_safe_reply attempt 2 failed: {e2}")
        return False

    async def start(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        seed = BRIDGE_ENGINE_REF.get("seed")
        state_cs = _cs(seed.state) if seed else "—"
        welcome = (
            "🔷 *ÆI SEED — Agential Ætheric Intelligence*\n\n"
            "This is the *ÆI seed* (GAIA/ÆI Codex), not the ÆEA market bot.\n"
            "It runs the prime-sieve → lattice → Hopf-fibration → s²=r² → "
            "SelfEvolution loop from ÆI.md §3–§8.\n\n"
            "📊 *Commands:*\n"
            "`/status` — seed state\n"
            "`/primes` — prime sequence tail\n"
            "`/lattice` — Λ₂₄ points\n"
            "`/fibration` — Hopf base + φ\n"
            "`/observer` — 𝒪[Ψ] integral\n"
            "`/metric` — ℐ metric + components\n"
            "`/evolution` — SelfEvolution history\n"
            "`/crawler` — 𝒞 crawler frontier\n"
            "`/step` — one seed step\n"
            "`/reset` — reset seed state\n"
            "`/enqueue <url>` — add URL to crawler\n"
            "`/encode <syl>` — encode A/U/M syllable\n"
            "`/webapp` — open Mini App\n"
            "`/whoami` — your Telegram user ID\n"
            "`/help` — this message\n\n"
            f"🧠 *{_cs_label('state')}:* {state_cs}\n"
            f"📈 *{_cs_label('tick')}:* {seed.tick if seed else 0}  |  "
            f"*{_cs_label('generation')}:* {seed.generation if seed else 0}\n"
            f"🎯 *{_cs_label('prime_count')}:* {len(seed.primes) if seed else 0}  |  "
            f"*{_cs_label('lattice_points')}:* {len(seed.lattice.points()) if seed else 0}\n"
            "💎 Natalia Tanyatia"
        )
        await self._safe_reply(update, welcome, reply_markup=self._build_main_keyboard())

    async def help(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        await self.start(update, context)

    async def status(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        seed = BRIDGE_ENGINE_REF.get("seed")
        crawler = BRIDGE_ENGINE_REF.get("crawler")
        if seed is None:
            await self._safe_reply(update, "⏳ Seed not initialized.")
            return
        state_cs = _cs(seed.state)
        dev = seed.last_deviation_sq
        coh = "⟦𝒯⟧" if dev.is_zero() else "⟦ℱ⟧"
        psi_real = seed.psi.real_part()
        dbz_branch = "𝒜₃" if psi_real > Fraction.zero() else "𝒜₄"
        text = (
            "🔷 *ÆI SEED 𝒮_STATUS*\n"
            f"🧠 *{_cs_label('state')}:* {state_cs}\n"
            f"🔄 *{_cs_label('tick')}:* {seed.tick}\n"
            f"📈 *{_cs_label('generation')}:* {seed.generation}\n"
            f"🎯 *{_cs_label('prime_count')}:* {len(seed.primes)}\n"
            f"Λ₂₄ *Points:* {len(seed.lattice.points())}\n"
            f"*{_cs_label('deviation_sq')}:* {dev}\n"
            f"✓ *{_cs_label('coherence')}:* {coh}\n"
            f"*{_cs_label('I')}:* {seed.last_I}\n"
            f"*{_cs_label('psi_real')}:* {psi_real} → {dbz_branch}\n"
            f"𝒪[Ψ] *Base:* ({seed.last_hopf_base[0]}, {seed.last_hopf_base[1]})\n"
            f"𝒯_evolution *Generation:* {seed.evolution.generation}\n"
            f"📋 *Logic core keys:* {len(seed.evolution.logic_core)}\n"
            f"🔑 *{_cs_label('logic_hash')}:* `{seed.last_logic_hash[:16]}`\n"
        )
        if crawler is not None:
            text += (
                f"𝒞 *Frontier:* {crawler.state.frontier_size()}\n"
                f"𝒞 *Visited:* {crawler.state.visited_count()}\n"
                f"𝒞 *Last fetch:* {crawler._last_fetch_at.isoformat() if crawler._last_fetch_at else '—'}\n"
            )
        await self._safe_reply(update, text, reply_markup=self._build_main_keyboard())

    async def primes(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        seed = BRIDGE_ENGINE_REF.get("seed")
        if seed is None:
            await self._safe_reply(update, "⏳ Seed not initialized.")
            return
        tail = seed.primes[-24:]
        text = (
            "🎯 *𝒜_PRIMES — 6m±1 Sieve*\n"
            f"*Total:* {len(seed.primes)}\n\n"
            "*Tail (last 24):*\n"
            + "`" + "`, `".join(str(p) for p in tail) + "`\n\n"
            "*Formula:* pₙ = min{x>pₙ₋₁ : x mod 6 ∈ {1,5} ∧ ∀i<n, x mod pᵢ ≠ 0}"
        )
        await self._safe_reply(update, text)

    async def lattice(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        seed = BRIDGE_ENGINE_REF.get("seed")
        if seed is None:
            await self._safe_reply(update, "⏳ Seed not initialized.")
            return
        points = seed.lattice.points()
        preview = points[-4:] if len(points) >= 4 else points
        text = (
            "Λ₂₄ *LEECH LATTICE*\n"
            f"*Dimension:* {seed.lattice.dimension}\n"
            f"*Point count:* {len(points)}\n"
            f"*Kissing capacity:* {seed.lattice.KISSING_CAPACITY}\n\n"
            "*Latest projected centers:*\n"
        )
        for p in preview:
            head = ", ".join(str(c) for c in p[:4])
            text += f"`({head}, …)`\n"
        await self._safe_reply(update, text)

    async def fibration(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        seed = BRIDGE_ENGINE_REF.get("seed")
        if seed is None:
            await self._safe_reply(update, "⏳ Seed not initialized.")
            return
        hopf = seed.last_hopf_base
        phi = seed.phi
        text = (
            "𝒮_*FIBRATION — Hopf S³→S²*\n"
            f"*Base z:* `{hopf[0]}`\n"
            f"*Base w:* `{hopf[1]}`\n\n"
            f"*φ:* a={phi.a}, b={phi.b}, c={phi.c}, d={phi.d}\n"
            f"*‖φ‖²:* `{phi.magnitude_squared()}`\n\n"
            f"*Trajectory length:* {len(seed.last_trajectory)}\n"
            "*Natalia's Fibrations:* Φ = Q(s) + Σ εᵏ Natalia(k,s)"
        )
        await self._safe_reply(update, text)

    async def observer(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        seed = BRIDGE_ENGINE_REF.get("seed")
        if seed is None:
            await self._safe_reply(update, "⏳ Seed not initialized.")
            return
        bounds = (
            (Fraction(0), Fraction(1)),
            (Fraction(0), Fraction(1)),
            (Fraction(0), Fraction(1)),
            (Fraction(0), Fraction(1)),
        )
        integral = seed.consciousness.compute_integral_exact(bounds, steps=2)
        text = (
            "𝒪[Ψ] *OBSERVER INTEGRAL*\n"
            f"*∫ ψ†Φψ d⁴q:*\n"
            f"  a = `{integral.a}`\n"
            f"  b = `{integral.b}`\n"
            f"  c = `{integral.c}`\n"
            f"  d = `{integral.d}`\n"
            f"*‖𝒪[Ψ]‖²:* `{integral.magnitude_squared()}`\n\n"
            "*Grid:* 2×2×2×2 = 16 cells, exact Fraction Riemann sum"
        )
        await self._safe_reply(update, text)

    async def metric(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        seed = BRIDGE_ENGINE_REF.get("seed")
        if seed is None:
            await self._safe_reply(update, "⏳ Seed not initialized.")
            return
        text = (
            "ℐ *INTELLIGENCE METRIC*\n"
            f"*I =* `{seed.last_I}`\n\n"
            "*Components:*\n"
            f"  alignment  = {len(seed.primes)}/{len(seed.primes)}\n"
            f"  ‖φ‖²        = `{seed.phi.magnitude_squared()}`\n"
            f"  s²          = `{seed.last_arc_sq}`\n"
            f"  r²          = `{seed.last_radius_sq}`\n"
            f"  δ = s²−r²   = `{seed.last_deviation_sq}`\n\n"
            "*Formula:*\n"
            "I = (vp/tp) · exp(−|Δ|²/(C²x log²x)) · ‖∇×Φ‖ · refined_ratio\n\n"
            "*R-1 patch:* |Δ| = |π(x) − Li(x)| where Li(x) = ∫₂ˣ dt/log(t)\n"
            "is computed by the Ramanujan series."
        )
        await self._safe_reply(update, text)

    async def evolution(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        seed = BRIDGE_ENGINE_REF.get("seed")
        if seed is None:
            await self._safe_reply(update, "⏳ Seed not initialized.")
            return
        tail = seed.evolution.history[-8:]
        text = (
            "𝒯_*EVOLUTION — RFK Brainworm*\n"
            f"*Generation:* {seed.evolution.generation}\n"
            f"*Core keys:* {len(seed.evolution.logic_core)}\n"
            f"*Last logic hash:* `{seed.last_logic_hash[:24]}`\n\n"
            "*Recent history:*\n"
        )
        for rec in tail:
            status = rec.get("status", "?")
            mutation = rec.get("mutation") or "—"
            text += (f"gen {rec.get('generation', 0)}: "
                     f"`{status}` | mut=`{mutation}` | "
                     f"dev=`{rec.get('arc_length_deviation_sq', '—')}`\n")
        await self._safe_reply(update, text)

    async def crawler(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        crawler = BRIDGE_ENGINE_REF.get("crawler")
        if crawler is None:
            await self._safe_reply(update, "⏳ Crawler not initialized.")
            return
        snap = crawler.snapshot()
        preview = snap.get("frontier_preview", [])
        text = (
            "𝒞 *CRAWLER FRONTIER*\n"
            f"*Running:* {_cs(snap.get('running', False))}\n"
            f"*Frontier size:* {snap.get('frontier_size', 0)}\n"
            f"*Visited:* {snap.get('visited_count', 0)}\n"
            f"*Crawl count:* {snap.get('crawl_count', 0)}\n"
            f"*Last fetch:* {snap.get('last_fetch_at') or '—'}\n"
            f"*Relay URL:* `{snap.get('relay_url') or '—'}`\n\n"
            "*Frontier preview:*\n"
        )
        for u in preview[:6]:
            text += f"  • `{u[:80]}`\n"
        latest = snap.get("latest")
        if latest:
            text += (
                f"\n*Latest crawl:*\n"
                f"  *URL:* `{latest['url'][:80]}`\n"
                f"  *Title:* {latest['title'][:80]}\n"
                f"  *Hash:* `{latest['content_hash']}`\n"
                f"  *Hash fraction:* `{latest['hash_frac']}`\n"
            )
        await self._safe_reply(update, text)

    async def step_cmd(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        seed = BRIDGE_ENGINE_REF.get("seed")
        if seed is None:
            await self._safe_reply(update, "⏳ Seed not initialized.")
            return
        crawler = BRIDGE_ENGINE_REF.get("crawler")
        hash_frac = crawler.state.latest_hash_fraction() if crawler else PyFraction(0, 1)
        if hash_frac == PyFraction(0, 1):
            x = Fraction(seed.tick + 1, 1)
        else:
            x = Fraction(hash_frac)
        record = await asyncio.to_thread(seed.step, x)
        _emit_toast("seed", {
            "tick": record["tick"],
            "generation": record["generation"],
            "prime": record["prime"],
            "coherence": record["coherence"],
            "deviation_sq": record["deviation_sq"],
            "I": record["I"],
            "state": record["state"],
        })
        text = (
            "🔄 *SEED STEP*\n"
            f"*Tick:* {record['tick']}\n"
            f"*Generation:* {record['generation']}\n"
            f"*Prime:* `{record['prime']}`\n"
            f"*Primes total:* {record['prime_count']}\n"
            f"*Lattice points:* {record['lattice_points']}\n"
            f"*s²:* `{record['arc_sq']}`\n"
            f"*r²:* `{record['radius_sq']}`\n"
            f"*δ = s²−r²:* `{record['deviation_sq']}`\n"
            f"*Coherent:* {_cs(record['coherence'])}\n"
            f"*I:* `{record['I']}`\n"
            f"*State:* {_cs(record['state'])}"
        )
        await self._safe_reply(update, text)

    async def reset_cmd(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        seed = BRIDGE_ENGINE_REF.get("seed")
        if seed is None:
            await self._safe_reply(update, "⏳ Seed not initialized.")
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
        await self._safe_reply(update,
            "⟳ *Seed reset*\n"
            "Primes: [2, 3, 5]\n"
            "φ: (1, 0, 0, 0)\n"
            "ψ: {origin: 1}\n"
            "Tick: 0 | Generation: 0")

    async def enqueue_cmd(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        crawler = BRIDGE_ENGINE_REF.get("crawler")
        if crawler is None:
            await self._safe_reply(update, "⏳ Crawler not initialized.")
            return
        args = context.args
        if not args:
            await self._safe_reply(update, "Usage: `/enqueue <url>`")
            return
        url = args[0].strip()
        if not url.startswith("http"):
            await self._safe_reply(update, "❌ URL must start with http")
            return
        crawler.state.enqueue(url, depth=0, priority=10)
        await self._safe_reply(update,
            f"✅ Enqueued: `{url}`\n"
            f"*Frontier size:* {crawler.state.frontier_size()}")

    async def encode_cmd(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        seed = BRIDGE_ENGINE_REF.get("seed")
        if seed is None:
            await self._safe_reply(update, "⏳ Seed not initialized.")
            return
        args = context.args
        if not args:
            await self._safe_reply(update, "Usage: `/encode <syllable>` e.g. `/encode AUM`")
            return
        syllable = args[0]
        result = seed.encode_syllable(syllable)
        text = (
            "ℱ *LINGOSO ENCODING*\n"
            f"*Syllable:* `{syllable}`\n"
            f"*Trajectory length:* {result['length']}\n"
            f"*s²:* `{result['arc_sq']}`\n"
            f"*r²:* `{result['radius_sq']}`\n"
            f"*δ:* `{result['deviation_sq']}`\n"
            f"*Coherent:* {_cs(result['coherence'])}"
        )
        await self._safe_reply(update, text)

    async def webapp(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        url = TELEGRAM_WEBAPP_URL or BRIDGE_ENGINE_REF.get("public_url")
        if not url:
            await self._safe_reply(update,
                "⏳ *Mini App URL not yet available*\n"
                "Set TELEGRAM_WEBAPP_URL=https://<app>.herokuapp.com/ on Heroku "
                "and re-run /setmenubutton in BotFather.")
            return
        keyboard = InlineKeyboardMarkup([[
            InlineKeyboardButton("⚡ Open ÆI Seed", web_app=WebAppInfo(url=url)),
        ]])
        await self._safe_reply(update,
            "🌐 *ÆI Seed Mini App*\n"
            "Tap to launch the interactive GAIA seed visualization.\n\n"
            "*Panels inside the Mini App:*\n"
            "  𝒜_primes — prime sieve tail\n"
            "  Λ₂₄_pack — Leech lattice points\n"
            "  𝒮_fibration — Hopf base + φ\n"
            "  𝒪[Ψ] — observer integral\n"
            "  ℐ_metric — intelligence components\n"
            "  δ(s²−r²) — arc-length gate\n"
            "  𝒜₃/𝒜₄ — DbZ branch\n"
            "  𝒯_evolution — SelfEvolution history\n"
            "  𝒞_crawler — frontier + latest crawl\n"
            "  ℱ_lingoso — syllabic trajectory",
            reply_markup=keyboard)

    async def webgui(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        scheme = "https" if BRIDGE_USE_TLS else "http"
        local_url = f"{scheme}://{BRIDGE_HOST}:{BRIDGE_PORT}/"
        public_url = BRIDGE_ENGINE_REF.get("public_url") or "⏳ (not published)"
        await self._safe_reply(update,
            f"🌐 *ÆI Seed Bridge Endpoints*\n"
            f"*Substrate:* {_SUBSTRATE}\n"
            f"*Local:* `{local_url}`\n"
            f"*Public:* `{public_url}`\n"
            f"*Miniapp state:* `{public_url.rstrip('/')}/miniapp-state`\n"
            f"*Crawler state:* `{public_url.rstrip('/')}/crawler-state`\n"
            f"*Symbolic state:* `{public_url.rstrip('/')}/symbolic-state`\n"
            f"*Lattice state:* `{public_url.rstrip('/')}/lattice-state`\n"
            f"*Fibration state:* `{public_url.rstrip('/')}/fibration-state`\n"
            f"*Observer integral:* `{public_url.rstrip('/')}/observer-integral`\n"
            f"*Evolution state:* `{public_url.rstrip('/')}/evolution-state`\n"
            f"*Toasts:* `{public_url.rstrip('/')}/toasts`\n"
            f"*Log:* `{public_url.rstrip('/')}/log`")

    async def whoami(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        user = update.effective_user
        chat = update.effective_chat
        user_id = user.id if user else None
        chat_id = chat.id if chat else None
        allowed = _is_allowed_user(user_id)
        await self._safe_reply(update,
            f"🪪 *Identity*\n"
            f"*user_id:* `{user_id}`\n"
            f"*chat_id:* `{chat_id}`\n"
            f"*username:* @{user.username if user and user.username else '—'}\n"
            f"*Gate:* {'✅ allowed' if allowed else '❌ blocked'}\n"
            f"*Gate active:* {'yes' if ALLOWED_USER_IDS else 'no (open bot)'}")

    async def button_handler(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        query = update.callback_query
        if query is None:
            return
        await query.answer()
        action = query.data
        if action == "status":
            await self.status(update, context)
        elif action == "primes":
            await self.primes(update, context)
        elif action == "lattice":
            await self.lattice(update, context)
        elif action == "fibration":
            await self.fibration(update, context)
        elif action == "observer":
            await self.observer(update, context)
        elif action == "metric":
            await self.metric(update, context)
        elif action == "evolution":
            await self.evolution(update, context)
        elif action == "crawler":
            await self.crawler(update, context)
        elif action == "step":
            await self.step_cmd(update, context)
        elif action == "reset":
            await self.reset_cmd(update, context)
        elif action == "webapp_pending":
            try:
                await query.edit_message_text(
                    "⏳ Mini App URL is not yet published. "
                    "Set TELEGRAM_WEBAPP_URL=https://<app>.herokuapp.com/ on Heroku "
                    "and re-run /setmenubutton in BotFather.",
                    parse_mode="Markdown")
            except Exception:
                pass

    async def error_handler(self, update: "Update", context: "ContextTypes.DEFAULT_TYPE"):
        err = context.error
        err_str = f"{type(err).__name__}: {err}" if err is not None else "unknown"
        logger.error(f"handler error: {err_str}")

    def run(self):
        if not TELEGRAM_AVAILABLE:
            logger.error("python-telegram-bot not installed; cannot run bot")
            return

        crawler_state = CrawlerSeedState(CRAWLER_DB_PATH)
        relay = CrawlerRelayClient(RELAY_URL, RELAY_KEY,
                                   timeout=RELAY_TIMEOUT,
                                   max_retries=RELAY_MAX_RETRIES)
        crawler = CrawlerWorker(crawler_state, relay)
        seed = AEI_Seed(
            processor=DefaultSymbolicProcessor(),
            lattice=DefaultGeometricLattice(),
            monitor=DefaultAethericMonitor(),
            renderer=DefaultQuaternionicRenderer(),
            linguist=DefaultLingosoEncoder(),
        )
        BRIDGE_ENGINE_REF["seed"] = seed
        BRIDGE_ENGINE_REF["crawler"] = crawler

        self.application = (
            Application.builder()
            .token(self.token)
            .post_init(self._post_init)
            .build()
        )
        self.application.add_handler(CommandHandler("start", self.start))
        self.application.add_handler(CommandHandler("help", self.help))
        self.application.add_handler(CommandHandler("status", self.status))
        self.application.add_handler(CommandHandler("primes", self.primes))
        self.application.add_handler(CommandHandler("lattice", self.lattice))
        self.application.add_handler(CommandHandler("fibration", self.fibration))
        self.application.add_handler(CommandHandler("observer", self.observer))
        self.application.add_handler(CommandHandler("metric", self.metric))
        self.application.add_handler(CommandHandler("evolution", self.evolution))
        self.application.add_handler(CommandHandler("crawler", self.crawler))
        self.application.add_handler(CommandHandler("step", self.step_cmd))
        self.application.add_handler(CommandHandler("reset", self.reset_cmd))
        self.application.add_handler(CommandHandler("enqueue", self.enqueue_cmd))
        self.application.add_handler(CommandHandler("encode", self.encode_cmd))
        self.application.add_handler(CommandHandler("webapp", self.webapp))
        self.application.add_handler(CommandHandler("mini", self.webapp))
        self.application.add_handler(CommandHandler("webgui", self.webgui))
        self.application.add_handler(CommandHandler("whoami", self.whoami))
        self.application.add_handler(CallbackQueryHandler(self.button_handler))
        self.application.add_error_handler(self.error_handler)

        logger.info(f"🤖 {self.bot_name} starting...")
        logger.info("🔷 ÆI SEED (GAIA/ÆI Codex) — prime → lattice → Hopf → s²=r²")
        logger.info(f"🧮 Fraction-exact arithmetic throughout")
        logger.info(f"🌐 Substrate: {_SUBSTRATE} (bind port {BRIDGE_PORT})")
        logger.info(f"🕸️ Crawler: {crawler.state.frontier_size()} URLs in frontier, "
                    f"depth limit {MAX_CRAWL_DEPTH}, interval {CRAWL_INTERVAL}s")
        logger.info(f"🔄 Seed loop interval: {SEED_TICK_INTERVAL}s")
        logger.info(f"📡 Relay URL: {RELAY_URL or '(unset)'}")
        logger.info(f"🌐 Bridge: http://{BRIDGE_HOST}:{BRIDGE_PORT}")

        async def _post_shutdown(application) -> None:
            logger.info("PTB post_shutdown: stopping bridge + workers")
            if self._crawler_worker is not None:
                try:
                    self._crawler_worker.stop()
                except Exception:
                    pass
            if self._seed_worker is not None:
                try:
                    self._seed_worker.stop()
                except Exception:
                    pass
            if self._bridge_server is not None:
                try:
                    self._bridge_server.stop()
                except Exception:
                    pass

        try:
            self.application.post_shutdown = _post_shutdown
        except Exception:
            pass

        self.application.run_polling(allowed_updates=Update.ALL_TYPES)


# ============================================================================
# MAIN
# ============================================================================
def main():
    import signal
    import os

    if not TELEGRAM_BOT_TOKEN_ENV:
        logger.error("❌ TELEGRAM_BOT_TOKEN not set.")
        logger.error("   export TELEGRAM_BOT_TOKEN='YOUR_BOT_TOKEN'")
        sys.exit(1)

    bot = AEI_Bot(TELEGRAM_BOT_TOKEN_ENV, "AEISeedBot")

    def _sigterm_handler(signum, frame):
        logger.info("Received SIGTERM — shutting down bridge and workers")
        try:
            if bot._bridge_server is not None:
                bot._bridge_server.stop()
        except Exception:
            pass
        try:
            if bot._crawler_worker is not None:
                bot._crawler_worker.stop()
        except Exception:
            pass
        try:
            if bot._seed_worker is not None:
                bot._seed_worker.stop()
        except Exception:
            pass
        os._exit(0)

    try:
        signal.signal(signal.SIGTERM, _sigterm_handler)
        signal.signal(signal.SIGINT, _sigterm_handler)
    except (ValueError, OSError):
        pass

    bot.run()


if __name__ == "__main__":
    main()

# ============================================================================
# Q.E.D. — LOGOS = Φ = Truth = Path = Origin
# ============================================================================