"""Prime counting: pi(x), Li(x), Riemann's R(x) and the explicit formulas.

Riemann's 1859 explicit formula (in the Riesel-Gohl form):

    pi_0(x) = R(x) - sum_rho R(x^rho) - 1/log x + arctan(pi/log x)/pi

and von Mangoldt's formula for Chebyshev's psi:

    psi_0(x) = x - sum_rho x^rho/rho - log(2 pi) - log(1 - x^-2)/2.

Truncating the sum over zeros at K pairs shows the "music": each zero adds
one oscillating harmonic, and the staircase emerges as K grows.
"""
from __future__ import annotations

import math

import mpmath as mp
import numpy as np


def sieve(n: int) -> np.ndarray:
    """Primes <= n (numpy sieve of Eratosthenes)."""
    if n < 2:
        return np.array([], dtype=np.int64)
    is_p = np.ones(n + 1, dtype=bool)
    is_p[:2] = False
    for p in range(2, int(n**0.5) + 1):
        if is_p[p]:
            is_p[p * p::p] = False
    return np.nonzero(is_p)[0]


def prime_pi(x, primes: np.ndarray | None = None):
    """pi(x) for scalar or array x."""
    x = np.asarray(x, dtype=float)
    if primes is None:
        primes = sieve(int(np.max(x)))
    return np.searchsorted(primes, x, side="right")


def Li(x):
    """Offset logarithmic integral Li(x) = li(x) - li(2)."""
    return np.vectorize(lambda v: float(mp.li(v) - mp.li(2)))(x)


def li(x):
    return np.vectorize(lambda v: float(mp.li(v)))(x)


def R(x):
    """Riemann's R(x) = sum mu(n)/n li(x^(1/n)) (Gram series, mpmath.riemannr)."""
    return np.vectorize(lambda v: float(mp.riemannr(v)))(x)


def _mobius_small(n: int) -> int:
    res, m, p = 1, n, 2
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            res = -res
        p += 1
    return -res if m > 1 else res


def _R_complex(logx_rho: complex, logx: float) -> complex:
    """R(x^rho) = sum_n mu(n)/n * Ei(rho log x / n), truncated where terms die out."""
    total = mp.mpc(0)
    nmax = max(2, int(3 * logx) + 5)
    for n in range(1, nmax + 1):
        mu = _mobius_small(n)
        if mu:
            total += mu / mp.mpf(n) * mp.ei(logx_rho / n)
    return total


def pi_explicit(x, zero_ordinates: np.ndarray) -> np.ndarray:
    """Riemann's explicit formula for pi_0(x) truncated to the given zeros (conjugate pairs)."""
    xs = np.atleast_1d(np.asarray(x, dtype=float))
    out = []
    for v in xs:
        L = math.log(v)
        s = mp.riemannr(v) - 1 / mp.mpf(L) + mp.atan(mp.pi / L) / mp.pi
        for g in zero_ordinates:
            rho = mp.mpc(0.5, g)
            s -= 2 * mp.re(_R_complex(rho * L, L))
        out.append(float(s))
    return np.array(out)


def chebyshev_psi(x, primes: np.ndarray | None = None):
    """psi(x) = sum_{p^k <= x} log p (numpy)."""
    xs = np.atleast_1d(np.asarray(x, dtype=float))
    if primes is None:
        primes = sieve(int(xs.max()))
    # list prime powers with their log p weight, then cumulative sum
    pk, w = [], []
    for p in primes:
        q = p
        while q <= xs.max():
            pk.append(q); w.append(math.log(p)); q *= p
    order = np.argsort(pk)
    pk = np.array(pk, dtype=float)[order]
    cw = np.cumsum(np.array(w)[order])
    idx = np.searchsorted(pk, xs, side="right")
    return np.where(idx > 0, cw[np.maximum(idx - 1, 0)], 0.0)


def psi_explicit(x, zero_ordinates: np.ndarray) -> np.ndarray:
    """von Mangoldt explicit formula for psi_0(x) with the given zeros (pairs)."""
    xs = np.atleast_1d(np.asarray(x, dtype=float))
    g = np.asarray(zero_ordinates, dtype=float)
    rho = 0.5 + 1j * g
    out = []
    for v in xs:
        osc = np.sum(2 * np.real(np.exp(rho * np.log(v)) / rho))
        out.append(v - osc - math.log(2 * math.pi) - 0.5 * math.log(1 - v**-2))
    return np.array(out)


def schoenfeld_bound(x):
    """Under RH: |pi(x) - li(x)| < sqrt(x) log(x) / (8 pi) for x >= 2657 (Schoenfeld 1976)."""
    x = np.asarray(x, dtype=float)
    return np.sqrt(x) * np.log(x) / (8 * np.pi)


def check_schoenfeld(xmax: int = 10**7, npts: int = 2000) -> dict:
    """Check Schoenfeld's RH-conditional bound on a log-spaced grid up to xmax."""
    primes = sieve(xmax)
    xs = np.unique(np.geomspace(2657, xmax, npts).astype(int)).astype(float)
    err = np.abs(prime_pi(xs, primes) - li(xs))
    bound = schoenfeld_bound(xs)
    ratio = err / bound
    return {"xmax": xmax, "max_ratio": float(ratio.max()), "argmax_x": float(xs[ratio.argmax()]),
            "holds": bool((ratio < 1).all())}
