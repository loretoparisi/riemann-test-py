"""Riemann-Siegel machinery: theta, Z(t), Gram points and zero counting N(T).

Two implementations of Z(t):
  * ``Z_mp``  -- mpmath.siegelz, arbitrary precision (slow, reference).
  * ``Z``     -- vectorised numpy Riemann-Siegel main sum + first correction term
                 C0. Error is O(t^{-3/4}); fine for locating zeros and for
                 statistics above t ~ 100. Use ``Z_mp`` to polish if needed.
"""
from __future__ import annotations

import numpy as np
import mpmath as mp

TWO_PI = 2.0 * np.pi


# ---------------------------------------------------------------- theta
def theta(t):
    """Riemann-Siegel theta via its asymptotic expansion (accurate for t > ~10)."""
    t = np.asarray(t, dtype=float)
    return (t / 2.0) * np.log(t / TWO_PI) - t / 2.0 - np.pi / 8.0 \
        + 1.0 / (48.0 * t) + 7.0 / (5760.0 * t**3) + 31.0 / (80640.0 * t**5)


def theta_mp(t):
    """Exact Riemann-Siegel theta (mpmath)."""
    return mp.siegeltheta(t)


# ---------------------------------------------------------------- Z(t)
def Z_mp(t):
    """Hardy's Z function at arbitrary precision. Real for real t, |Z(t)| = |zeta(1/2+it)|."""
    return mp.siegelz(t)


def _c0(p):
    num = np.cos(TWO_PI * (p * p - p - 1.0 / 16.0))
    den = np.cos(TWO_PI * p)
    bad = np.abs(den) < 1e-8          # removable singularity at p = 1/4, 3/4
    if np.any(bad):
        pe = p + 1e-6
        num = np.where(bad, np.cos(TWO_PI * (pe * pe - pe - 1.0 / 16.0)), num)
        den = np.where(bad, np.cos(TWO_PI * pe), den)
    return num / den


def Z(t, chunk: int = 4096):
    """Vectorised Riemann-Siegel Z(t) for t >= ~10 (numpy, float64)."""
    t = np.atleast_1d(np.asarray(t, dtype=float))
    out = np.empty_like(t)
    for start in range(0, t.size, chunk):
        tt = t[start:start + chunk]
        tau = np.sqrt(tt / TWO_PI)
        N = np.floor(tau).astype(int)
        p = tau - N
        nmax = int(N.max())
        n = np.arange(1, nmax + 1, dtype=float)
        th = theta(tt)
        phase = th[:, None] - tt[:, None] * np.log(n)[None, :]
        terms = np.cos(phase) / np.sqrt(n)[None, :]
        mask = n[None, :] <= N[:, None]
        main = 2.0 * np.sum(terms * mask, axis=1)
        sign = np.where((N - 1) % 2 == 0, 1.0, -1.0)
        corr = sign * (TWO_PI / tt) ** 0.25 * _c0(p)
        out[start:start + chunk] = main + corr
    return out if out.size > 1 else out[0]


# ---------------------------------------------------------------- Gram points
def gram_point(n: int, tol: float = 1e-12) -> float:
    """g_n with theta(g_n) = n*pi, by Newton's method (theta'(t) ~ log(t/2pi)/2)."""
    if n < -1:
        raise ValueError("Gram points are defined for n >= -1")
    w = float(mp.lambertw((8 * n + 1) / (8 * np.e)).real)
    t = max(TWO_PI * np.exp(1.0 + w), 10.0)
    for _ in range(50):
        f = float(theta(t)) - n * np.pi
        step = f / (0.5 * np.log(t / TWO_PI))
        t -= step
        if abs(step) < tol:
            break
    return t


def gram_points(n0: int, n1: int) -> np.ndarray:
    return np.array([gram_point(n) for n in range(n0, n1 + 1)])


# ---------------------------------------------------------------- counting
def N_smooth(T):
    """Smooth part of the zero-counting function: theta(T)/pi + 1."""
    return theta(T) / np.pi + 1.0


def S(T: float, n: int = 64, dps: int = 15) -> float:
    """S(T) = arg zeta(1/2+iT)/pi by continuous variation (Backlund).

    arg zeta is 0 at s=2 and stays principal along Re s = 2 (|zeta(2+it)-1| < 1),
    so we follow arg zeta(sigma+iT) from sigma=2 down to 1/2, sampling densely
    enough that consecutive phases differ by < pi/4 (the grid is refined until so).
    T must not be the ordinate of a zero.
    """
    with mp.workdps(dps):
        while True:
            sig = np.linspace(2.0, 0.5, n)
            vals = [mp.zeta(mp.mpc(x, T)) for x in sig]
            ph = np.array([float(mp.arg(v)) for v in vals])
            d = np.diff(np.unwrap(ph))
            if np.all(np.abs(d) < np.pi / 4) or n > 8192:
                break
            n *= 2
        return float(np.unwrap(ph)[-1] / np.pi)


def N_exact(T: float) -> int:
    """Number of zeros with 0 < Im rho <= T, via N(T) = theta(T)/pi + 1 + S(T)."""
    val = float(theta_mp(T)) / np.pi + 1.0 + S(T)
    n = int(round(val))
    if abs(val - n) > 0.1:
        raise ArithmeticError(f"N(T) not near an integer ({val}); T may be too close to a zero")
    return n
