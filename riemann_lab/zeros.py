"""Locating zeta zeros on the critical line and certifying the count (Turing-style).

The certificate logic is the classical one used since Turing (1953):
  1. Every sign change of the real function Z(t) is a zero of zeta on the line.
  2. N(T) counts *all* zeros in the critical strip up to height T, including
     any hypothetical ones off the line.
  3. If the number of sign changes found in (T1, T2] equals N(T2) - N(T1),
     then every zero in that window lies on the critical line (and is simple).

``N`` is computed independently by ``zeta.N_exact`` (argument principle), so the
check is genuinely a verification of RH in the window, up to floating-point
reliability (this is a numerical experiment, not interval arithmetic).
"""
from __future__ import annotations

import functools
from dataclasses import dataclass

import mpmath as mp
import numpy as np
from scipy.optimize import brentq

from . import zeta


@functools.lru_cache(maxsize=None)
def zetazero(n: int, dps: int = 20) -> float:
    """Imaginary part of the n-th zero (mpmath, high precision, cached)."""
    with mp.workdps(dps):
        return float(mp.zetazero(n).imag)


def first_zeros(n: int) -> np.ndarray:
    """First n zero ordinates via mpmath (slow-ish: ~70 ms each)."""
    return np.array([zetazero(k) for k in range(1, n + 1)])


def _Zs(t):
    return float(zeta.Z(np.array([t]))) if np.ndim(t) == 0 else zeta.Z(t)


def find_zeros(T1: float, T2: float, oversample: int = 10, polish: bool = False) -> np.ndarray:
    """All sign changes of Z(t) in (T1, T2], located by bracketing + Brent.

    Grid step = mean zero spacing / oversample. Close pairs of zeros can hide
    between grid points; ``verify_window`` detects that via the N(T) count and
    retries with a finer grid.
    """
    if T1 < 10:
        raise ValueError("use first_zeros() below t=10; numpy Z needs t >= 10")
    mean_gap = 2 * np.pi / np.log(T2 / (2 * np.pi))
    step = mean_gap / oversample
    grid = np.arange(T1, T2 + step, step)
    grid = grid[grid <= T2]
    vals = zeta.Z(grid)
    idx = np.nonzero(np.sign(vals[:-1]) * np.sign(vals[1:]) < 0)[0]
    f = lambda x: float(zeta.Z(np.array([x, x]))[0])
    roots = np.array([brentq(f, grid[i], grid[i + 1], xtol=1e-12) for i in idx])
    if polish and roots.size:
        roots = np.array([float(mp.findroot(mp.siegelz, r)) for r in roots])
    return roots


@dataclass
class WindowReport:
    T1: float
    T2: float
    sign_changes: int
    N_T1: int
    N_T2: int
    oversample: int

    @property
    def expected(self) -> int:
        return self.N_T2 - self.N_T1

    @property
    def all_on_line(self) -> bool:
        return self.sign_changes == self.expected

    def __str__(self) -> str:
        verdict = "ALL ZEROS ON THE CRITICAL LINE" if self.all_on_line else "MISMATCH (refine grid or investigate)"
        return (f"window ({self.T1:g}, {self.T2:g}]: N(T2)-N(T1) = {self.N_T2}-{self.N_T1} = {self.expected}, "
                f"sign changes of Z = {self.sign_changes} (grid oversample {self.oversample}) -> {verdict}")


def _safe_T(T: float) -> float:
    """Nudge T away from a zero ordinate so that N(T) is well defined."""
    for k in range(20):
        Tk = T + 0.0137 * k
        if abs(float(zeta.Z(np.array([Tk, Tk]))[0])) > 1e-3:
            return Tk
    return T


def verify_window(T1: float, T2: float, max_refine: int = 4):
    """Turing-style certificate that all zeros with T1 < t <= T2 are on the line."""
    T1, T2 = _safe_T(T1), _safe_T(T2)
    n1, n2 = zeta.N_exact(T1), zeta.N_exact(T2)
    over = 10
    for _ in range(max_refine):
        roots = find_zeros(T1, T2, oversample=over)
        rep = WindowReport(T1, T2, len(roots), n1, n2, over)
        if rep.all_on_line:
            return rep, roots
        over *= 4
    return rep, roots


def gram_law_stats(n0: int, n1: int) -> dict:
    """Fraction of Gram intervals [g_n, g_n+1) obeying Gram's law ((-1)^n Z(g_n) > 0)."""
    g = zeta.gram_points(n0, n1)
    z = zeta.Z(g)
    good = ((-1.0) ** np.arange(n0, n1 + 1)) * z > 0
    return {"n0": n0, "n1": n1, "good": int(good.sum()), "bad": int((~good).sum()),
            "fraction_good": float(good.mean())}
