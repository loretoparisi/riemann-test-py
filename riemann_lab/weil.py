"""Weil's positivity criterion, tested on finite families of test functions.

Weil (1952):  RH  <=>  W(g * g~) >= 0 for every (nice) test function g,
where W is the explicit-formula functional (the geometric side of
``explicit_formula``: poles + archimedean place + primes) and g~(u) = g(-u).
For h = |g^|^2 the spectral side sum_gamma h(gamma) is visibly >= 0 when every
gamma is real; the criterion says the *prime side alone* is always >= 0.

Family used here: Gaussians of width s placed at u_1..u_m on the log-scale,
g = sum_j c_j G_s(u - u_j). Then W(g * g~) = c^T M c with the m x m Weil matrix

    M_ij = W(h_ij),  h_ij(r) = e^{-s^2 r^2} cos(r (u_i - u_j)),
    g_ij(u) = (1/(4 sqrt(pi) s)) [e^{-(u - D)^2/(4 s^2)} + e^{-(u + D)^2/(4 s^2)}],  D = u_i - u_j,

so Weil positivity on this family is exactly  "M is positive semidefinite".
We build M twice:
  * from primes (geometric side: Lambda(n) for n <= e^{max D + 9 s}, plus the
    archimedean integral by the trapezoid rule, which is spectrally accurate here),
  * from zeros (spectral side, 2 sum_{gamma > 0} e^{-s^2 gamma^2} cos(gamma D)),
compare them entrywise, and report the smallest eigenvalue of the prime-side M.
A hypothetical zero beta + i t with beta != 1/2 adds an *indefinite* rank-2 term
(``fake_offline_zero``), so the family can detect such a zero.

A second, scalar family (Gaussian bumps centred at height r0, h >= 0 on R) is
scanned over (r0, sigma) for W(h) >= 0 using only the prime side.
"""
from __future__ import annotations

import math

import numpy as np
from scipy import special

from . import explicit_formula
from .explicit_formula import _von_mangoldt_terms


def _arch_integral(s: float, D: np.ndarray, dr: float = 0.01) -> np.ndarray:
    """(1/2pi) int e^{-s^2 r^2} cos(r D) Re psi(1/4 + i r/2) dr for each D (trapezoid rule)."""
    R = 7.0 / s
    r = np.arange(0.0, R + dr, dr)
    w = np.exp(-(s * r) ** 2) * special.digamma(0.25 + 0.5j * r).real
    wt = np.full(r.size, dr)
    wt[0] = dr / 2                                  # even integrand: 2 * int_0^R
    return np.array([2 * np.sum(wt * w * np.cos(r * d)) for d in D]) / (2 * math.pi)


def g_shift(u, s: float, D):
    u = np.asarray(u, dtype=float)
    c = 1.0 / (4 * math.sqrt(math.pi) * s)
    return c * (np.exp(-(u - D) ** 2 / (4 * s * s)) + np.exp(-(u + D) ** 2 / (4 * s * s)))


def geometric_values(s: float, D: np.ndarray) -> np.ndarray:
    """W(h_D) from primes + archimedean + poles for each shift D."""
    D = np.asarray(D, dtype=float)
    poles = 2 * math.exp(s * s / 4) * np.cosh(D / 2)
    arch = -g_shift(0.0, s, D) * math.log(math.pi) + _arch_integral(s, D)
    xmax = math.exp(D.max() + 18 * s)
    pk, lam = _von_mangoldt_terms(xmax)
    lp = np.log(pk)
    prime = np.array([-2.0 * np.sum(lam / np.sqrt(pk) * g_shift(lp, s, d)) for d in D])
    return poles + arch + prime


def spectral_values(s: float, D: np.ndarray, zero_ordinates, extra_zeros=()) -> np.ndarray:
    D = np.asarray(D, dtype=float)
    g = np.asarray(zero_ordinates, dtype=float)
    out = 2 * np.array([np.sum(np.exp(-(s * g) ** 2) * np.cos(g * d)) for d in D])
    for beta, t in extra_zeros:
        dl = beta - 0.5
        for gam in (t + 1j * dl, t - 1j * dl):
            out = out + 2 * np.real(np.exp(-(s * gam) ** 2) * np.cos(gam * D))
    return out


def weil_matrix(s: float, centres, zero_ordinates=None, extra_zeros=(), side: str = "geometric"):
    u = np.asarray(centres, dtype=float)
    D = u[:, None] - u[None, :]
    Du, inv = np.unique(np.abs(D).round(12), return_inverse=True)
    if side == "geometric":
        vals = geometric_values(s, Du)
    else:
        vals = spectral_values(s, Du, zero_ordinates, extra_zeros)
    return vals[inv].reshape(D.shape)


def check_family(s: float, m: int, du: float, zero_ordinates, extra_zeros=()) -> dict:
    """Weil matrix for m Gaussians of width s spaced du apart on the log scale."""
    centres = du * np.arange(m)
    Mg = weil_matrix(s, centres)
    Ms = weil_matrix(s, centres, zero_ordinates, side="spectral")
    eg = np.linalg.eigvalsh(Mg)
    es = np.linalg.eigvalsh(Ms)
    err = float(np.abs(Mg - Ms).max())
    out = {"s": s, "m": m, "du": du, "lambda_min_primes": float(eg[0]), "lambda_max_primes": float(eg[-1]),
           "lambda_min_zeros": float(es[0]), "max_entry_diff": err,
           "positive_within_error": bool(eg[0] > -m * err - 1e-13)}
    if extra_zeros:
        Mf = weil_matrix(s, centres, zero_ordinates, extra_zeros, side="spectral")
        out["lambda_min_with_offline_zero"] = float(np.linalg.eigvalsh(Mf)[0])
    return out


def scalar_scan(centres=np.linspace(0, 60, 31), sigmas=(0.3, 0.6, 1.0), tol: float = 1e-12) -> dict:
    """W(h) from primes alone for the Gaussian-pair family of ``explicit_formula`` (h >= 0).

    Where no zero is near r0 the true W(h) is far below round-off (e.g. ~1e-22 at r0 = 4),
    so positivity is asserted up to ``tol``.
    """
    vals = np.array([[sum(explicit_formula.geometric_side(r0, sg)) for r0 in centres] for sg in sigmas])
    i, j = np.unravel_index(np.argmin(vals), vals.shape)
    return {"count": int(vals.size), "min_W": float(vals[i, j]), "at": (float(centres[j]), float(sigmas[i])),
            "nonnegative_within_tol": bool((vals > -tol).all()), "tol": tol, "values": vals}


def summary(zero_ordinates, configs=((0.1, 12, 0.35), (0.07, 16, 0.3), (0.05, 24, 0.25)),
            fake=((0.6, 30.0),)) -> dict:
    fam = [check_family(s, m, du, zero_ordinates, extra_zeros=fake) for s, m, du in configs]
    return {"families": fam, "scalar": scalar_scan()}
