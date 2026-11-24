"""Masullo's toy trace formula (The Music of the Primes, Example 1.8.1.1).

On functions on the circle R>0 / gamma^Z, convolution by a test function phi,
    A(phi) f(x) = \\int phi(t) f(x/t) dt/t,
is trace class. Its eigenfunctions are the characters t^{z_m}, z_m = 2 pi i m / log gamma,
with eigenvalues M(phi)(z_m) (Mellin transform), so

    Trace A(phi) = sum_m M(phi)(z_m)                  (spectral side)
                 = log(gamma) * sum_k phi(gamma^k)    (geometric side, Poisson).

If supp(phi) lies strictly inside (1, gamma) the trace is 0. In the book this is
why each prime p outside a finite set S contributes nothing to the global trace
("orbital traces vanish"), with gamma playing the role of N(p).

Here we compute the trace three ways: spectral sum, Poisson sum, and the
literal trace of a discretised operator matrix.
"""
from __future__ import annotations

import math

import numpy as np


def bump(u, centre: float, width: float):
    """Smooth compactly supported bump in the log variable u = log t."""
    x = (np.asarray(u, dtype=float) - centre) / width
    out = np.zeros_like(x)
    inside = np.abs(x) < 1
    out[inside] = np.exp(-1.0 / (1.0 - x[inside] ** 2))
    return out


def mellin(phi_log, s, a: float, b: float, n: int = 20001):
    r"""M(phi)(s) = \int phi(t) t^s dt/t = \int Phi(u) e^{su} du, Phi(u) = phi(e^u) supported in [a,b].

    Trapezoid rule on a dense grid: spectrally accurate for smooth compactly supported Phi.
    ``s`` may be an array.
    """
    u = np.linspace(a, b, n)
    w = np.full(n, (b - a) / (n - 1)); w[[0, -1]] /= 2
    s = np.atleast_1d(np.asarray(s, dtype=complex))
    vals = (phi_log(u) * w)[None, :] * np.exp(s[:, None] * u[None, :])
    out = vals.sum(axis=1)
    return out if out.size > 1 else out[0]


def trace_spectral(phi_log, gamma: float, a: float, b: float, mmax: int = 400) -> float:
    L = math.log(gamma)
    z = 2j * math.pi * np.arange(-mmax, mmax + 1) / L
    return float(np.sum(mellin(phi_log, z, a, b)).real)


def trace_geometric(phi_log, gamma: float, a: float, b: float) -> float:
    L = math.log(gamma)
    ks = range(math.floor(a / L) - 1, math.ceil(b / L) + 2)
    return L * float(sum(phi_log(np.array([k * L]))[0] for k in ks))


def trace_matrix(phi_log, gamma: float, a: float, b: float, n: int = 2000) -> float:
    """Literal trace of the discretised periodic convolution operator on [0, log gamma)."""
    L = math.log(gamma)
    u = np.arange(n) * L / n
    du = L / n
    diff = u[:, None] - u[None, :]
    K = np.zeros((n, n))
    for k in range(math.floor(a / L) - 1, math.ceil(b / L) + 2):
        K += phi_log(diff + k * L)
    return float(np.trace(K) * du)


def demo(gamma: float = 7.0, centre: float = 1.0, width: float = 0.8) -> dict:
    """Return the three traces for phi = bump(log t; centre, width)."""
    phi = lambda u: bump(u, centre, width)
    a, b = centre - width, centre + width
    return {"gamma": gamma, "support_log": (a, b), "inside_(1,gamma)": bool(a > 0 and b < math.log(gamma)),
            "spectral": trace_spectral(phi, gamma, a, b), "geometric": trace_geometric(phi, gamma, a, b),
            "matrix": trace_matrix(phi, gamma, a, b)}
