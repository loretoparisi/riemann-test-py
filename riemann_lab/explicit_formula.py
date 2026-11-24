"""The Guinand-Weil explicit formula: the bridge between primes and zeros.

For an even test function h(r), holomorphic in |Im r| <= 1/2 + eps, with
g(u) = (1/2pi) \\int h(r) e^{-iru} dr, writing the zeros as rho = 1/2 + i*gamma:

    sum_gamma h(gamma) = h(i/2) + h(-i/2) - g(0) log(pi)
                         + (1/2pi) \\int h(r) Re psi(1/4 + i r/2) dr
                         - 2 sum_{n>=1} Lambda(n)/sqrt(n) g(log n).

The left side is the "spectral side", the right side the "geometric side"
(poles, archimedean place, primes). This is the F = Q, trivial-character case
of Weil's formula, which Masullo's Theorem 12.5.1.1 claims to refine: his
version keeps the same geometric side but only the zeros with
|Re rho - 1/2| <= alpha on the spectral side.

Test function used here: a pair of Gaussians centred at +-r0 with width 1/sigma,
    h(r) = exp(-sigma^2 (r-r0)^2/2) + exp(-sigma^2 (r+r0)^2/2),
    g(u) = (2/(sigma sqrt(2 pi))) exp(-u^2/(2 sigma^2)) cos(r0 u),
which probes zeros near height r0 and prime powers up to about e^{6 sigma}.
"""
from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np
from scipy import integrate, special

from .primes import sieve


def h_gauss(r, r0: float, sigma: float):
    r = np.asarray(r, dtype=complex)
    return np.exp(-sigma**2 * (r - r0) ** 2 / 2) + np.exp(-sigma**2 * (r + r0) ** 2 / 2)


def g_gauss(u, r0: float, sigma: float):
    u = np.asarray(u, dtype=float)
    return 2.0 / (sigma * math.sqrt(2 * math.pi)) * np.exp(-u**2 / (2 * sigma**2)) * np.cos(r0 * u)


def _von_mangoldt_terms(xmax: float):
    pk, lam = [], []
    for p in sieve(int(xmax)):
        q = int(p)
        while q <= xmax:
            pk.append(q); lam.append(math.log(p)); q *= int(p)
    return np.array(pk, dtype=float), np.array(lam)


@dataclass
class ExplicitFormulaResult:
    spectral: float
    poles: float
    archimedean: float
    primes: float
    zeros_used: int

    @property
    def geometric(self) -> float:
        return self.poles + self.archimedean + self.primes

    @property
    def residual(self) -> float:
        return self.spectral - self.geometric

    def __str__(self) -> str:
        return (f"spectral (zeros) = {self.spectral:.12f}\n"
                f"geometric        = {self.geometric:.12f}  [poles {self.poles:.3e}, "
                f"archimedean {self.archimedean:.6f}, primes {self.primes:.6f}]\n"
                f"residual         = {self.residual:.3e}  using {self.zeros_used} zeros")


def geometric_side(r0: float, sigma: float, umax_sigmas: float = 9.0):
    """Poles + archimedean + prime terms for the Gaussian-pair test function."""
    hp = h_gauss(0.5j, r0, sigma)
    poles = float(2 * hp.real)            # h(i/2) + h(-i/2) = 2 Re h(i/2) for even h
    arch_const = -float(g_gauss(0.0, r0, sigma)) * math.log(math.pi)
    f = lambda r: float((h_gauss(r, r0, sigma) * special.digamma(0.25 + 0.5j * r)).real.real)
    half = 12.0 / sigma
    pts = sorted({-r0 - half, -r0, -r0 + half, r0 - half, r0, r0 + half})
    arch_int = 0.0
    for a, b in zip(pts[:-1], pts[1:]):
        arch_int += integrate.quad(f, a, b, limit=400, epsabs=1e-13, epsrel=1e-13)[0]
    arch = arch_const + arch_int / (2 * math.pi)
    xmax = math.exp(umax_sigmas * sigma)
    pk, lam = _von_mangoldt_terms(xmax)
    prime = -2.0 * float(np.sum(lam / np.sqrt(pk) * g_gauss(np.log(pk), r0, sigma)))
    return poles, arch, prime


def spectral_side(zero_ordinates, r0: float, sigma: float, extra_zeros=()):
    """sum over all zeros of h(gamma); zero_ordinates are the positive gammas.

    ``extra_zeros`` lets you inject hypothetical zeros rho = beta + i*t given as
    (beta, t) pairs. Each comes with its functional-equation and conjugate
    partners, i.e. gamma = +-t +- i(beta - 1/2).
    """
    g = np.asarray(zero_ordinates, dtype=float)
    total = 2.0 * float(np.sum(h_gauss(g, r0, sigma).real))     # +gamma and -gamma
    for beta, t in extra_zeros:
        d = beta - 0.5
        for gam in (t + 1j * d, t - 1j * d):
            total += 2.0 * float(h_gauss(gam, r0, sigma).real)
    return total


def check(zero_ordinates, r0: float = 20.0, sigma: float = 1.0, extra_zeros=()) -> ExplicitFormulaResult:
    poles, arch, prime = geometric_side(r0, sigma)
    spec = spectral_side(zero_ordinates, r0, sigma, extra_zeros)
    return ExplicitFormulaResult(spec, poles, arch, prime, len(zero_ordinates))


def scan(zero_ordinates, centres, sigma: float = 1.0):
    """Residual of the explicit formula for test functions centred at each r0.

    A residual far above round-off at some r0 means the zero list is missing a
    zero near r0, or has one that is not on the line. This is a spectral
    certificate, complementary to the Turing count in ``zeros.verify_window``.
    """
    return np.array([check(zero_ordinates, r0, sigma).residual for r0 in centres])
