"""Random-matrix statistics of zeta zeros (Montgomery 1973, Odlyzko 1987).

Unfold the zeros with the smooth counting function so that the mean spacing
is 1, then compare:
  * nearest-neighbour spacings with the GUE Wigner surmise
        p(s) = (32/pi^2) s^2 exp(-4 s^2/pi)
    (and with GOE and Poisson, which should fit badly);
  * pair correlation with Montgomery's 1 - (sin(pi u)/(pi u))^2.
A good GUE fit is the main numerical evidence for the Hilbert-Polya idea that the
zeros are eigenvalues of a self-adjoint (unitary-symmetry) operator.
"""
from __future__ import annotations

import numpy as np
from scipy import integrate, stats

from . import zeta


def unfold(zero_ordinates) -> np.ndarray:
    return zeta.N_smooth(np.asarray(zero_ordinates, dtype=float))


def spacings(zero_ordinates) -> np.ndarray:
    return np.diff(unfold(zero_ordinates))


def gue_pdf(s):
    s = np.asarray(s, dtype=float)
    return 32 / np.pi**2 * s**2 * np.exp(-4 * s**2 / np.pi)


def goe_pdf(s):
    s = np.asarray(s, dtype=float)
    return np.pi / 2 * s * np.exp(-np.pi * s**2 / 4)


def poisson_pdf(s):
    return np.exp(-np.asarray(s, dtype=float))


def _cdf(pdf):
    def cdf(x):
        x = np.atleast_1d(np.asarray(x, dtype=float))
        return np.array([integrate.quad(pdf, 0, v)[0] for v in x])
    return cdf


def gue_cdf(x):
    x = np.asarray(x, dtype=float)
    # closed form of the Wigner GUE surmise CDF
    from scipy.special import erf
    return erf(2 * x / np.sqrt(np.pi)) - 4 * x / np.pi * np.exp(-4 * x**2 / np.pi)


def goe_cdf(x):
    return 1 - np.exp(-np.pi * np.asarray(x, dtype=float) ** 2 / 4)


def poisson_cdf(x):
    return 1 - np.exp(-np.asarray(x, dtype=float))


def ks_distances(s) -> dict:
    s = np.asarray(s, dtype=float)
    return {name: float(stats.kstest(s, cdf).statistic)
            for name, cdf in (("GUE", gue_cdf), ("GOE", goe_cdf), ("Poisson", poisson_cdf))}


def montgomery(u):
    u = np.asarray(u, dtype=float)
    with np.errstate(invalid="ignore", divide="ignore"):
        r = 1 - (np.sin(np.pi * u) / (np.pi * u)) ** 2
    return np.where(u == 0, 0.0, r)


def pair_correlation(zero_ordinates, umax: float = 3.0, bins: int = 60):
    """Histogram density of unfolded differences x_j - x_i in (0, umax]."""
    x = np.sort(unfold(zero_ordinates))
    diffs = []
    for k in range(1, 40):
        d = x[k:] - x[:-k]
        diffs.append(d[d <= umax])
    d = np.concatenate(diffs)
    hist, edges = np.histogram(d, bins=bins, range=(0, umax))
    centres = 0.5 * (edges[1:] + edges[:-1])
    density = hist / (len(x) * (edges[1] - edges[0]))
    return centres, density
