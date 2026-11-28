"""Majorana regularisation of the combined norm (numerical evidence, not proof).

Two regularisations of N(alpha) = int_0^oo |M_chi|^2 x^(1-2alpha) dx built from Majorana's tower D+:

  R1  tower cut-off: N_n = sum_{m<n} |c_m|^2, c_m = <M_chi, psi_m> in the orthonormal basis
      psi_m(t) = N_m t^(2alpha-1) e^(-t) L_m^(2alpha-1)(2t) of L^2(t^(1-2alpha) dt), N_m^2 = 2^(2alpha) m!/Gamma(m+2alpha).
      Generating function: sum_m r^m c_m/N_m = (1-r)^(-2alpha) (Laplace M)((1+r)/(1-r)).
  R2  Tikhonov on the boost at the critical line: N_eps = (1/2pi) int |Gamma(1/4+iE)|^2 / (|L(1/2-2iE)|^2 + eps) dE.

Both are finite for every chi at a fixed parameter, so neither is a GRH criterion at a fixed parameter; both
increase to the unregularised quantity, so in the limit they give back `grh_iff_finite_norm` and nothing more.
"""
from __future__ import annotations

import math

import mpmath as mp
import numpy as np

from . import combined as C, hlr


def _lognorm(m: np.ndarray, alpha: float) -> np.ndarray:
    from scipy.special import gammaln
    return 0.5 * (2 * alpha * math.log(2) + gammaln(m + 1) - gammaln(m + 2 * alpha))


def circle(K: int, decay: float = 1e-12):
    rho = decay ** (1.0 / K)
    r = rho * np.exp(2j * math.pi * np.arange(K) / K)
    return rho, r


def coeffs_from_values(G: np.ndarray, rho: float, nmax: int, alpha: float) -> np.ndarray:
    K = len(G)
    a = np.fft.fft(G) / K
    m = np.arange(nmax)
    return a[:nmax] * np.exp(-m * math.log(rho)) * np.exp(_lognorm(m.astype(float), alpha))


def laplace_M(F: C.Holo, p: np.ndarray, chunk: int = 1024) -> np.ndarray:
    """int_0^oo M(t) e^(-pt) dt = F(ip), F the holomorphic Majorana vector (n-sum with tails)."""
    out = np.empty(len(p), dtype=complex)
    for i in range(0, len(p), chunk):
        out[i:i + chunk] = F(1j * p[i:i + chunk])
    return out


def tower_coeffs_true(chi, alpha: float, nmax: int, K: int, N: int = 3000) -> np.ndarray:
    rho, r = circle(K)
    p = (1 + r) / (1 - r)
    F = C.Holo(chi, N)
    G = (1 - r) ** (-2 * alpha) * laplace_M(F, p)
    return coeffs_from_values(G, rho, nmax, alpha)


# ------------------------------------------------------------------ model terms D(x) = sum d_j (1 - e^-x) x^(-s_j)
def model_terms(beta, gamma1=None, dps: int = 30, chi=None):
    """L(chi) (zeta if chi is None; chi must be real) with its first zero pair 1/2 +- i gamma1 replaced by beta +- i gamma1, 1 - beta +- i gamma1: the list of
    (s_j, d_j) to add to the x side (removed zeros enter with -c_rho). Residue coefficients as in hlr.ZeroExpansion."""
    with mp.workdps(dps):
        if gamma1 is None:
            g1 = mp.zetazero(1).imag
        else:
            g1 = mp.findroot(lambda t: hlr.L_of(chi)(mp.mpc(0.5, mp.re(t))), mp.mpf(gamma1))
            g1 = mp.re(g1)
        beta = mp.mpf(beta)
        Lmod = C.moved_zero_L(chi, g1, beta)
        Ld = hlr.Ld_of(chi)
        out = []
        for sgn in (1, -1):
            rho = mp.mpc(0.5, sgn * g1)
            s = (1 - rho) / 2
            out.append((complex(s), -complex(mp.gamma(s) / (2 * Ld(rho)))))
            for b in (beta, 1 - beta):
                rp = mp.mpc(b, sgn * g1)
                sp = (1 - rp) / 2
                out.append((complex(sp), complex(mp.gamma(sp) / (2 * mp.diff(Lmod, rp)))))
    return out


def model_G(terms, alpha: float, r: np.ndarray) -> np.ndarray:
    """(1-r)^(-2alpha) Laplace(D)(p): Laplace of (1 - e^-x) x^-s is Gamma(1-s) (p^(s-1) - (p+1)^(s-1))."""
    G = np.zeros(len(r), dtype=complex)
    for s, d in terms:
        g = complex(mp.gamma(1 - s))
        G += d * g * ((1 + r) ** (s - 1) * (1 - r) ** (1 - s - 2 * alpha) - 2 ** (s - 1) * (1 - r) ** (1 - s - 2 * alpha))
    return G


def tower_coeffs_model(terms, alpha: float, nmax: int, K: int) -> np.ndarray:
    rho, r = circle(K)
    return coeffs_from_values(model_G(terms, alpha, r), rho, nmax, alpha)


def _binom_series(A: complex, n: int, sign: float) -> np.ndarray:
    """Taylor coefficients of (1 + sign r)^A."""
    b = np.empty(n, dtype=complex)
    b[0] = 1
    for m in range(n - 1):
        b[m + 1] = b[m] * (A - m) / (m + 1) * sign
    return b


def tower_coeffs_model_exact(terms, alpha: float, nmax: int) -> np.ndarray:
    """Same coefficients from exact binomial series (convolution), an independent check of the FFT."""
    tot = np.zeros(nmax, dtype=complex)
    for s, d in terms:
        g = complex(mp.gamma(1 - s))
        A = 1 - s - 2 * alpha
        a1 = _binom_series(A, nmax, -1.0)
        tot += d * g * (np.convolve(_binom_series(s - 1, nmax, 1.0), a1)[:nmax] - 2 ** (s - 1) * a1)
    m = np.arange(nmax, dtype=float)
    return tot * np.exp(_lognorm(m, alpha))


def partial_norms(c: np.ndarray, ns) -> list:
    cs = np.cumsum(np.abs(c) ** 2)
    return [float(cs[n - 1]) for n in ns]


# ------------------------------------------------------------------ R2: Tikhonov at the critical line
def tikhonov_critical(chi, eps: float, zeros_t, t_max: float = 24.0, L_override=None, dps: int = 20) -> float:
    """(1/2pi) int |Gamma(1/4 + iE)|^2 / (|L(1/2 - 2iE)|^2 + eps) dE, breakpoints refined at the peaks E = zeros_t
    down to the width sqrt(eps)/(2|L'|) ~ sqrt(eps)."""
    Lf = L_override or hlr.L_of(chi)
    with mp.workdps(dps):
        q = mp.mpf(1) / 4
        f = lambda E: abs(mp.gamma(mp.mpc(q, E))) ** 2 / (abs(Lf(mp.mpc(0.5, -2 * E))) ** 2 + eps)
        pts = {mp.mpf(x) for x in np.arange(-t_max, t_max + 1e-9, 1.0).round(6).tolist()}
        w = mp.sqrt(eps) / 4
        for t0 in zeros_t:
            t0 = mp.mpf(t0)
            if abs(t0) < t_max - 1:
                pts.add(t0)
                s = w
                while s < 0.5:
                    pts.update((t0 - s, t0 + s))
                    s *= 3
        pts = sorted(p for p in pts if -t_max <= p <= t_max)
        return float(mp.quad(f, pts) / (2 * mp.pi))


def tikhonov_limit_pred(chi, rhos, L_override=None, dps: int = 30) -> float:
    """S = sum_rho |Gamma((1-rho)/2)|^2 / (4 |L'(rho)|): sqrt(eps) N_eps -> S."""
    tot = 0.0
    with mp.workdps(dps):
        for rho in rhos:
            rho = mp.mpc(rho)
            Ld = mp.diff(L_override, rho) if L_override is not None else hlr.Ld_of(chi)(rho)
            tot += float(abs(mp.gamma((1 - rho) / 2)) ** 2 / (4 * abs(Ld)))
    return tot
