"""Ramanujan + Majorana + Masullo: one norm, four computations (numerical evidence, not proof).

For a primitive character chi (None = zeta), M_chi(x) = sum mu chi(n)/n e^{-x/n^2} = sum (-x)^k/(k! L(2k+1, chi))
(Ramanujan, via the Master Theorem) and F_chi(w) = int_0^oo M_chi(t) e^{iwt} dt = sum mu chi(n) n/(1 - i n^2 w)
(holomorphic on Im w > 0). With alpha = 1 - c in (1/2, 1):

    ||F_chi||^2_{D+_alpha} := 2^(2alpha-1)/(2pi Gamma(2alpha-1)) int_H |F_chi(u+iv)|^2 v^(2alpha-2) du dv  (Majorana)
                            = int_0^oo |M_chi(t)|^2 t^(1-2alpha) dt                                     (Laplace side)
                            = int_0^oo |M_chi(x)|^2 x^(2c) dx/x                    (Masullo's seminorm on Re z = c)
                            = (1/2pi) int |Gamma(c+it) / L(1-2c-2it, chi)|^2 dt               (RMT + Plancherel)

(the first equality is Paley-Wiener: int |F(u+iv)|^2 du = 2pi int |M(t)|^2 e^{-2vt} dt, then int_0^oo v^(2a-2)
e^{-2vt} dv = Gamma(2a-1) (2t)^(1-2a)). The last line needs the Mellin transform of M_chi to be Gamma(s)/L(1-2s)
on Re s = c, which for 0 < c < 1/4 is equivalent to L(w, chi) != 0 on 1 - 2c <= Re w < 1, so:

  GRH(chi) <=> F_chi in D+_alpha for all alpha in (3/4, 1) <=> the line norms are finite for all c in (0, 1/4),
  and with simple zeros (1/4 - c) ||.||^2 -> B_chi = (1/8) sum_rho |Gamma((1-rho)/2)/L'(rho, chi)|^2 as c -> 1/4.

This is a reformulation of GRH (Hardy-Littlewood 1918 / Garg-Maji 2022 in Hilbert-space dress), not a proof.
"""
from __future__ import annotations

import math

import mpmath as mp
import numpy as np
from scipy import integrate

from . import hlr


# ------------------------------------------------------------------ helpers
def _terms(zexp: hlr.ZeroExpansion, X0: float, tol: float = 1e-22):
    """All expansion terms (s0, c) as arrays: nontrivial + the trivial ones that matter beyond X0."""
    s = list(zexp.s0)
    c = list(zexp.c)
    for s0, cc in zexp.triv:
        if abs(cc) * X0 ** (-float(s0)) < tol:
            break
        s.append(complex(s0))
        c.append(complex(cc))
    return np.array(s, dtype=complex), np.array(c, dtype=complex)


def B_from_zeros(zexp: hlr.ZeroExpansion) -> float:
    """B = (1/2) sum |c_rho|^2 with c_rho = Gamma((1-rho)/2) / (2 L'(rho)), i.e. (1/8) sum |Gamma/L'|^2."""
    return float(0.5 * np.sum(np.abs(zexp.c) ** 2))


# ------------------------------------------------------------------ Masullo line norm: x side and Mellin side
def line_norm_x(c: float, ser: hlr.Series, zexp: hlr.ZeroExpansion, X0: float, c0=0) -> float:
    """int_0^oo |M - c0|^2 x^(2c-1) dx: power series on [0, X0] (for c > 0, x = y^(1/2c) on [0, 1] removes the
    endpoint singularity), then sum_{k,l} c_k conj(c_l) X0^(2c - s_k - conj s_l) / (s_k + conj s_l - 2c) beyond
    X0, the constant -c0 entering as a term with s = 0. c0 = 1/L(1, chi) with -1 < c < 0 is the unconditional
    case (no zeros needed for the identity to hold); c0 = 0 with 0 < c < 1/4 is the GRH-equivalent one."""
    with mp.workdps(20):
        c0m = mp.mpc(c0)
        if c > 0:
            e = 1 / (2 * mp.mpf(c))
            a = mp.quad(lambda y: abs(ser(y ** e) - c0m) ** 2, [0, 0.5, 1]) * e
        else:
            # |M - c0|^2 = x^2 |G(x)|^2 with G = sum_{k>=1} (-1)^k x^(k-1) inv_k / k! smooth; x = y^(1/(2c+2))
            # turns int_0^1 x^(2c+1) |G|^2 dx into int_0^1 |G|^2 dy / (2c + 2) (no endpoint singularity)
            def G(x):
                with mp.workdps(ser.dps):
                    tot, term = mp.mpf(0), mp.mpf(-1)
                    for k in range(1, ser.kmax + 1):
                        tot += term * ser.inv[k]
                        term *= -x / (k + 1)
                    return tot
            e = 1 / (2 * mp.mpf(c) + 2)
            a = mp.quad(lambda y: abs(G(y ** e)) ** 2, [0, 0.5, 1]) * e
        pts = [1] + [p for p in (5, 15, 30) if p < X0] + [X0]
        b = mp.quad(lambda x: abs(ser(x) - c0m) ** 2 * x ** (2 * c - 1), pts)
    s, cc = _terms(zexp, X0)
    if c0 != 0:
        s = np.append(s, 0.0)
        cc = np.append(cc, -complex(c0))
    S = s[:, None] + np.conj(s)[None, :] - 2 * c
    tail = np.sum(cc[:, None] * np.conj(cc)[None, :] * np.exp(-S * math.log(X0)) / S)
    return float(a + b) + float(tail.real)


def line_norm_mellin(chi, c, t_max: float = 40.0, zeros_t=(), L_override=None, h_hint=None, dps: int = 20) -> float:
    """(1/2pi) int |Gamma(c+it)/L(1-2c-2it)|^2 dt. No zeros enter except as quadrature breakpoints (zeros_t:
    the t = -gamma/2 near which 1/L peaks, as mpf/str for precision; h_hint: peak half-width)."""
    Lf = L_override or hlr.L_of(chi)
    with mp.workdps(dps):
        c = mp.mpf(c)
        f = lambda t: abs(mp.gamma(mp.mpc(c, t)) / Lf(mp.mpc(1 - 2 * c, -2 * t))) ** 2
        pts = {mp.mpf(p) for p in np.arange(-t_max, t_max + 1e-9, 2.0).round(6).tolist()}
        if h_hint:
            h = mp.mpf(h_hint)
            for t0 in zeros_t:
                t0 = mp.mpf(t0)
                if abs(t0) < t_max - 1:
                    pts.add(t0)
                    k = h
                    while k < 0.5:                 # geometric breakpoints resolve the 1/((t-t0)^2 + h^2) peak
                        pts.update((t0 - k, t0 + k))
                        k *= 4
        pts = sorted(p for p in pts if -t_max <= p <= t_max)
        v = mp.quad(f, pts)
        return float(v / (2 * mp.pi))


# ------------------------------------------------------------------ Majorana holomorphic side
class Holo:
    """F_chi(w) = sum_{n<=N} mu chi(n) n/(1 - i n^2 w) + (i/w) sum_j (-i/w)^j T_{2j+1}(N), Im w > 0, |w| N^2 >> 1.
    Computed from the n-sum only (no zeros)."""

    def __init__(self, chi, N: int = 1000, J: int = 8):
        from .criteria import mobius_array
        mu = mobius_array(N).astype(float)
        n = np.arange(N + 1, dtype=float)
        if chi is None:
            cvec = mu.astype(complex)
        else:
            vals = np.array(chi.values, dtype=complex)
            cvec = mu * vals[np.arange(N + 1) % chi.q]
        self.cn = cvec[1:] * n[1:]
        self.n2 = n[1:] ** 2
        Lf = hlr.L_of(chi)
        self.T = []
        with mp.workdps(40):
            for j in range(J + 1):
                m = 2 * j + 1
                Linv = mp.mpc(hlr.inv_L1(chi)) if m == 1 else 1 / Lf(m)
                self.T.append(complex(Linv - mp.fsum(mp.mpc(cvec[k]) * mp.mpf(k) ** (-m) for k in range(1, N + 1) if mu[k])))

    def __call__(self, w):
        w = np.atleast_1d(np.asarray(w, dtype=complex))
        head = (self.cn[None, :] / (1 - 1j * self.n2[None, :] * w[:, None])).sum(axis=1)
        tail = np.zeros_like(w)
        r = -1j / w
        p = np.ones_like(w)
        for T in self.T:
            tail += p * T
            p = p * r
        return head + (1j / w) * tail


def hline_integral(F: Holo, v: float) -> float:
    """int_R |F(u + iv)|^2 du by adaptive quadrature (|F|^2 ~ |1/L(1)|^2/u^2 at infinity)."""
    g = lambda u: float(np.abs(F(u + 1j * v)[0]) ** 2)
    pts = [-200, -50, -10, -2, 0, 2, 10, 50, 200]
    tot = 0.0
    for a, b in zip(pts[:-1], pts[1:]):
        tot += integrate.quad(g, a, b, limit=400, epsabs=0, epsrel=1e-12)[0]
    for a, b in ((-np.inf, -200), (200, np.inf)):
        tot += integrate.quad(g, a, b, limit=400, epsabs=0, epsrel=1e-12)[0]
    return tot


def laplace_weighted(v: float, ser: hlr.Series, zexp: hlr.ZeroExpansion, X0: float) -> float:
    """int_0^oo |M(t)|^2 e^{-2vt} dt: series on [0, X0]; beyond, sum_{k,l} c_k conj(c_l) int_X0^oo t^(-S) e^{-2vt} dt
    = sum c_k conj(c_l) (2v)^(S-1) Gamma(1-S, 2v X0), S = s_k + conj s_l."""
    with mp.workdps(20):
        pts = [0, 1] + [p for p in (5, 15, 30) if p < X0] + [X0]
        head = mp.quad(lambda t: abs(ser(t)) ** 2 * mp.exp(-2 * v * t), pts)
        s, cc = _terms(zexp, X0, tol=1e-20)
        tail = mp.mpf(0)
        for k in range(len(s)):
            for l in range(len(s)):
                S = mp.mpc(s[k] + np.conj(s[l]))
                tail += mp.re(mp.mpc(cc[k] * np.conj(cc[l])) * (2 * v) ** (S - 1) * mp.gammainc(1 - S, 2 * v * X0))
    return float(head + tail)


# ------------------------------------------------------------------ model L with an off-line pair
def moved_zero_L(chi, gamma: float, beta: float):
    """L(w) R(w): the on-line zeros 1/2 +- i gamma (gamma of a real character) replaced by beta +- i gamma and
    1 - beta +- i gamma (functional-equation symmetric). A model only: it has no Euler product and no M."""
    Lf = hlr.L_of(chi)
    r1, r1b = mp.mpc(0.5, gamma), mp.mpc(0.5, -gamma)
    new = [mp.mpc(beta, gamma), mp.mpc(1 - beta, gamma), mp.mpc(beta, -gamma), mp.mpc(1 - beta, -gamma)]

    def L(w):
        num = 1
        for z in new:
            num *= (w - z)
        return Lf(w) * num / ((w - r1) ** 2 * (w - r1b) ** 2)
    return L


def visible_height(c: float, rel: float = 1e-16) -> float:
    """Largest gamma with |Gamma(c + i gamma/2)|^2 >= rel |Gamma(c)|^2: zeros above it cannot move a double-precision
    evaluation of the line norm (their weight is below rounding)."""
    ref = 2 * float(mp.re(mp.loggamma(c)))
    lo, hi = 0.0, 400.0
    for _ in range(60):
        mid = (lo + hi) / 2
        if 2 * float(mp.re(mp.loggamma(mp.mpc(c, mid / 2)))) - ref >= math.log(rel):
            lo = mid
        else:
            hi = mid
    return lo
