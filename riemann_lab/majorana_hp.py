"""Majorana's infinite-component tower as a Hilbert-Polya frame (numerical evidence, not proof).

Majorana's infinite-component equations live in unitary lowest-weight representations D+_k of SL(2, R)
(Bargmann index k: K0 = k + n on level n, rest masses m k/(k + n)). This module uses the *noncompact*
generator K1 = (K+ + K-)/2 instead of K0:

  * the spectral measure of K1 on the lowest state of D+_k is |Gamma(k + iE)|^2 dE (its Jacobi matrix in the
    level basis is the Meixner-Pollaczek recurrence), so a truncated Majorana tower gives Gauss nodes E_j and
    weights w_j for that measure;
  * the combined norm of `riemann_lab.combined` on the line Re z = c is
        (1/2pi) int |Gamma(c + iE) / L(1 - 2c - 2iE, chi)|^2 dE = <v0| |L(1 - 2c - 2i K1)|^-2 |v0>   in D+_c,
    approximated by the finite tower sum (1/2pi) sum_j w_j / |L(1 - 2c - 2i E_j)|^2;
  * at k = 1/4 the representation is the even sector of one harmonic oscillator, where K1, K2 are quadratic in
    a, a+ and D = (xp + px)/2 = -2 K2 (Berry-Keating's xp);
  * as k -> 1/4 the measure |Gamma/L|^2 dE develops Lorentzian peaks of width h = 1/4 - k at E = -gamma/2 for each
    zero 1/2 + i gamma of L(chi) (and +gamma/2 for zeros of L(chibar)); h mu_k tends to a point measure on the
    zeros with total mass B_chi, so the eigenvalues of the Jacobi matrix of mu_k lock onto the zeros.

The operator is built from L itself, and an off-line zero beta + i gamma shows up only in D+_k with
k = (1 - beta)/2. Nothing here excludes that; doing so is GRH.
"""
from __future__ import annotations

import math

import mpmath as mp
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigh_tridiagonal, expm

from . import hlr


# ------------------------------------------------------------------ 1. one oscillator = D+_{1/4} + D+_{3/4}
def oscillator(N: int) -> dict:
    """Truncated a, x, p and the su(1,1) generators K0 = (a+a + 1/2)/2, K+ = a+^2/2, K- = a^2/2, K1, K2."""
    a = np.diag(np.sqrt(np.arange(1, N, dtype=float)), 1)
    ad = a.T.copy()
    K0 = np.diag((np.arange(N) + 0.5) / 2)
    Kp, Km = ad @ ad / 2, a @ a / 2
    x = (a + ad) / math.sqrt(2)
    p = 1j * (ad - a) / math.sqrt(2)
    return {"a": a, "ad": ad, "K0": K0, "Kp": Kp, "Km": Km, "K1": (Kp + Km) / 2, "K2": (Kp - Km) / 2j,
            "x": x, "p": p, "D": (x @ p + p @ x) / 2}


def _com(A, B):
    return A @ B - B @ A


def oscillator_check(N: int) -> dict:
    o = oscillator(N)
    K0, Kp, Km = o["K0"], o["Kp"], o["Km"]
    k = N - 4                                        # interior block: away from the truncation edge
    e_alg = max(abs((_com(K0, Kp) - Kp)[:k, :k]).max(), abs((_com(K0, Km) + Km)[:k, :k]).max(),
                abs((_com(Kp, Km) + 2 * K0)[:k, :k]).max())
    cas = K0 @ K0 - K0 - Kp @ Km
    ev, od = np.arange(0, k, 2), np.arange(1, k, 2)
    e_cas_even = abs(cas[np.ix_(ev, ev)] - (-3 / 16) * np.eye(len(ev))).max()
    e_cas_odd = abs(cas[np.ix_(od, od)] - (-3 / 16) * np.eye(len(od))).max()
    from .majorana import sl2_matrices
    J0, Jp, _ = sl2_matrices(0.25, len(ev) - 1)
    e_ply = max(abs(K0[np.ix_(ev, ev)] - J0).max(), abs(Kp[np.ix_(ev, ev)] - Jp).max())
    e_D = abs((o["D"] + 2 * o["K2"])[:k, :k]).max()
    scale = max(abs(K0).max() ** 2, abs(Kp @ Km).max())     # products of entries ~ N^2/4: errors are relative to it
    e_alg, e_cas_even, e_cas_odd = e_alg / scale, e_cas_even / scale, e_cas_odd / scale
    return {"alg": float(e_alg), "cas_even": float(e_cas_even), "cas_odd": float(e_cas_odd),
            "plyushchay": float(e_ply), "D_vs_K2": float(e_D), "D": o["D"]}


def hermite_functions(m: int, x: np.ndarray) -> np.ndarray:
    """phi_0..phi_m on x (orthonormal Hermite functions, stable recurrence)."""
    out = np.zeros((m + 1, len(x)))
    out[0] = math.pi ** -0.25 * np.exp(-x * x / 2)
    if m >= 1:
        out[1] = math.sqrt(2) * x * out[0]
    for j in range(2, m + 1):
        out[j] = math.sqrt(2 / j) * x * out[j - 1] - math.sqrt((j - 1) / j) * out[j - 2]
    return out


def squeezed_coeffs_closed(n: float, m: int) -> np.ndarray:
    """<phi_2j | U(log n) phi0> for j <= m, U(l) f(x) = e^{-l/2} f(e^{-l} x): (cosh l)^{-1/2} tanh(l)^j sqrt((2j)!)/(2^j j!)."""
    lam = math.log(n)
    out = np.zeros(m + 1)
    c = 1 / math.sqrt(math.cosh(lam))
    for j in range(m + 1):
        out[j] = c * math.tanh(lam) ** j * math.exp(0.5 * math.lgamma(2 * j + 1) - j * math.log(2) - math.lgamma(j + 1))
    return out


def squeezed_coeffs_quad(n: float, m: int) -> np.ndarray:
    """Same coefficients by quadrature of the normalised Gaussian n^{-1/2} pi^{-1/4} e^{-x^2/(2 n^2)} against phi_2j
    (trapezoid on a wide grid: spectrally accurate for these smooth, fast-decaying integrands)."""
    X = 12 * n + 40
    M = 400001
    x = np.linspace(-X, X, M)
    g = n ** -0.5 * math.pi ** -0.25 * np.exp(-x * x / (2 * n * n))
    H = hermite_functions(2 * m, x)
    dx = 2 * X / (M - 1)                 # not x[1] - x[0]: that difference loses 1e-11 relative
    return (H[0::2] * g).sum(axis=1) * dx


def dilation_overlap_matrix(D: np.ndarray, lam: float) -> float:
    """<phi0, e^{-i lam D} phi0> from the truncated D (real: -i D is a real antisymmetric matrix)."""
    A = (-1j * lam * D).real
    return float(expm(A)[0, 0])


def dilation_overlap_fourier(lam: float, dps: int = 25) -> float:
    """int cos(lam E) |Gamma(1/4 + iE/2)|^2 dE / int |Gamma(1/4 + iE/2)|^2 dE (spectral side of D)."""
    with mp.workdps(dps):
        f = lambda E: abs(mp.gamma(mp.mpc(0.25, E / 2))) ** 2
        pts = [0, 2, 5, 10, 20, 40, 80, mp.inf]
        num = mp.quad(lambda E: mp.cos(lam * E) * f(E), pts)
        den = mp.quad(f, pts)
        return float(num / den)


# ------------------------------------------------------------------ 2. Majorana tower = Gauss rule for |Gamma(k+iE)|^2
def boost_matrix(k: float, n: int) -> np.ndarray:
    """K1 = (J+ + J-)/2 of D+_k on levels 0..n-1 (tridiagonal, off-diagonal sqrt(j (j + 2k - 1))/2)."""
    from .majorana import sl2_matrices
    _, Jp, Jm = sl2_matrices(k, n - 1)
    return (Jp + Jm) / 2


def tower_rule(k: float, n: int):
    """Eigenvalues E_j of the n-level K1 in D+_k and weights mu0 U_0j^2, mu0 = 2 pi Gamma(2k)/4^k."""
    j = np.arange(1, n, dtype=float)
    ev, U = eigh_tridiagonal(np.zeros(n), np.sqrt(j * (j + 2 * k - 1)) / 2)
    mu0 = 2 * math.pi * math.gamma(2 * k) / 4 ** k
    return ev, mu0 * U[0] ** 2


def gamma_moment(k: float, m: int, dps: int = 25) -> float:
    with mp.workdps(dps):
        f = lambda E: E ** (2 * m) * abs(mp.gamma(mp.mpc(k, E))) ** 2
        return float(2 * mp.quad(f, [0, 1, 3, 6, 10, 20, 40, 80, mp.inf]))


def gamma_charfun(k: float, lam: float) -> float:
    """int cos(lam E) |Gamma(k + iE)|^2 dE = 2 pi Gamma(2k) (2 cosh(lam/2))^(-2k)."""
    return 2 * math.pi * math.gamma(2 * k) * (2 * math.cosh(lam / 2)) ** (-2 * k)


# ------------------------------------------------------------------ 3. the combined norm as a finite tower sum
def tower_norm(chi, k: float, n: int, dps: int = 18, rel_cut: float = 1e-30) -> float:
    """(1/2pi) sum_j w_j / |L(1 - 2k - 2i E_j, chi)|^2 over the n-level tower (no zeros used)."""
    E, W = tower_rule(k, n)
    Lf = hlr.L_of(chi)
    keep = W > rel_cut * W.sum()
    tot = mp.mpf(0)
    with mp.workdps(dps):
        km = mp.mpf(k)
        for e, w in zip(E[keep], W[keep]):
            tot += w / abs(Lf(mp.mpc(1 - 2 * km, -2 * e))) ** 2
    return float(tot / (2 * mp.pi))


# ------------------------------------------------------------------ 4. point spectrum at k -> 1/4
def arithmetic_measure(chi, k, T: float, peaks, h: float, nodes: int = 24, dps: int = 20, L_override=None):
    """Discretisation (E_i, W_i) of |Gamma(k + iE)/L(1 - 2k - 2iE)|^2 dE/2pi on [-T, T]: Gauss-Legendre panels
    of `nodes` points between breakpoints every 0.5, refined geometrically (ratio 3) around each peak in `peaks`
    down to width h. Zeros enter only as breakpoints. k may be an mpf (k = 1/4 - h at full precision)."""
    Lf = L_override or hlr.L_of(chi)
    bps = set(np.arange(-T, T + 1e-9, 0.5).round(6).tolist())
    for t0 in peaks:
        if abs(t0) < T - 0.5:
            bps.add(float(t0))
            s = h
            while s < 0.25:
                bps.update((float(t0) - s, float(t0) + s))
                s *= 3
    bps = np.array(sorted(b for b in bps if -T <= b <= T))
    x, w = leggauss(nodes)
    E, W = [], []
    with mp.workdps(dps):
        km = mp.mpf(k)
        for a, b in zip(bps[:-1], bps[1:]):
            mid, half = (a + b) / 2, (b - a) / 2
            for xi, wi in zip(x, w):
                e = mid + half * xi
                f = abs(mp.gamma(mp.mpc(km, e)) / Lf(mp.mpc(1 - 2 * km, -2 * e))) ** 2
                E.append(e)
                W.append(float(f) * wi * half / (2 * math.pi))
    return np.array(E), np.array(W)


def lanczos_rule(E: np.ndarray, W: np.ndarray, n: int):
    """Gauss rule (nodes, weights) of size n for the discrete measure sum W_i delta_{E_i}: Lanczos on diag(E)
    from sqrt(W/sum W), full reorthogonalisation, then the eigen-decomposition of the n x n Jacobi matrix."""
    q = np.sqrt(W / W.sum())
    Q = [q]
    al, be = [], []
    prev, b = np.zeros_like(q), 0.0
    for _ in range(n):
        v = E * Q[-1] - b * prev
        a = v @ Q[-1]
        v = v - a * Q[-1]
        for _r in range(2):
            for qq in Q:
                v = v - (v @ qq) * qq
        al.append(a)
        b = float(np.linalg.norm(v))
        be.append(b)
        prev = Q[-1]
        Q.append(v / b)
    ev, U = eigh_tridiagonal(np.array(al), np.array(be[:-1]))
    return ev, W.sum() * U[0] ** 2


def point_mass_pred(chi, rho, L_override=None, dps: int = 30) -> float:
    """|Gamma((1 - rho)/2)|^2 / (8 |L'(rho)|^2): the limit of h x (mass of the peak at E = -Im(rho)/2) as k -> (1 - Re rho)/2."""
    with mp.workdps(dps):
        rho = mp.mpc(rho)
        if L_override is not None:
            Ld = mp.diff(L_override, rho)
        else:
            Ld = hlr.Ld_of(chi)(rho)
        return float(abs(mp.gamma((1 - rho) / 2)) ** 2 / (8 * abs(Ld) ** 2))


def locate(ev: np.ndarray, wt: np.ndarray, E0: float):
    j = int(np.argmin(abs(ev - E0)))
    return float(ev[j]), float(wt[j])


def tower_moment(k: float, m: int, n: int = 40) -> float:
    """mu0 <e0, K1^(2m) e0> on the n-level tower (exact for 2m < 2n)."""
    J = boost_matrix(k, n)
    v = np.zeros(n)
    v[0] = 1.0
    w = v.copy()
    for _ in range(m):
        w = J @ (J @ w)
    return 2 * math.pi * math.gamma(2 * k) / 4 ** k * float(v @ w)
