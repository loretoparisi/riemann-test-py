"""Ettore Majorana's mathematics, tested with the tools built for Masullo's GRH programme (and vice versa).

Eight topics, one per check in ``majorana_checks`` (criteria: docs/majorana_done_criteria.md):

1. Majorana's 1932 infinite-component equation: his two unitary infinite-dimensional representations of
   the Lorentz algebra, the mass tower M_s = m/(s + 1/2), the boosted spectrum and the tachyonic branch,
   and the tower's spectral zeta function (= 2 zeta(s - 1)).
2. The (2+1)-d Majorana equation (Plyushchay): the discrete series D+_alpha of SL(2, R) on weighted
   Bergman spaces of the disk. Cayley + Laplace + Mellin carry its norm to an L2 norm on the vertical line
   Re z = 1 - alpha: exactly the seminorms that define Masullo's Hardy-Sobolev spaces.
3. "Local RH" for that basis: the Mellin transform of every basis vector has all its zeros on Re z = 1 - alpha
   (Meixner-Pollaczek polynomials have real zeros).
4. Riemann's Xi expanded in the same basis (Meixner-Pollaczek series) and its zeros recovered from it.
5. Majorana's stellar representation applied to the Jensen polynomials of Xi (Griffin-Ono-Rolen-Zagier):
   hyperbolicity = all Majorana stars on one great circle.
6. Majorana fermions and random matrices: class D (Majorana BdG) and class C Hamiltonians against the
   low-lying zeros of the quadratic Dirichlet family (Katz-Sarnak symmetry types).
7. Majorana's 1928 semi-analytic solution of the Thomas-Fermi equation, checked by shooting and by its
   Mellin transform on the strip 0 < Re s < 3.
8. Majorana algebras (Ivanov; Castillo-Ramirez's thesis): the Norton-Sakuma algebras, in exact rational
   arithmetic, and the moonshine numbers around the Griess algebra (Rademacher's Kloosterman series, Weil's
   bound).

Everything is floating point or exact rational arithmetic on finite truncations: evidence, not proof.
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr
from functools import lru_cache

import mpmath as mp
import numpy as np


# ====================================================================== 1. Majorana's tower
def _lorentz_basis(j0: float, J: float):
    st, j = [], j0
    while j <= J + 1e-9:
        m = -j
        while m <= j + 1e-9:
            st.append((j, m))
            m += 1
        j += 1
    return st


def lorentz_generators(j0: float, c: float, J: float):
    """Gel'fand-Naimark matrices of the Lorentz representation (j0, c), truncated at j <= J.

    Majorana (1932) found the two unitary ones used by his equation: (j0, c) = (0, 1/2) (integer spins) and
    (1/2, 0) (half-integer spins); for them A_j = 0 and C_j = i/2, so the boost matrix elements are the
    (1/2) sqrt(...) entries printed in Esposito's account (EJTP 3(10), eq. 40). Returns (states, H, F) with
    H = (H1, H2, H3) rotations and F = (F1, F2, F3) boosts.
    """
    st = _lorentz_basis(j0, J)
    idx = {s: i for i, s in enumerate(st)}
    n = len(st)
    Hp, Hm, H3 = (np.zeros((n, n), complex) for _ in range(3))
    Fp, Fm, F3 = (np.zeros((n, n), complex) for _ in range(3))

    def C(j):
        return 0 if j <= 0 else 1j / j * np.sqrt(complex((j * j - j0 * j0) * (j * j - c * c) / (4 * j * j - 1)))

    def A(j):
        return 1j * j0 * c / (j * (j + 1)) if j > 0 else 0

    for (j, m), i in idx.items():
        H3[i, i] = m
        if (j, m + 1) in idx:
            Hp[idx[(j, m + 1)], i] = np.sqrt((j + m + 1) * (j - m))
        if (j, m - 1) in idx:
            Hm[idx[(j, m - 1)], i] = np.sqrt((j + m) * (j - m + 1))
        if (j - 1, m) in idx:
            F3[idx[(j - 1, m)], i] += C(j) * np.sqrt(j * j - m * m)
        F3[i, i] += -A(j) * m
        if (j + 1, m) in idx:
            F3[idx[(j + 1, m)], i] += -C(j + 1) * np.sqrt((j + 1) ** 2 - m * m)
        if (j - 1, m + 1) in idx:
            Fp[idx[(j - 1, m + 1)], i] += C(j) * np.sqrt((j - m) * (j - m - 1))
        if (j, m + 1) in idx:
            Fp[idx[(j, m + 1)], i] += -A(j) * np.sqrt((j - m) * (j + m + 1))
        if (j + 1, m + 1) in idx:
            Fp[idx[(j + 1, m + 1)], i] += C(j + 1) * np.sqrt((j + m + 1) * (j + m + 2))
        if (j - 1, m - 1) in idx:
            Fm[idx[(j - 1, m - 1)], i] += -C(j) * np.sqrt((j + m) * (j + m - 1))
        if (j, m - 1) in idx:
            Fm[idx[(j, m - 1)], i] += -A(j) * np.sqrt((j + m) * (j - m + 1))
        if (j + 1, m - 1) in idx:
            Fm[idx[(j + 1, m - 1)], i] += -C(j + 1) * np.sqrt((j - m + 1) * (j - m + 2))
    H = [(Hp + Hm) / 2, (Hp - Hm) / 2j, H3]
    F = [(Fp + Fm) / 2, (Fp - Fm) / 2j, F3]
    return st, H, F


def _com(a, b):
    return a @ b - b @ a


def tower_check(j0: float, J_algebra: float, J_spectrum: float, p: float = 0.7, m: float = 1.0) -> dict:
    """Algebra and covariance of Majorana's equation (Gamma^mu p_mu - m) psi = 0 on the representation
    (j0, c = 1/2 - j0) truncated at J_algebra (dense matrices), and its spectrum in the helicity sector
    m_z = j0 truncated at J_spectrum (the sector is invariant under H3, F3, Gamma0, Gamma3)."""
    c = 0.5 - j0
    st, H, F = lorentz_generators(j0, c, J_algebra)
    inner = np.array([s[0] <= J_algebra - 1 + 1e-9 for s in st])

    def err(M):
        return float(abs(M[np.ix_(inner, inner)]).max())

    cyc = [(0, 1, 2), (1, 2, 0), (2, 0, 1)]
    algebra = max(max(err(_com(H[i], H[j]) - 1j * H[k]) for i, j, k in cyc),
                  max(err(_com(H[i], F[j]) - 1j * F[k]) for i, j, k in cyc),
                  max(err(_com(F[i], F[j]) + 1j * H[k]) for i, j, k in cyc))
    hermitian = max(float(abs(M - M.conj().T).max()) for M in H + F)
    G0 = np.diag([s[0] + 0.5 for s in st]).astype(complex)
    G = [1j * _com(F[k], G0) for k in range(3)]
    vector = max(max(err(_com(H[i], G[j]) - 1j * G[k]) for i, j, k in cyc),
                 max(err(_com(F[a], G[b]) + (1j * G0 if a == b else 0)) for a in range(3) for b in range(3)))
    # helicity sector m_z = j0: F3 is tridiagonal there, Gamma3_ab = i F3_ab (g_b - g_a)
    js = np.arange(j0, J_spectrum + 1e-9, 1.0)
    g0 = js + 0.5
    n = len(js)
    G3 = np.zeros((n, n), complex)
    for k in range(1, n):
        j = js[k]
        f = 1j / 2 * math.sqrt(j * j - j0 * j0)            # <j-1, m|F3|j, m> = C_j sqrt(j^2 - m^2), C_j = i/2
        G3[k - 1, k] = 1j * f * (g0[k] - g0[k - 1])
        G3[k, k - 1] = np.conj(G3[k - 1, k])
    D = np.diag(1 / np.sqrt(g0))
    E = np.sort(np.linalg.eigvalsh(D @ (m * np.eye(n) + p * G3) @ D))
    expected = np.array([math.sqrt((m / (js[k] + 0.5)) ** 2 + p * p) for k in range(4)])
    rest = np.sort(m / np.diag(G0).real)[::-1]
    rest = np.unique(np.round(rest, 14))[::-1][:4]
    return {"states": len(st), "algebra_err": algebra, "hermitian_err": hermitian, "vector_err": vector,
            "rest_masses": rest, "rest_expected": np.array([m / (j0 + k + 0.5) for k in range(4)]),
            "top_energies": E[::-1][:4], "expected_energies": expected,
            "negative": E[E < 0], "p": p}


def tower_spectral_zeta(s, half_integer: bool):
    """Sum over all states of Majorana's tower of (M/m)^s, each spin-j level counted 2j+1 times."""
    j0 = mp.mpf(0.5) if half_integer else mp.mpf(0)
    f = lambda k: (2 * (j0 + k) + 1) * (j0 + k + mp.mpf(0.5)) ** (-s)
    head = mp.fsum(f(k) for k in range(2000))
    return head + mp.sumem(f, [2000, mp.inf])           # Euler-Maclaurin tail


def tower_spectral_zeta_closed(s, half_integer: bool):
    return 2 * mp.zeta(s - 1) if half_integer else 2 * (2 ** (s - 1) - 1) * mp.zeta(s - 1)


# ====================================================================== 2. discrete series and Hardy-Sobolev
def sl2_matrices(alpha: float, nmax: int):
    """D+_alpha of SL(2, R) in Plyushchay's basis chi_n (eq. 7): J0 chi_n = (alpha + n) chi_n,
    J+ chi_n = sqrt((n+1)(n+2 alpha)) chi_(n+1), J- = J+^T."""
    n = np.arange(nmax + 1)
    J0 = np.diag(alpha + n).astype(float)
    Jp = np.zeros((nmax + 1, nmax + 1))
    for k in range(nmax):
        Jp[k + 1, k] = math.sqrt((k + 1) * (k + 2 * alpha))
    return J0, Jp, Jp.T.copy()


def sl2_check(alpha: float, nmax: int = 40, m: float = 1.0) -> dict:
    J0, Jp, Jm = sl2_matrices(alpha, nmax)
    k = nmax - 1                      # interior block
    e1 = abs((_com(J0, Jp) - Jp)[:k, :k]).max()
    e2 = abs((_com(J0, Jm) + Jm)[:k, :k]).max()
    e3 = abs((_com(Jp, Jm) + 2 * J0)[:k, :k]).max()
    cas = J0 @ J0 - J0 - Jp @ Jm          # = alpha(alpha - 1) on D+_alpha
    e4 = abs((cas - alpha * (alpha - 1) * np.eye(nmax + 1))[:k, :k]).max()
    masses = m * alpha / np.diag(J0)[:5]   # rest frame of (P.J - alpha m) Psi = 0
    # differential realization J0 = z d/dz + alpha on z^n
    diff = max(abs((nn + alpha) - (alpha + nn)) for nn in range(nmax + 1))
    # J+ = z^2 d/dz + 2 alpha z (Plyushchay eq. 4 up to the normalisation of chi_n)
    nrm = [math.sqrt(math.gamma(2 * alpha + nn) / (math.gamma(nn + 1) * math.gamma(2 * alpha))) for nn in range(nmax + 1)]
    jp_diff = max(abs((nn + 2 * alpha) * nrm[nn] / nrm[nn + 1] - Jp[nn + 1, nn]) for nn in range(nmax))
    return {"comm_err": float(max(e1, e2, e3)), "casimir_err": float(e4), "masses": masses,
            "masses_expected": np.array([m * alpha / (alpha + nn) for nn in range(5)]),
            "diff_realization_err": float(max(diff, jp_diff))}


def laguerre_mellin(n: int, beta, s):
    """Int_0^oo t^(s-1) t^beta e^-t L_n^(beta)(2t) dt = sum_k (-1)^k C(n+beta, n-k) 2^k/k! Gamma(s+beta+k)."""
    return mp.gamma(s + beta) * laguerre_mellin_poly(n, beta, s)


def laguerre_mellin_poly(n: int, beta, s):
    tot, poch = mp.mpf(0), mp.mpf(1)
    for k in range(n + 1):
        tot += (-1) ** k * mp.binomial(n + beta, n - k) * mp.mpf(2) ** k / mp.factorial(k) * poch
        poch *= (s + beta + k)
    return tot


def laguerre_mellin_poly_coeffs(n: int, beta) -> list:
    """Coefficients (highest degree first) of Q_n(s) = laguerre_mellin_poly(n, beta, s) as a polynomial in s."""
    total = [mp.mpf(0)] * (n + 1)          # lowest degree first
    poch = [mp.mpf(1)]
    for k in range(n + 1):
        w = (-1) ** k * mp.binomial(n + beta, n - k) * mp.mpf(2) ** k / mp.factorial(k)
        for i, cf in enumerate(poch):
            total[i] += w * cf
        new = [mp.mpf(0)] * (len(poch) + 1)       # poch *= (s + beta + k)
        for i, cf in enumerate(poch):
            new[i] += cf * (beta + k)
            new[i + 1] += cf
        poch = new
    return total[::-1]


def laguerre_all(nmax: int, beta, x) -> list:
    """L_0^(beta)(x), ..., L_nmax^(beta)(x) by the three-term recurrence."""
    L = [mp.mpf(1), 1 + beta - x]
    for k in range(1, nmax):
        L.append(((2 * k + 1 + beta - x) * L[k] - (k + beta) * L[k - 1]) / (k + 1))
    return L[:nmax + 1]


def basis_F(n: int, alpha, t):
    beta = 2 * alpha - 1
    return t ** beta * mp.exp(-t) * laguerre_all(n, beta, 2 * t)[n]


def basis_combo(c, alpha, t):
    beta = 2 * alpha - 1
    L = laguerre_all(len(c) - 1, beta, 2 * t)
    return t ** beta * mp.exp(-t) * sum(ci * li for ci, li in zip(c, L))


def hardy_sobolev_chain(alpha: float, coeffs, dps: int = 25) -> dict:
    """Four computations of the norm of f = sum c_n (basis vector n) in D+_alpha (alpha > 1/2), or in the
    Hardy space for alpha = 1/2:

    * coefficients: sum |c_n|^2 Gamma(n + 2 alpha)/(n! 2^(2 alpha));
    * Laplace side: Int_0^oo |F(t)|^2 t^(1 - 2 alpha) dt  (F = sum c_n F_n);
    * Mellin side: (1/2 pi) Int |M F(1 - alpha + i tau)|^2 d tau (Masullo's seminorm on the line Re z = 1 - alpha);
    * disk side: 4 Int_D |g|^2 (1 - |z|^2)^(2 alpha - 2) d^2z / (2 pi Gamma(2 alpha - 1) 2^(1 - 2 alpha)), where
      g(z) = f(w(z)) (1 - z)^(-2 alpha) under the Cayley map; g = sum c_n Gamma(n + 2a)/(n! 2^(2a)) z^n, i.e. the
      Majorana-Plyushchay basis chi_n ~ z^n. For alpha = 1/2: 2 x the mean of |g|^2 on the circle.
    """
    with mp.workdps(dps):
        a = mp.mpf(alpha)
        beta = 2 * a - 1
        c = [mp.mpf(x) for x in coeffs]
        N = len(c) - 1
        coef = sum(c[n] ** 2 * mp.gamma(n + 2 * a) / (mp.factorial(n) * 2 ** (2 * a)) for n in range(N + 1))

        def F(t):
            return basis_combo(c, a, t)
        lap = mp.quad(lambda t: F(t) ** 2 * t ** (1 - 2 * a), [0, 1, 5, 15, 40, mp.inf])

        def M(tau):
            s = 1 - a + 1j * tau
            return sum(c[n] * laguerre_mellin(n, beta, s) for n in range(N + 1))
        mel = mp.quad(lambda tau: abs(M(tau)) ** 2, [-mp.inf, -20, -5, 0, 5, 20, mp.inf]) / (2 * mp.pi)
        b = [c[n] * mp.gamma(n + 2 * a) / (mp.factorial(n) * 2 ** (2 * a)) for n in range(N + 1)]
        K = 4 * (N + 1)                                    # trapezoid in theta: exact for |g|^2, degree <= 2N
        th = [2 * mp.pi * k / K for k in range(K)]

        def ang(r):
            return sum(abs(sum(b[n] * (r * mp.expj(t)) ** n for n in range(N + 1))) ** 2 for t in th) / K * 2 * mp.pi
        if alpha == 0.5:
            disk = 2 * ang(mp.mpf(1)) / (2 * mp.pi)
        else:
            # u = 1 - r^2 = v^(1/(2a-1)) removes the endpoint singularity: Int ang (1-r^2)^(2a-2) r dr
            # = 1/(2(2a-1)) Int_0^1 ang(sqrt(1 - v^(1/(2a-1)))) dv
            e = 1 / (2 * a - 1)
            raw = mp.quad(lambda v: ang(mp.sqrt(1 - v ** e)), [0, 0.5, 1]) / (2 * (2 * a - 1))
            disk = 4 * raw / (2 * mp.pi * mp.gamma(2 * a - 1) * 2 ** (1 - 2 * a))
        return {"coefficients": coef, "laplace": lap, "mellin": mel, "disk": disk}


def plyushchay_orthonormal(alpha: float, nmax: int = 6) -> float:
    """Max deviation from orthonormality of chi_n = sqrt(Gamma(2a+n)/(n! Gamma(2a))) z^n under the measure
    (2a - 1)/pi (1 - |z|^2)^(2a - 2) d^2z (Plyushchay eqs. 6-7), radial integral by quadrature."""
    a = mp.mpf(alpha)
    worst = 0
    for n in range(nmax + 1):
        nrm = mp.gamma(2 * a + n) / (mp.factorial(n) * mp.gamma(2 * a))
        e = 1 / (2 * a - 1)          # Int_0^1 r^(2n+1) (1-r^2)^(2a-2) dr with u = 1 - r^2 = v^e
        val = (2 * a - 1) * 2 * mp.quad(lambda v: (1 - v ** e) ** n, [0, 0.5, 1]) / (2 * (2 * a - 1))
        worst = max(worst, abs(nrm * val - 1))
    return float(worst)


def masullo_two_line_norm(coeffs, alpha_basis: float, a: float, b: float, dps: int = 20) -> dict:
    """Masullo's s = 0 Hardy-Sobolev norm on G = R>0 with base I = [a, b]:
    Int |phi(t)|^2 max(t^(2a), t^(2b)) dt/t, against the two single-line (discrete-series) norms
    Int |phi|^2 t^(2 sigma) dt/t = (1/2pi) Int |M phi(sigma + i tau)|^2 d tau, sigma = a, b."""
    with mp.workdps(dps):
        al = mp.mpf(alpha_basis)
        c = [mp.mpf(x) for x in coeffs]

        def F(t):
            return basis_combo(c, al, t)
        pts = [0, 1, 5, 15, 40, mp.inf]
        hs = mp.quad(lambda t: F(t) ** 2 * max(t ** (2 * a), t ** (2 * b)) / t, pts)
        line = {}
        for sig in (a, b):
            x_side = mp.quad(lambda t: F(t) ** 2 * t ** (2 * sig) / t, pts)
            m_side = mp.quad(lambda tau: abs(sum(c[n] * laguerre_mellin(n, 2 * al - 1, sig + 1j * tau)
                                                 for n in range(len(c)))) ** 2,
                             [-mp.inf, -10, 0, 10, mp.inf]) / (2 * mp.pi)
            line[sig] = (x_side, m_side)
        return {"hardy_sobolev": hs, "lines": line}


# ====================================================================== 3. local RH for the basis
def local_rh(alpha, n: int, dps: int = 50) -> dict:
    """Zeros of Q_n(s) (Mellin transform of basis vector n divided by Gamma) and their real parts."""
    with mp.workdps(dps):
        a = mp.mpf(alpha)
        cf = laguerre_mellin_poly_coeffs(n, 2 * a - 1)
        if n == 0:
            return {"n": 0, "max_dev": 0.0, "roots": []}
        roots = mp.polyroots(cf, maxsteps=400, extraprec=4 * dps)
        dev = max(abs(mp.re(r) - (1 - a)) for r in roots)
        return {"n": n, "max_dev": dev, "roots": roots}


def line_sign_changes(alpha, n: int, grid: int, dps: int = 30) -> dict:
    """i^-n Q_n(1 - alpha + i tau) is real; count its sign changes on [-T, T] covering all zeros."""
    with mp.workdps(dps):
        a = mp.mpf(alpha)
        beta = 2 * a - 1
        T = 2 * math.sqrt(n + 2 * float(a)) * math.sqrt(n + 1) + 5
        taus = [-T + 2 * T * k / grid for k in range(grid + 1)]
        vals = [laguerre_mellin_poly(n, beta, 1 - a + 1j * t) / mp.mpc(0, 1) ** n for t in taus]
        imag = max(abs(mp.im(v)) / (abs(v) + mp.mpf(10) ** (-dps // 2)) for v in vals)
        re = [mp.re(v) for v in vals]
        changes = sum(1 for x, y in zip(re[:-1], re[1:]) if x * y < 0)
        return {"sign_changes": changes, "max_rel_imag": float(imag)}


def mellin_quadrature_vs_closed(alpha, n: int, points, dps: int = 25) -> float:
    with mp.workdps(dps):
        a = mp.mpf(alpha)
        worst = 0
        for s in points:
            s = mp.mpc(s)
            # t in (0, 1] as t = e^-u: t^(s-1) oscillates infinitely often at t = 0 when Im s != 0
            q = mp.quad(lambda u: mp.exp(-u * s) * basis_F(n, a, mp.exp(-u)), [0, 5, 20, 60, 200, mp.inf]) + \
                mp.quad(lambda t: t ** (s - 1) * basis_F(n, a, t), [1, 5, 15, 40, mp.inf])
            cl = laguerre_mellin(n, 2 * a - 1, s)
            worst = max(worst, abs(q - cl) / abs(cl))
        return float(worst)


def line_orthonormality(alpha, pairs, dps: int = 20) -> float:
    """(1/2pi) Int M F_n conj(M F_m) on Re s = 1 - alpha, divided by Gamma(n + 2a)/(n! 2^(2a)): delta_nm."""
    with mp.workdps(dps):
        a = mp.mpf(alpha)
        beta = 2 * a - 1
        worst = 0
        for n, m in pairs:
            v = mp.quad(lambda t: laguerre_mellin(n, beta, 1 - a + 1j * t) * mp.conj(laguerre_mellin(m, beta, 1 - a + 1j * t)),
                        [-mp.inf, -20, -5, 0, 5, 20, mp.inf]) / (2 * mp.pi)
            nrm = mp.gamma(n + 2 * a) / (mp.factorial(n) * 2 ** (2 * a))
            worst = max(worst, abs(v / nrm - (1 if n == m else 0)))
        return float(worst)


def mixed_control(alpha, n: int, m: int, dps: int = 40) -> float:
    """F_n^(alpha) + F_m^(alpha + 1/2): Mellin = Gamma(s + 2a - 1) [Q_n^a(s) + (s + 2a - 1) Q_m^(a+1/2)(s)].
    Returns the spread max Re z - min Re z of its zeros (no common vertical line if > 0)."""
    with mp.workdps(dps):
        a = mp.mpf(alpha)
        p1 = laguerre_mellin_poly_coeffs(n, 2 * a - 1)[::-1]
        q = laguerre_mellin_poly_coeffs(m, 2 * a)[::-1]
        p2 = [mp.mpf(0)] * (len(q) + 1)
        for i, cf in enumerate(q):               # (s + 2a - 1) q(s)
            p2[i] += cf * (2 * a - 1)
            p2[i + 1] += cf
        L = max(len(p1), len(p2))
        tot = [(p1[i] if i < len(p1) else 0) + (p2[i] if i < len(p2) else 0) for i in range(L)]
        roots = mp.polyroots(tot[::-1], maxsteps=400, extraprec=4 * dps)
        re = [mp.re(r) for r in roots]
        return float(max(re) - min(re))


# ====================================================================== 4. Xi in the discrete-series basis
def xi(s):
    return s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def mp_poly_values(lam, nmax: int, x):
    """Meixner-Pollaczek P_n^(lam)(x; pi/2), n <= nmax: (n+1) P_(n+1) = 2x P_n - (n + 2 lam - 1) P_(n-1)."""
    p = [mp.mpf(1), 2 * x]
    for n in range(1, nmax):
        p.append((2 * x * p[n] - (n + 2 * lam - 1) * p[n - 1]) / (n + 1))
    return p[:nmax + 1]


def mp_poly_norm(lam, n: int):
    """Int P_n^2 |Gamma(lam + ix)|^2 dx = 2 pi Gamma(n + 2 lam)/(2^(2 lam) n!)."""
    return 2 * mp.pi * mp.gamma(n + 2 * lam) / (2 ** (2 * lam) * mp.factorial(n))


def xi_mp_coefficients(lam, nmax: int, dps: int, X: float = 40.0, per_unit: int = 4, nodes: int = 30) -> list:
    """a_n with Xi(2x) = sum a_n P_n^(lam)(x; pi/2): a_n = Int Xi(2x) P_n |Gamma(lam+ix)|^2 dx / h_n,
    composite Gauss-Legendre on [0, X] (Xi(2x) |Gamma|^2 ~ e^(-3 pi x/2)), using evenness."""
    with mp.workdps(dps):
        lam = mp.mpf(lam)
        xg, wg = np.polynomial.legendre.leggauss(nodes)
        a = [mp.mpf(0)] * (nmax + 1)
        seg = int(X * per_unit)
        for k in range(seg):
            lo, hi = mp.mpf(X) * k / seg, mp.mpf(X) * (k + 1) / seg
            for xx, w in zip(xg, wg):
                x = lo + (hi - lo) * (mp.mpf(float(xx)) + 1) / 2
                g = mp.re(xi(mp.mpf(0.5) + 2j * x)) * abs(mp.gamma(lam + 1j * x)) ** 2 * (hi - lo) / 2 * mp.mpf(float(w))
                pp = mp_poly_values(lam, nmax, x)
                for n in range(0, nmax + 1, 2):
                    a[n] += 2 * g * pp[n]
        return [a[n] / mp_poly_norm(lam, n) for n in range(nmax + 1)]


def xi_mp_partial(a, lam, N: int, x):
    pp = mp_poly_values(mp.mpf(lam), N, x)
    return sum(a[n] * pp[n] for n in range(0, N + 1, 2))


def xi_mp_zeros(a, lam, N: int, k: int, dps: int) -> list:
    """Real roots of S_N(x) near gamma_j/2, j <= k, returned as ordinates gamma = 2x."""
    with mp.workdps(dps):
        out = []
        for j in range(1, k + 1):
            g = mp.zetazero(j).imag
            try:
                out.append(2 * mp.findroot(lambda x: xi_mp_partial(a, lam, N, x), g / 2))
            except (ValueError, ZeroDivisionError):
                out.append(mp.nan)
        return out


# ====================================================================== 5. Majorana stars of Jensen polynomials
def riemann_Phi(u):
    tot = mp.mpf(0)
    for n in range(1, 30):
        term = (2 * mp.pi ** 2 * n ** 4 * mp.exp(9 * u / 2) - 3 * mp.pi * n ** 2 * mp.exp(5 * u / 2)) * mp.exp(-mp.pi * n * n * mp.exp(2 * u))
        tot += term
        if abs(term) < mp.mpf(10) ** (-mp.mp.dps - 10):
            break
    return tot


def xi_taylor_beta(kmax: int, dps: int = 60) -> list:
    """beta_k > 0 with xi(1/2 + z) = sum beta_k z^(2k): Xi(t) = 4 Int_0^oo Phi(u) cos(ut) du for the Phi
    below (Polya's kernel is 2 Phi), so beta_k = 4 Int_0^oo Phi(u) u^(2k) du/(2k)!."""
    with mp.workdps(dps):
        return [4 * mp.quad(lambda u: riemann_Phi(u) * u ** (2 * k), [0, 0.25, 0.5, 1, 1.5, 2, 3]) / mp.factorial(2 * k)
                for k in range(kmax + 1)]


def gorz_gamma(beta) -> list:
    """Griffin-Ono-Rolen-Zagier: (-1 + 4z^2) Lambda(1/2 + z) = 8 xi(1/2 + z) = sum gamma(n) z^(2n)/n!."""
    return [8 * mp.factorial(k) * b for k, b in enumerate(beta)]


def jensen_coeffs(gam, d: int, n: int) -> list:
    """J^(d,n)(X) = sum_j C(d, j) gamma(n + j) X^j, lowest degree first."""
    return [mp.binomial(d, j) * gam[n + j] for j in range(d + 1)]


def _to_fraction(x, digits: int = 50) -> Fr:
    s = mp.nstr(x, digits, min_fixed=-10**9, max_fixed=10**9)
    return Fr(s)


def sturm_real_roots(coeffs_low_first) -> int:
    """Number of distinct real roots, exactly (Sturm's theorem over Q)."""
    p = [_to_fraction(c) if not isinstance(c, Fr) else c for c in coeffs_low_first]

    def trim(a):
        while a and a[-1] == 0:
            a = a[:-1]
        return a

    def deriv(a):
        return [i * a[i] for i in range(1, len(a))]

    def rem(a, b):
        a = a[:]
        while len(a) >= len(b) and a:
            f = a[-1] / b[-1]
            sh = len(a) - len(b)
            for i in range(len(b)):
                a[sh + i] -= f * b[i]
            a = trim(a[:-1]) if a[-1] == 0 else trim(a)
        return a

    seq = [trim(p), trim(deriv(p))]
    while True:
        r = rem(seq[-2], seq[-1])
        if not r:
            break
        seq.append([-x for x in r])

    def changes(signs):
        s = [x for x in signs if x != 0]
        return sum(1 for a, b in zip(s[:-1], s[1:]) if a * b < 0)
    at_minus = [(-1) ** (len(q) - 1) * (1 if q[-1] > 0 else -1) for q in seq]
    at_plus = [(1 if q[-1] > 0 else -1) for q in seq]
    return changes(at_minus) - changes(at_plus)


def majorana_stars(coeffs_low_first, dps: int = 60) -> np.ndarray:
    """Majorana's stellar representation: the spin-d/2 state with amplitudes c_k (|s, s-k>) has Majorana
    polynomial sum_k c_k C(d, k)^(1/2) z^(d-k); with c_k = C(d,k)^(1/2) gamma(n+d-k) that is J^(d,n)(z).
    Its roots, stereographically projected, are the stars (X, Y, Z) on the unit sphere."""
    with mp.workdps(dps):
        roots = mp.polyroots(list(coeffs_low_first)[::-1], maxsteps=500, extraprec=3 * dps)
        out = []
        for w in roots:
            r2 = abs(w) ** 2
            out.append((float(2 * mp.re(w) / (1 + r2)), float(2 * mp.im(w) / (1 + r2)), float((r2 - 1) / (r2 + 1))))
        return np.array(out)


def perturbed_beta(beta, a: float, b: float) -> list:
    """Coefficients (in t^2, same convention as beta) of Xi(t) (t^2 - c)(t^2 - conj c)/|c|^2, c = (a + ib)^2:
    Xi with an extra quadruple of zeros t = +-a +- ib, i.e. s = 1/2 -+ b + i(+-a), off the critical line.
    (A pair at t = +-ib alone would NOT do: it is a real zero w = b^2 of F(w), w = -t^2, and Jensen
    hyperbolicity only sees non-real w.)"""
    c = mp.mpc(a, b) ** 2
    c2, rc = abs(c) ** 2, mp.re(c)
    out = []
    for k in range(len(beta)):
        v = c2 * beta[k]
        if k >= 1:
            v += 2 * rc * beta[k - 1]
        if k >= 2:
            v += beta[k - 2]
        out.append(v / c2)
    return out


# ====================================================================== 6. Majorana random matrices and quadratic L
def bdg_samples(cls: str, N: int, samples: int, seed: int = 1) -> np.ndarray:
    """Smallest positive eigenvalues of 2N x 2N Bogoliubov-de Gennes Hamiltonians H = [[h, D], [-conj(D)?, -h^T]]:
    class D (D antisymmetric; equivalently H = iA with A real antisymmetric in the Majorana basis) or
    class C (D symmetric). Returned unfolded by the semicircle density at 0, rho(0) = 2M/(pi R)."""
    rng = np.random.default_rng(seed)
    out = []
    M = 2 * N
    R = 2 * math.sqrt(M)                 # all entries have E|H_ij|^2 = 1 -> semicircle radius 2 sqrt(M)
    rho0 = 2 * M / (math.pi * R)
    batch = 500
    done = 0
    while done < samples:
        k = min(batch, samples - done)
        g = (rng.standard_normal((k, N, N)) + 1j * rng.standard_normal((k, N, N))) / math.sqrt(2)
        h = (g + np.conj(np.swapaxes(g, 1, 2))) / math.sqrt(2)
        d = (rng.standard_normal((k, N, N)) + 1j * rng.standard_normal((k, N, N))) / math.sqrt(2)
        if cls == "D":
            d = (d - np.swapaxes(d, 1, 2)) / math.sqrt(2)
            lower = -np.conj(d)
        else:
            d = (d + np.swapaxes(d, 1, 2)) / math.sqrt(2)
            lower = np.conj(d)
        H = np.block([[h, d], [lower, -np.conj(h)]])
        ev = np.linalg.eigvalsh(H)
        pos = ev[:, N:]                  # spectrum is symmetric: +-E
        out.append(pos * rho0)
        done += k
    return np.concatenate(out)


def bdg_particle_hole_err(cls: str, N: int = 6) -> float:
    """Check the symmetry: class D, U H^* U^-1 = -H with U = sigma_x (C^2 = +1); class C, sigma_y (C^2 = -1)."""
    rng = np.random.default_rng(0)
    g = (rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N)))
    h = g + g.conj().T
    d = rng.standard_normal((N, N)) + 1j * rng.standard_normal((N, N))
    if cls == "D":
        d = d - d.T
        H = np.block([[h, d], [-d.conj(), -h.conj()]])
        U = np.block([[np.zeros((N, N)), np.eye(N)], [np.eye(N), np.zeros((N, N))]])
    else:
        d = d + d.T
        H = np.block([[h, d], [d.conj(), -h.conj()]])
        U = np.block([[np.zeros((N, N)), -np.eye(N)], [np.eye(N), np.zeros((N, N))]])
    return float(abs(U @ H.conj() @ np.linalg.inv(U) + H).max() + abs(H - H.conj().T).max())


def W_usp(x):
    x = np.asarray(x, float)
    return 1 - np.sinc(2 * x)          # np.sinc(y) = sin(pi y)/(pi y)


def W_so_even(x):
    return 1 + np.sinc(2 * np.asarray(x, float))


def jacobi_symbol(a: int, n: int) -> int:
    a %= n
    r = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                r = -r
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            r = -r
        a %= n
    return r if n == 1 else 0


def kronecker(d: int, n: int) -> int:
    if n == 0:
        return 1 if abs(d) == 1 else 0
    r = 1
    while n % 2 == 0:
        n //= 2
        if d % 2 == 0:
            return 0
        r *= 1 if d % 8 in (1, 7) else -1
    return r * jacobi_symbol(d, n) if n > 1 else r


def is_fundamental(d: int) -> bool:
    def squarefree(m):
        m = abs(m)
        k = 2
        while k * k <= m:
            if m % (k * k) == 0:
                return False
            k += 1
        return True
    if d % 4 == 1:
        return squarefree(d)
    if d % 4 == 0:
        m = d // 4
        return m % 4 in (2, 3) and squarefree(m)
    return False


class QuadraticL:
    """Lambda(1/2 + it, chi_d) for a fundamental discriminant d by the theta integral
    Lambda(s) = Int_1^oo theta(x) (x^((s+a)/2) + x^((1-s+a)/2)) dx/x, theta(x) = sum chi_d(n) n^a e^(-pi n^2 x/q)
    (root number 1 for real characters), Gauss-Legendre in u = log x. Z(t) is Lambda divided by
    |Gamma((1/2 + it + a)/2)| (q/pi)^((1/2 + a)/2): the Hardy-type Z_chi."""

    def __init__(self, d: int, nodes: int = 400):
        self.d, self.q = d, abs(d)
        self.a = 0 if d > 0 else 1
        q = self.q
        nmax = int(math.sqrt(45 * q / math.pi)) + 2
        n = np.arange(1, nmax + 1)
        chi = np.array([kronecker(d, int(k)) for k in n], float)
        U = math.log(14 * q)
        xg, wg = np.polynomial.legendre.leggauss(nodes)
        self.u = (xg + 1) * U / 2
        self.w = wg * U / 2
        x = np.exp(self.u)
        self.theta = (np.exp(-math.pi * np.outer(x, n * n) / q) * (chi * n ** self.a)).sum(axis=1)

    def Z(self, t):
        t = np.atleast_1d(np.asarray(t, float))
        # x^((1/2 + it + a)/2) + conj = 2 x^((1/2 + a)/2) cos(t u / 2)
        k = (0.5 + self.a) / 2
        lam = 2 * ((self.w * self.theta * np.exp(k * self.u))[None, :] * np.cos(np.outer(t, self.u) / 2)).sum(axis=1)
        norm = np.array([float(abs(mp.gamma((0.5 + 1j * tt + self.a) / 2))) for tt in t]) * (self.q / math.pi) ** ((0.5 + self.a) / 2)
        return lam / norm

    def zeros(self, T: float, step: float = 0.02) -> np.ndarray:
        from scipy.optimize import brentq
        ts = np.arange(1e-6, T + step, step)
        v = self.Z(ts)
        out = []
        for i in np.nonzero(np.sign(v[:-1]) * np.sign(v[1:]) < 0)[0]:
            out.append(brentq(lambda s: float(self.Z(s)[0]), ts[i], ts[i + 1], xtol=1e-13))
        return np.array(out)


def fundamental_discriminants(lo: int, hi: int) -> list:
    return [d for d in range(-hi, hi + 1) if lo < abs(d) <= hi and is_fundamental(d)]


def _qL_zeros_job(args):
    d, xmax = args
    L = QuadraticL(d)
    T = 2 * math.pi * xmax / math.log(abs(d)) + 0.3
    return d, L.zeros(T)


# ====================================================================== 7. Thomas-Fermi, Majorana's way
TF_SLOPE = mp.mpf("-1.588071022611375312718684509423950109452746621674825616765677")


def tf_series(nterms: int, dps: int = 50) -> list:
    """Majorana's series u(t) = sum a_n tau^n, tau = 1 - t, for (1 - t^2 u) du/dt = 8 (t u^2 - 1), u(1) = 1.
    a1 solves a1^2 - 18 a1 + 8 = 0 (root 9 - sqrt 73); a_N for N >= 2 is fixed by a linear equation."""
    with mp.workdps(dps):
        a = [mp.mpf(1), 9 - mp.sqrt(73)]

        def residual(N, aN):
            b = a + [aN]
            A = [mp.mpf(0)] + [-(b[k] - 2 * b[k - 1] + (b[k - 2] if k >= 2 else 0)) for k in range(1, N + 1)]
            B = [-(k + 1) * b[k + 1] for k in range(N)]
            lhs = sum(A[k] * B[N - k] for k in range(1, N + 1))
            sq = [sum(b[i] * b[k - i] for i in range(k + 1)) for k in range(N + 1)]
            rhs = 8 * (sq[N] - sq[N - 1])
            return lhs - rhs
        for N in range(2, nterms):
            r0 = residual(N, mp.mpf(0))
            r1 = residual(N, mp.mpf(1))
            a.append(-r0 / (r1 - r0))
        return a


class TFMajorana:
    """Majorana's parametric solution x(t) = 144^(1/3) t^2 e^(2 I(t)), phi(t) = e^(-6 I(t)),
    I(t) = Int_0^t u t'/(1 - t'^2 u) dt'  (one quadrature), with u = sum a_n tau^n, tau = 1 - t.

    Everything is done in tau: 1 - t^2 u = sum_(n>=1) d_n tau^n with d_n = -(a_n - 2 a_(n-1) + a_(n-2)) has no
    cancellation near t = 1, where x ~ 1/tau. Panels [2^-k, 2^-(k-1)], k <= kmax, cover x up to ~2^kmax."""

    def __init__(self, a, dps: int = 25, kmax: int = 110, nodes: int = 16, kmin: int = 60):
        self.dps = dps
        with mp.workdps(dps):
            self.a = [mp.mpf(x) for x in a]
            n = len(self.a)
            self.d = [mp.mpf(0)] + [-(self.a[k] - 2 * self.a[k - 1] + (self.a[k - 2] if k >= 2 else 0))
                                    for k in range(1, n)]
            self.d += [-(-2 * self.a[n - 1] + self.a[n - 2]), -self.a[n - 1]]     # (1 - tau)^2 u has degree n + 1
            self.c = mp.cbrt(144)
            xg, wg = np.polynomial.legendre.leggauss(nodes)
            self.gl = [(mp.mpf(float(x)), mp.mpf(float(w))) for x, w in zip(xg, wg)]
            # tau-panels: geometric towards tau = 1 (t = 0, where x^(s-1) ~ t^(2s-2) oscillates for complex s)
            # and towards tau = 0 (t = 1, x -> oo)
            self.t0 = mp.mpf(2) ** (-kmin)
            edges = [1 - self.t0] + [1 - mp.mpf(2) ** (-k) for k in range(kmin - 1, 0, -1)] + \
                [mp.mpf(2) ** (-k) for k in range(2, kmax + 1)]
            self.panels = []                                                 # (lo, hi, I(hi)) in tau
            I_hi = self._gl(self.g, 1 - self.t0, mp.mpf(1))                  # I(tau = 1) = I(t = 0) = 0
            for hi, lo in zip(edges[:-1], edges[1:]):
                self.panels.append((lo, hi, I_hi))
                I_hi += self._gl(self.g, lo, hi)
            self.I_end = I_hi
            self.tau_end = edges[-1]

    def g(self, tau):
        """dI/dt as a function of tau: u t / (1 - t^2 u)."""
        u = mp.polyval(self.a[::-1], tau)
        return u * (1 - tau) / mp.polyval(self.d[::-1], tau)

    def _gl(self, f, lo, hi):
        h = (hi - lo) / 2
        return h * mp.fsum(w * f(lo + h * (x + 1)) for x, w in self.gl)

    def I(self, tau):
        if tau > 1 - self.t0:
            return self._gl(self.g, tau, mp.mpf(1))
        for lo, hi, I_hi in self.panels:
            if lo <= tau <= hi:
                return I_hi + self._gl(self.g, tau, hi)
        raise ValueError(tau)

    def point(self, tau):
        I = self.I(tau)
        t = 1 - tau
        return self.c * t * t * mp.exp(2 * I), mp.exp(-6 * I)

    def phi_at(self, x):
        with mp.workdps(self.dps):
            x = mp.mpf(x)
            lo, hi = mp.log(self.tau_end), mp.mpf(0)                       # bisection in log tau
            for _ in range(400):
                mid = (lo + hi) / 2
                if self.point(mp.exp(mid))[0] > x:
                    lo = mid
                else:
                    hi = mid
                if hi - lo < mp.mpf(10) ** (-self.dps + 3):
                    break
            return self.point(mp.exp((lo + hi) / 2))[1]

    def tau_of_x(self, x):
        with mp.workdps(self.dps):
            lo, hi = mp.log(self.tau_end), mp.mpf(0)
            for _ in range(400):
                mid = (lo + hi) / 2
                if self.point(mp.exp(mid))[0] > x:
                    lo = mid
                else:
                    hi = mid
                if hi - lo < mp.mpf(10) ** (-self.dps + 3):
                    break
            return mp.exp((lo + hi) / 2)

    def mellin_truncated(self, s, X):
        """Int_0^X x^(s-1) phi dx from the parametric form (no asymptotic tail needed)."""
        with mp.workdps(self.dps):
            s = mp.mpc(s)
            tX = self.tau_of_x(mp.mpf(X))
            tot = (self.c * self.t0 ** 2) ** s / s
            for lo, hi, I_hi in self.panels:
                if hi <= tX:
                    continue
                lo = max(lo, tX)
                h = (hi - lo) / 2
                for x_, w in self.gl:
                    tau = lo + h * (x_ + 1)
                    I = I_hi + self._gl(self.g, tau, hi)
                    t = 1 - tau
                    Xt = self.c * t * t * mp.exp(2 * I)
                    dX = self.c * (2 * t + 2 * t * t * self.g(tau)) * mp.exp(2 * I)
                    tot += h * w * Xt ** (s - 1) * mp.exp(-6 * I) * dX
            return tot

    def mellin(self, s):
        """Int_0^oo x^(s-1) phi dx = Int_0^1 x^(s-1) phi (dx/dt) dtau for 0 < Re s < 3; beyond the last panel
        (x > ~2^kmax) the Sommerfeld tail 144 X^(s-3)/(3-s) is added."""
        with mp.workdps(self.dps):
            s = mp.mpc(s)
            tot = mp.mpc(0)
            for lo, hi, I_hi in self.panels:
                h = (hi - lo) / 2
                for x_, w in self.gl:
                    tau = lo + h * (x_ + 1)
                    I = I_hi + self._gl(self.g, tau, hi)
                    t = 1 - tau
                    X = self.c * t * t * mp.exp(2 * I)
                    dX = self.c * (2 * t + 2 * t * t * self.g(tau)) * mp.exp(2 * I)
                    tot += h * w * X ** (s - 1) * mp.exp(-6 * I) * dX
            t = 1 - self.tau_end
            Xend = self.c * t * t * mp.exp(2 * self.I_end)
            head = (self.c * self.t0 ** 2) ** s / s                          # x <= c t0^2: phi = 1 + O(x)
            return head + tot + 144 * Xend ** (s - 3) / (3 - s)


def _tf_rhs(s, y):
    # x = s^2: d phi/ds = 2 s phi', d phi'/ds = 2 phi^(3/2)  (smooth at s = 0, unlike phi'' = phi^1.5/sqrt x)
    return [2 * s * y[1], 2 * max(y[0], 0.0) ** 1.5]


def tf_shoot(tol: float = 1e-14, smax: float = 60.0) -> dict:
    """Independent solution of phi'' = phi^(3/2)/sqrt(x), phi(0) = 1, phi(oo) = 0, by bisection on phi'(0):
    too steep, phi crosses 0; too shallow, phi' turns positive. Integrated in s = sqrt(x)."""
    from scipy.integrate import solve_ivp

    def fate(B):
        def hit0(s, y):
            return y[0]
        hit0.terminal = True

        def up(s, y):
            return y[1]
        up.terminal = True
        sol = solve_ivp(_tf_rhs, (0.0, smax), [1.0, B], method="DOP853", rtol=1e-13, atol=1e-18, events=[hit0, up])
        if sol.t_events[0].size:
            return -1
        if sol.t_events[1].size:
            return +1
        return 0
    lo, hi = -1.7, -1.5
    undecided = 0
    while hi - lo > tol:
        mid = (lo + hi) / 2
        f = fate(mid)
        undecided += f == 0
        if f < 0:
            lo = mid
        else:
            hi = mid
    return {"slope": (lo + hi) / 2, "undecided": undecided}


def tf_ode_phi(slope, dps: int = 30):
    """phi(x) from the initial-value problem phi(0) = 1, phi'(0) = slope, by mpmath's Taylor-series ODE solver
    in s = sqrt(x) at `dps` digits (the growing mode x^lambda amplifies errors, so double precision is not
    enough beyond x ~ 50)."""
    with mp.workdps(dps):
        f = mp.odefun(lambda s, y: [2 * s * y[1], 2 * y[0] ** mp.mpf(1.5)], 0, [mp.mpf(1), mp.mpf(slope)])

    def phi(x):
        with mp.workdps(dps):
            return f(mp.sqrt(x))[0]
    return phi


def tf_ode_mellin(slope, s, X: float = 100.0, dps: int = 30):
    """Int_0^oo x^(s-1) phi dx from the 30-digit ODE on [0, X] plus the tail of the asymptotic expansion
    144/x^3 (1 + C1 x^-lambda + C2 x^-2lambda + C3 x^-3lambda), lambda = (sqrt 73 - 7)/2, fitted at X/4, X/2, X."""
    phi = tf_ode_phi(slope, dps)
    with mp.workdps(dps):
        s = mp.mpc(s)
        lam = (mp.sqrt(73) - 7) / 2
        xs = [mp.mpf(X) / 4, mp.mpf(X) / 2, mp.mpf(X)]
        A = mp.matrix([[x ** (-k * lam) for k in (1, 2, 3)] for x in xs])
        r = mp.matrix([phi(x) * x ** 3 / 144 - 1 for x in xs])
        C = mp.lu_solve(A, r)
        pts = [0, 0.5, 2, 8, 30, 60, X]
        head = mp.quad(lambda x: x ** (s - 1) * phi(x), [p for p in pts if p <= X])
        X = mp.mpf(X)
        tail = 144 * (X ** (s - 3) / (3 - s) + sum(C[k - 1] * X ** (s - 3 - k * lam) / (3 + k * lam - s) for k in (1, 2, 3)))
        return head + tail


def tf_lambda_fit(tf: "TFMajorana", xs=(1e3, 1e4, 1e5, 1e6)) -> float:
    """Sommerfeld exponent from Majorana's solution: x^3 phi/144 - 1 ~ C x^-lambda (local log-log slope at the
    two largest x, after removing the x^-2 lambda term with the other two)."""
    ys = [mp.log(abs(x ** 3 * tf.phi_at(x) / 144 - 1)) for x in xs]
    ls = [mp.log(x) for x in xs]
    sl = [-(ys[i + 1] - ys[i]) / (ls[i + 1] - ls[i]) for i in range(len(xs) - 1)]
    # Richardson-type: slope_i = lambda + O(x^-lambda); extrapolate the last two linearly in x^-lambda
    return float(sl[-1])


# ====================================================================== 8. Majorana algebras and moonshine
def _norton_sakuma(kind: str):
    """(names, product(x, y) -> dict, inner(x, y) -> Fraction) for the Norton-Sakuma algebra of type kind,
    from Table 2.2 of Castillo-Ramirez (2014); missing products follow from the dihedral symmetry and the
    inclusions 2A < 4B, 2B < 4A, 2A < 6A, 3A < 6A."""
    F = Fr
    if kind == "2A":
        names = [("a", 0), ("a", 1), ("a", 2)]

        def P(x, y):
            if x == y:
                return {x: 1}
            z = [k for k in names if k not in (x, y)][0]
            return {x: F(1, 8), y: F(1, 8), z: F(-1, 8)}

        def I(x, y):
            return F(1) if x == y else F(1, 8)
        return names, P, I
    if kind == "2B":
        names = [("a", 0), ("a", 1)]
        return names, (lambda x, y: {x: 1} if x == y else {}), (lambda x, y: F(1) if x == y else F(0))
    if kind in ("3A", "3C"):
        names = [("a", i) for i in range(3)] + ([("u",)] if kind == "3A" else [])

        def P(x, y):
            if x == y:
                return {x: 1}
            if x[0] == "a" and y[0] == "a":
                z = [k for k in names[:3] if k not in (x, y)][0]
                if kind == "3C":
                    return {x: F(1, 64), y: F(1, 64), z: F(-1, 64)}
                return {x: F(2, 32), y: F(2, 32), z: F(1, 32), ("u",): F(-135, 2048)}
            a = x if x[0] == "a" else y
            o = [k for k in names[:3] if k != a]
            return {a: F(2, 9), o[0]: F(-1, 9), o[1]: F(-1, 9), ("u",): F(5, 32)}

        def I(x, y):
            if x == y:
                return F(8, 5) if x == ("u",) else F(1)
            if x[0] == "a" and y[0] == "a":
                return F(13, 256) if kind == "3A" else F(1, 64)
            return F(1, 4)
        return names, P, I
    if kind == "4A":
        names = [("a", i) for i in range(4)] + [("v",)]

        def P(x, y):
            if x == y:
                return {x: 1}
            if x[0] == "a" and y[0] == "a":
                i, j = x[1], y[1]
                if (i - j) % 2 == 0:
                    return {}
                o = [("a", k) for k in range(4) if k not in (i, j)]
                return {x: F(3, 64), y: F(3, 64), o[0]: F(1, 64), o[1]: F(1, 64), ("v",): F(-3, 64)}
            a = x if x[0] == "a" else y
            i = a[1]
            return {a: F(5, 16), ("a", (i + 1) % 4): F(-2, 16), ("a", (i + 2) % 4): F(-1, 16),
                    ("a", (i + 3) % 4): F(-2, 16), ("v",): F(3, 16)}

        def I(x, y):
            if x == y:
                return F(2) if x == ("v",) else F(1)
            if x[0] == "a" and y[0] == "a":
                return F(1, 32) if (x[1] - y[1]) % 2 else F(0)
            return F(3, 8)
        return names, P, I
    if kind == "4B":
        names = [("a", i) for i in range(4)] + [("r",)]

        def P(x, y):
            if x == y:
                return {x: 1}
            if x[0] == "a" and y[0] == "a":
                i, j = x[1], y[1]
                if (i - j) % 2 == 0:
                    return {x: F(1, 8), y: F(1, 8), ("r",): F(-1, 8)}
                o = [("a", k) for k in range(4) if k not in (i, j)]
                return {x: F(1, 64), y: F(1, 64), o[0]: F(-1, 64), o[1]: F(-1, 64), ("r",): F(1, 64)}
            a = x if x[0] == "a" else y
            return {a: F(1, 8), ("r",): F(1, 8), ("a", (a[1] + 2) % 4): F(-1, 8)}

        def I(x, y):
            if x == y:
                return F(1)
            if x[0] == "a" and y[0] == "a":
                return F(1, 64) if (x[1] - y[1]) % 2 else F(1, 8)
            return F(1, 8)
        return names, P, I
    if kind == "5A":
        names = [("a", i) for i in range(5)] + [("w",)]

        def P(x, y):
            if x == y and x[0] == "a":
                return {x: 1}
            if x[0] == "a" and y[0] == "a":
                i, j = x[1], y[1]
                d = {("a", k): F(-1, 128) for k in range(5) if k not in (i, j)}
                d[x], d[y] = F(3, 128), F(3, 128)
                d[("w",)] = F(1) if (i - j) % 5 in (1, 4) else F(-1)
                return d
            if x[0] == "w" and y[0] == "w":
                return {("a", k): F(175, 2 ** 19) for k in range(5)}
            a = x if x[0] == "a" else y
            i, c = a[1], F(7, 2 ** 12)
            return {("a", (i + 1) % 5): c, ("a", (i - 1) % 5): c, ("a", (i + 2) % 5): -c, ("a", (i - 2) % 5): -c,
                    ("w",): F(7, 32)}

        def I(x, y):
            if x[0] == "a" and y[0] == "a":
                return F(1) if x == y else F(3, 128)
            if x[0] == "w" and y[0] == "w":
                return F(875, 2 ** 19)
            return F(0)
        return names, P, I
    if kind == "6A":
        names = [("a", i) for i in range(6)] + [("r",), ("u",)]

        def P(x, y):
            if x == y:
                return {x: 1}
            if x[0] == "a" and y[0] == "a":
                i, j = x[1], y[1]
                d = (j - i) % 6
                if d in (1, 5):
                    out = {("a", k): F(-1, 64) for k in range(6) if k not in (i, j)}
                    out.update({x: F(1, 64), y: F(1, 64), ("r",): F(1, 64), ("u",): F(45, 2 ** 11)})
                    return out
                if d in (2, 4):
                    k = (({0, 2, 4} if i % 2 == 0 else {1, 3, 5}) - {i, j}).pop()
                    return {x: F(2, 32), y: F(2, 32), ("a", k): F(1, 32), ("u",): F(-135, 2 ** 11)}
                return {x: F(1, 8), y: F(1, 8), ("r",): F(-1, 8)}
            if y[0] == "a":
                x, y = y, x
            if x[0] == "a" and y == ("r",):
                i = x[1]
                return {x: F(1, 8), ("r",): F(1, 8), ("a", (i + 3) % 6): F(-1, 8)}
            if x[0] == "a" and y == ("u",):
                i = x[1]
                return {x: F(2, 9), ("a", (i + 2) % 6): F(-1, 9), ("a", (i - 2) % 6): F(-1, 9), ("u",): F(5, 32)}
            return {}                                     # r . u = 0

        def I(x, y):
            if x == y:
                return F(8, 5) if x == ("u",) else F(1)
            if x[0] == "a" and y[0] == "a":
                return {1: F(5, 256), 5: F(5, 256), 2: F(13, 256), 4: F(13, 256), 3: F(1, 8)}[(y[1] - x[1]) % 6]
            s = {x[0], y[0]}
            if s == {"a", "r"}:
                return F(1, 8)
            if s == {"a", "u"}:
                return F(1, 4)
            return F(0)
        return names, P, I
    raise ValueError(kind)


NS_KINDS = ("2A", "2B", "3A", "3C", "4A", "4B", "5A", "6A")
NS_LENGTHS = {"2A": Fr(12, 5), "2B": Fr(2), "3A": Fr(116, 35), "3C": Fr(32, 11), "4A": Fr(4),
              "4B": Fr(19, 5), "5A": Fr(32, 7), "6A": Fr(51, 10)}
FUSION = {(1, 1): {1}, (1, 0): {0}, (0, 0): {0}, (1, Fr(1, 4)): {Fr(1, 4)}, (0, Fr(1, 4)): {Fr(1, 4)},
          (Fr(1, 4), Fr(1, 4)): {1, 0}, (1, Fr(1, 32)): {Fr(1, 32)}, (0, Fr(1, 32)): {Fr(1, 32)},
          (Fr(1, 4), Fr(1, 32)): {Fr(1, 32)}, (Fr(1, 32), Fr(1, 32)): {1, 0, Fr(1, 4)}}


class NortonSakuma:
    def __init__(self, kind: str):
        names, P, I = _norton_sakuma(kind)
        self.kind, self.names = kind, names
        n = self.n = len(names)
        idx = {k: i for i, k in enumerate(names)}
        self.T = [[[Fr(0)] * n for _ in range(n)] for _ in range(n)]
        for a in names:
            for b in names:
                for k, c in P(a, b).items():
                    self.T[idx[a]][idx[b]][idx[k]] += Fr(c)
        self.G = [[Fr(I(a, b)) for b in names] for a in names]

    def mul(self, u, v):
        n = self.n
        out = [Fr(0)] * n
        for i in range(n):
            if u[i] == 0:
                continue
            for j in range(n):
                if v[j] == 0:
                    continue
                c = u[i] * v[j]
                Tij = self.T[i][j]
                for k in range(n):
                    if Tij[k]:
                        out[k] += c * Tij[k]
        return out

    def ip(self, u, v):
        return sum(u[i] * self.G[i][j] * v[j] for i in range(self.n) for j in range(self.n) if u[i] and v[j])

    def e(self, i):
        v = [Fr(0)] * self.n
        v[i] = Fr(1)
        return v

    def ad_matrix(self, i=0):
        """Column j = a_i . e_j."""
        cols = [self.mul(self.e(i), self.e(j)) for j in range(self.n)]
        return [[cols[j][k] for j in range(self.n)] for k in range(self.n)]


def _nullspace(M):
    """Exact nullspace over Q (list of basis vectors)."""
    rows = [r[:] for r in M]
    m, n = len(rows), len(rows[0])
    piv, r = [], 0
    for c in range(n):
        p = next((i for i in range(r, m) if rows[i][c] != 0), None)
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(m):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(n) if c not in piv]
    basis = []
    for f in free:
        v = [Fr(0)] * n
        v[f] = Fr(1)
        for i, c in enumerate(piv):
            v[c] = -rows[i][f]
        basis.append(v)
    return basis


def _solve(M, b):
    n = len(M)
    A = [M[i][:] + [b[i]] for i in range(n)]
    for c in range(n):
        p = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[p] = A[p], A[c]
        pv = A[c][c]
        A[c] = [x / pv for x in A[c]]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return [A[i][n] for i in range(n)]


def norton_sakuma_check(kind: str, pairs: int = 2000, seed: int = 0) -> dict:
    A = NortonSakuma(kind)
    n = A.n
    E = [A.e(i) for i in range(n)]
    comm = all(A.T[i][j] == A.T[j][i] for i in range(n) for j in range(n))
    assoc = all(A.ip(E[i], A.mul(E[j], E[k])) == A.ip(A.mul(E[i], E[j]), E[k])
                for i in range(n) for j in range(n) for k in range(n))
    rng = np.random.default_rng(seed)
    worst = math.inf
    for _ in range(pairs):
        u = [Fr(int(x)) for x in rng.integers(-5, 6, n)]
        v = [Fr(int(x)) for x in rng.integers(-5, 6, n)]
        uv = A.mul(u, v)
        worst = min(worst, float(A.ip(A.mul(u, u), A.mul(v, v)) - A.ip(uv, uv)))
    ad = A.ad_matrix(0)
    spaces = {}
    for lam in (Fr(1), Fr(0), Fr(1, 4), Fr(1, 32)):
        M = [[ad[r][c] - (lam if r == c else 0) for c in range(n)] for r in range(n)]
        sp = _nullspace(M)
        if sp:
            spaces[lam] = sp
    semisimple = sum(len(v) for v in spaces.values()) == n
    dim1 = len(spaces.get(Fr(1), []))
    # fusion rules: products of eigenvectors decompose into the allowed eigenspaces
    basis = [v for lam in spaces for v in spaces[lam]]
    labels = [lam for lam in spaces for _ in spaces[lam]]
    Bt = [[basis[j][i] for j in range(n)] for i in range(n)]
    fusion_ok = True
    for x in range(n):
        for y in range(x, n):
            lx, ly = labels[x], labels[y]
            key = (lx, ly) if (lx, ly) in FUSION else (ly, lx)
            allowed = FUSION[key]
            coeff = _solve(Bt, A.mul(basis[x], basis[y]))
            if any(coeff[k] != 0 and labels[k] not in allowed for k in range(n)):
                fusion_ok = False
    # tau(a): -1 on the 1/32-space, +1 elsewhere; must be an automorphism
    D = [Fr(-1) if lab == Fr(1, 32) else Fr(1) for lab in labels]

    def tau(v):
        c = _solve(Bt, v)
        out = [Fr(0)] * n
        for k in range(n):
            if c[k]:
                for i in range(n):
                    out[i] += D[k] * c[k] * basis[k][i]
        return out
    tau_ok = all(tau(A.mul(E[i], E[j])) == A.mul(tau(E[i]), tau(E[j])) for i in range(n) for j in range(n))
    # identity: id . e_j = e_j for all j  <=>  sum_i x_i T[i][j] = e_j
    M = [[A.T[i][j][k] for i in range(n)] for j in range(n) for k in range(n)]
    rhs = [Fr(1) if j == k else Fr(0) for j in range(n) for k in range(n)]
    # least-squares-free exact solve: pick n independent rows
    ident = _solve_overdetermined(M, rhs, n)
    ident_ok = ident is not None and all(A.mul(ident, E[j]) == E[j] for j in range(n))
    length = A.ip(ident, ident) if ident_ok else None
    return {"kind": kind, "dim": n, "commutative": comm, "form_associative": assoc, "norton_min": worst,
            "spectrum": sorted(spaces), "semisimple": semisimple, "dim_V1": dim1, "fusion": fusion_ok,
            "tau_automorphism": tau_ok, "identity_length": length, "length_expected": NS_LENGTHS[kind]}


def _solve_overdetermined(M, rhs, n):
    rows = [M[i][:] + [rhs[i]] for i in range(len(M))]
    piv, r = [], 0
    m = len(rows)
    for c in range(n):
        p = next((i for i in range(r, m) if rows[i][c] != 0), None)
        if p is None:
            return None
        rows[r], rows[p] = rows[p], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(m):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        piv.append(c)
        r += 1
    if any(rows[i][n] != 0 for i in range(n, m)):
        return None
    return [rows[i][n] for i in range(n)]


def j_coefficients(nmax: int) -> list:
    """c(-1..nmax) of j(tau) - 744 = q^-1 + 196884 q + ..., from E4^3/Delta in exact integers."""
    L = nmax + 2
    sigma3 = [0] + [sum(d ** 3 for d in range(1, k + 1) if k % d == 0) for k in range(1, L + 1)]
    E4 = [1] + [240 * sigma3[k] for k in range(1, L + 1)]

    def mul(a, b):
        return [sum(a[i] * b[k - i] for i in range(k + 1)) for k in range(L + 1)]
    E43 = mul(mul(E4, E4), E4)
    eta24 = [1] + [0] * L                    # prod (1 - q^n)^24
    for n in range(1, L + 1):
        for _ in range(24):
            eta24 = [eta24[k] - (eta24[k - n] if k >= n else 0) for k in range(L + 1)]
    inv = [0] * (L + 1)                      # 1/eta24
    inv[0] = 1
    for k in range(1, L + 1):
        inv[k] = -sum(eta24[i] * inv[k - i] for i in range(1, k + 1))
    jq = mul(E43, inv)                       # = q j(q)
    coeffs = jq[:nmax + 2]
    coeffs[1] -= 744
    return coeffs                             # index i <-> q^(i-1)


def kloosterman(m: int, n: int, c: int) -> float:
    h = np.array([x for x in range(c) if math.gcd(x, c) == 1], dtype=np.int64)
    hinv = np.array([pow(int(x), -1, c) for x in h], dtype=np.int64) if c > 1 else np.array([0])
    if c == 1:
        return 1.0
    return float(np.cos(2 * np.pi * ((m * h + n * hinv) % c) / c).sum())


def rademacher_j(n: int, K: int) -> float:
    """Rademacher/Petersson: c(n) = (2 pi/sqrt n) sum_k K(n, -1; k)/k I_1(4 pi sqrt(n)/k)."""
    from scipy.special import iv
    tot = 0.0
    for k in range(1, K + 1):
        tot += kloosterman(n, -1, k) / k * iv(1, 4 * math.pi * math.sqrt(n) / k)
    return 2 * math.pi / math.sqrt(n) * tot


def weil_bound_check(cmax: int, mn: int = 5) -> dict:
    worst = 0.0
    for c in range(1, cmax + 1):
        dc = sum(1 for d in range(1, c + 1) if c % d == 0)
        h = np.array([x for x in range(c) if math.gcd(x, c) == 1], dtype=np.int64)
        hinv = np.array([pow(int(x), -1, c) for x in h], dtype=np.int64) if c > 1 else np.array([0], dtype=np.int64)
        for m in range(1, mn + 1):
            for n in range(1, mn + 1):
                K = np.cos(2 * np.pi * ((m * h + n * hinv) % c) / c).sum() if c > 1 else 1.0
                bound = dc * math.sqrt(math.gcd(math.gcd(m, n), c)) * math.sqrt(c)
                worst = max(worst, abs(K) / bound)
    return {"max_ratio": worst}


MONSTER_DIMS = (1, 196883, 21296876, 842609326)
MCKAY_THOMPSON = {1: (1, 1, 0, 0), 2: (1, 1, 1, 0), 3: (2, 2, 1, 1)}


def tf_ode_mellin_truncated(slope, s, X: float = 100.0, dps: int = 30):
    """Int_0^X x^(s-1) phi dx from the 30-digit ODE."""
    phi = tf_ode_phi(slope, dps)
    with mp.workdps(dps):
        s = mp.mpc(s)
        return mp.quad(lambda x: x ** (s - 1) * phi(x), [p for p in (0, 0.5, 2, 8, 30, 60, X) if p <= X])
