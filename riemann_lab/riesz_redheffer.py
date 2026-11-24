"""Riesz (1916) and Redheffer (1977) criteria.

Riesz
-----
    R(x) = sum_{k>=1} (-1)^(k+1) x^k / ((k-1)! zeta(2k)),
    RH  <=>  R(x) = O(x^(1/4 + eps)).

Expanding 1/zeta(2k) = sum mu(n) n^(-2k) gives the fast form
    R(x) = x * sum_{n>=1} mu(n)/n^2 * exp(-x/n^2),
and moving the Mellin contour right (R(x) = (1/2pi i) int Gamma(w) x^(1-w) / zeta(2-2w) dw)
gives, with simple zeros,
    R(x) = sum_rho Gamma(1 - rho/2) / (2 zeta'(rho)) * x^(rho/2)
plus sum_k k! x^(-k) / (2 zeta'(-2k)) from the trivial zeros,
so R(x)/x^(1/4) is an almost-periodic function in log x whose amplitude is
dominated by the first few zeros (Gamma(1 - rho/2) decays like e^(-pi |gamma|/4)).
``riesz`` computes R exactly from mu; ``riesz_from_zeros`` evaluates the zero sum.
Their agreement is the convergence check.

Truncation: terms with n > M = c sqrt(x) are handled by expanding the exponential,
    sum_{n>M} mu(n) n^(-2) e^(-x/n^2) = sum_j (-x)^j / j! * (1/zeta(2j+2) - sum_{n<=M} mu(n) n^(-2j-2)),
which converges like (x/M^2)^j / j!.

Redheffer
---------
A_n is the n x n 0/1 matrix with a_ij = 1 if j = 1 or i | j. Then det A_n = M(n),
the Mertens function, so RH <=> det A_n = O(n^(1/2 + eps)). We check the identity
exactly (fraction-free integer elimination) for small n and in floating point for
larger n, and report the dominant eigenvalues, which grow like sqrt(n) (Vaughan).
"""
from __future__ import annotations

import math

import mpmath as mp
import numpy as np

from .criteria import mertens, mobius_array


# ===================================================================== Riesz
def riesz(x, c: float = 4.0, L: int | None = None, jmax: int = 14):
    """R(x) for an array of x >= 10 (float64), with a rigorous bound on the truncation.

    S(x) = R(x)/x is split as
        1/zeta(2) + sum_{n<=N} mu(n) n^-2 (e^(-x/n^2) - 1)                      (N = c sqrt x)
                  + sum_{j>=1} (-x)^j / j! * sum_{N<n<=L} mu(n) n^(-2j-2)  + E,
    and |E| <= sum_j x^j / j! * L^(-2j-1) / (2j+1) ~ x / (3 L^3) is returned as ``err``.
    Returns (R, err) arrays.
    """
    x = np.sort(np.atleast_1d(np.asarray(x, dtype=float)))
    L = L or int(60 * x.max() ** (7 / 12)) + 1000
    mu8 = mobius_array(L)
    Ns = np.minimum((c * np.sqrt(x)).astype(np.int64) + 10, L)
    Nstar = int(Ns.max())
    mu = mu8[:Nstar + 1].astype(float)
    n = np.arange(Nstar + 1, dtype=float)
    n[0] = np.inf
    inv2 = 1.0 / n**2
    # T_j(N) = sum_{N<n<=L} mu(n) n^(-2j-2) = (suffix over (N, N*]) + (block over (N*, L], chunked)
    big = np.zeros(jmax + 1)
    for c0 in range(Nstar + 1, L + 1, 1 << 22):
        c1 = min(c0 + (1 << 22), L + 1)
        nn = np.arange(c0, c1, dtype=float)
        i2 = 1.0 / nn**2
        w = mu8[c0:c1].astype(float) * i2
        for j in range(1, jmax + 1):
            w = w * i2
            big[j] += w.sum()
    T = np.zeros((jmax + 1, x.size))
    w = mu * inv2
    for j in range(1, jmax + 1):
        w = w * inv2
        suffix = np.concatenate((np.cumsum(w[::-1])[::-1], [0.0]))   # suffix[k] = sum_{k<=n<=N*}
        T[j] = suffix[Ns + 1] + big[j]
    inv_z2 = float(1 / mp.zeta(2))
    R = np.empty_like(x)
    err = np.empty_like(x)
    for i, (xi, N) in enumerate(zip(x, Ns)):
        nn = n[1:N + 1]
        head = math.fsum(np.concatenate(([inv_z2], mu[1:N + 1] / nn**2 * np.expm1(-xi / nn**2))))
        tail, term = 0.0, 1.0
        for j in range(1, jmax + 1):
            term *= -xi / j
            tail += term * T[j, i]
        e = sum(xi**j / math.factorial(j) * float(L) ** (-2 * j - 1) / (2 * j + 1) for j in range(1, 6))
        R[i] = xi * (head + tail)
        err[i] = xi * e
    return R, err


def riesz_series_mp(x: float, dps: int | None = None) -> float:
    """R(x) from the defining alternating series, at high precision (slow; small x only)."""
    dps = dps or int(x / 2.3) + 30
    with mp.workdps(dps):
        X = mp.mpf(x)
        s, k = mp.mpf(0), 1
        term = X
        while True:
            t = term / mp.zeta(2 * k)
            s += t if k % 2 else -t
            if k > X and abs(t) < mp.mpf(10) ** (-dps + 5):
                break
            term = term * X / k
            k += 1
        return float(s)


def riesz_from_zeros(x, nzeros: int = 30, ntrivial: int = 3) -> np.ndarray:
    """sum over the first nzeros zeros (and conjugates) of Gamma(1-rho/2) x^(rho/2) / (2 zeta'(rho)),
    plus the first ``ntrivial`` terms k! x^-k / (2 zeta'(-2k)) from the trivial zeros."""
    x = np.atleast_1d(np.asarray(x, dtype=float))
    total = np.zeros_like(x)
    with mp.workdps(25):
        for k in range(1, nzeros + 1):
            rho = mp.zetazero(k)
            c = complex(mp.gamma(1 - rho / 2) / (2 * mp.zeta(rho, derivative=1)))
            r = complex(rho)
            total += 2 * np.real(c * np.exp(r / 2 * np.log(x)))
        # trivial zeros of zeta(2-2w) at w = 1+k give k! x^-k / (2 zeta'(-2k)) (asymptotic)
        for k in range(1, ntrivial + 1):
            total += float(mp.factorial(k) / (2 * mp.zeta(-2 * k, derivative=1))) * x ** (-k)
    return total


def riesz_summary(xmax: float = 1e10, npts: int = 200, nzeros: int = 30) -> dict:
    """max |R(x)|/x^(1/4) on a log grid up to xmax, plus agreement with the zero sum."""
    x = np.geomspace(10, xmax, npts)
    R, trunc = riesz(x)
    ratio = R / x**0.25
    Rz = riesz_from_zeros(x, nzeros)
    big = x > 1e3
    err = np.abs(R - Rz)[big] / x[big] ** 0.25
    k = int(np.argmax(np.abs(ratio)))
    exps = np.log(np.abs(R[x > 1e4]) + 1e-300) / np.log(x[x > 1e4])
    return {"xmax": xmax, "max_abs_R_over_x14": float(np.abs(ratio).max()), "at_x": float(x[k]),
            "max_err_vs_zero_sum_over_x14": float(err.max()), "nzeros": nzeros,
            "max_growth_exponent_x>1e4": float(exps.max()),
            "max_truncation_bound_over_x14": float((trunc / x**0.25).max()),
            "x": x, "R": R, "R_zeros": Rz}


# ===================================================================== Redheffer
def redheffer_matrix(n: int) -> np.ndarray:
    A = np.zeros((n, n), dtype=np.int64)
    for i in range(1, n + 1):
        A[i - 1, i - 1::i] = 1
    A[:, 0] = 1
    return A


def det_bareiss(A) -> int:
    """Exact integer determinant (fraction-free Gaussian elimination)."""
    M = [list(map(int, row)) for row in A]
    n = len(M)
    sign, prev = 1, 1
    for k in range(n - 1):
        if M[k][k] == 0:
            for r in range(k + 1, n):
                if M[r][k] != 0:
                    M[k], M[r] = M[r], M[k]
                    sign = -sign
                    break
            else:
                return 0
        pk = M[k][k]
        rowk = M[k]
        for i in range(k + 1, n):
            mik = M[i][k]
            rowi = M[i]
            for j in range(k + 1, n):
                rowi[j] = (rowi[j] * pk - mik * rowk[j]) // prev
            rowi[k] = 0
        prev = pk
    return sign * M[-1][-1]


def redheffer_check(n_exact: int = 150, n_float=(200, 500, 1000, 2000)) -> dict:
    """det A_n vs M(n): exact for n <= n_exact, floating-point LU for n in n_float."""
    Mx = mertens(max(max(n_float), n_exact))
    exact_ok = all(det_bareiss(redheffer_matrix(n)) == Mx[n] for n in range(1, n_exact + 1))
    rows = []
    for n in n_float:
        A = redheffer_matrix(n).astype(float)
        sgn, logdet = np.linalg.slogdet(A)
        det = sgn * math.exp(logdet) if sgn != 0 else 0.0
        ev = np.linalg.eigvals(A)
        lam = ev[np.argsort(-np.abs(ev))][:2]
        rows.append({"n": n, "det_float": det, "M_n": int(Mx[n]), "match": round(det) == Mx[n],
                     "top_eigs": [complex(v) for v in lam],
                     "top_eig_over_sqrt_n": float(np.abs(lam[0]) / math.sqrt(n))})
    return {"exact_ok_n<=": n_exact if exact_ok else None, "float": rows,
            "all_match": exact_ok and all(r["match"] for r in rows)}
