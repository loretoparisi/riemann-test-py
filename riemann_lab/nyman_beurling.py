"""Nyman-Beurling criterion in Baez-Duarte's form: distances d_N -> 0.

Let rho(x) = {x} (fractional part), chi = indicator of (0, 1], and e_k(x) = rho(1/(k x)).
Baez-Duarte (2003):

    RH  <=>  d_N -> 0,    d_N^2 = inf_{c_1..c_N} || chi - sum_{k<=N} c_k e_k ||^2_{L^2(0, inf)}.

d_N is the distance from chi to span{e_1..e_N}, so d_N^2 = 1 - b^T G^-1 b with

    b_k = <chi, e_k> = (log k + 1 - gamma) / k,
    G_hk = <e_h, e_k> = A(h', k') / d     (d = gcd(h, k), h = d h', k = d k'),

and Vasyunin's closed form for coprime h, k (checked here against direct integration):

    A(h, k) = (log 2pi - gamma)/2 (1/h + 1/k) + (k - h)/(2hk) log(h/k)
              - pi/(2hk) (V(h, k) + V(k, h)),      V(h, k) = sum_{m=1}^{k-1} {mh/k} cot(pi m/k).

What to expect. Burnol (2002) proved  liminf d_N^2 log N >= sum_rho m_rho^2 / |rho|^2,
which is C0 = 2 + gamma - log 4pi = 0.04619... if all zeros are simple. Baez-Duarte,
Balazard, Landreau and Saias conjectured d_N^2 ~ C0 / log N under RH; Landreau and
Richard (Exp. Math. 11, 2002) computed d_N to N = 20000 and found a slow, irregular
decrease with d_N^2 log N close to C0 (not monotone in N). The Gram
matrix is very ill-conditioned, so everything runs in mpmath at high precision and
the answer is accepted only when two precisions agree.
"""
from __future__ import annotations

import math

import mpmath as mp
import numpy as np

C0 = 2 + 0.5772156649015329 - math.log(4 * math.pi)     # sum 1/|rho|^2 = 0.0461914...


def _cot_tables(N: int):
    return {k: [None] + [mp.cot(mp.pi * m / k) for m in range(1, k)] for k in range(2, N + 1)}


def _V(h: int, k: int, cot) -> mp.mpf:
    if k == 1:
        return mp.mpf(0)
    ck = cot[k]
    return mp.fsum((m * h % k) * ck[m] for m in range(1, k)) / k


def gram_entry(h: int, k: int, cot) -> mp.mpf:
    d = math.gcd(h, k)
    h, k = h // d, k // d
    A = ((mp.log(2 * mp.pi) - mp.euler) / 2 * (mp.mpf(1) / h + mp.mpf(1) / k)
         + mp.mpf(k - h) / (2 * h * k) * mp.log(mp.mpf(h) / k)
         - mp.pi / (2 * h * k) * (_V(h, k, cot) + _V(k, h, cot)))
    return A / d


def gram_entry_numeric(h: int, k: int, periods: int = 200) -> float:
    """<e_h, e_k> = int_0^inf {y/h}{y/k} y^-2 dy by exact piecewise integration (cross-check)."""
    with mp.workdps(30):
        L = h * k // math.gcd(h, k)
        Y = periods * L
        bps = sorted({0, *range(h, Y + 1, h), *range(k, Y + 1, k)})
        tot = mp.mpf(bps[1]) / (h * k)
        for lo, hi in zip(bps[1:-1], bps[2:]):
            a, b = lo // h, lo // k
            tot += (mp.mpf(hi - lo) / (h * k) - (mp.mpf(b) / h + mp.mpf(a) / k) * mp.log(mp.mpf(hi) / lo)
                    - a * b * (mp.mpf(1) / hi - mp.mpf(1) / lo))
        cuts = sorted({0, *range(h, L + 1, h), *range(k, L + 1, k)})
        mean = mp.quad(lambda y: mp.frac(y / h) * mp.frac(y / k), cuts) / L
        return float(tot + mean / Y)


def distances(N: int, dps: int = 60):
    """d_n^2 for n = 1..N (one Cholesky of the N x N Gram matrix gives all of them)."""
    with mp.workdps(dps):
        cot = _cot_tables(N)
        G = mp.matrix(N, N)
        for h in range(1, N + 1):
            for k in range(h, N + 1):
                G[h - 1, k - 1] = G[k - 1, h - 1] = gram_entry(h, k, cot)
        b = [(mp.log(k) + 1 - mp.euler) / k for k in range(1, N + 1)]
        # Cholesky G = L L^T; with y = L^-1 b, ||proj||^2 over the first n = sum_{i<n} y_i^2
        Lm = mp.matrix(N, N)
        for j in range(N):
            s = G[j, j] - mp.fsum(Lm[j, i] ** 2 for i in range(j))
            if s <= 0:
                raise ArithmeticError(f"Gram matrix not positive at precision {dps} (n={j + 1}); raise dps")
            Lm[j, j] = mp.sqrt(s)
            for r in range(j + 1, N):
                Lm[r, j] = (G[r, j] - mp.fsum(Lm[r, i] * Lm[j, i] for i in range(j))) / Lm[j, j]
        y = []
        for j in range(N):
            y.append((b[j] - mp.fsum(Lm[j, i] * y[i] for i in range(j))) / Lm[j, j])
        d2, acc = [], mp.mpf(0)
        for j in range(N):
            acc += y[j] ** 2
            d2.append(1 - acc)
        return np.array([float(v) for v in d2])


def summary(N: int = 120, dps: int = 60) -> dict:
    """d_N^2 at two precisions, monotonicity, and d_N^2 log N against Burnol's constant C0."""
    d2 = distances(N, dps)
    d2b = distances(N, dps + 40)
    n = np.arange(1, N + 1)
    scaled = d2 * np.log(np.maximum(n, 2))
    return {"N": N, "dps": (dps, dps + 40), "d2_N": float(d2b[-1]),
            "precision_agreement": float(np.max(np.abs(d2 - d2b))),
            "monotone_nonincreasing": bool(np.all(np.diff(d2b) <= 1e-30)),
            "d2_log_N": float(scaled[-1]), "C0_burnol": C0,
            "above_burnol": bool(scaled[-1] > C0),
            "n": n, "d2": d2b}
