"""Elementary and analytic statements equivalent to RH, checked numerically.

* Robin (1984):     RH  <=>  sigma(n) < e^gamma n log log n   for all n > 5040.
* Lagarias (2002):  RH  <=>  sigma(n) <= H_n + exp(H_n) log H_n  for all n >= 1.
* Mertens:          RH  <=>  M(x) = O(x^(1/2+eps)).  (|M(x)| < sqrt(x) is FALSE.)
* Li (1997):        RH  <=>  lambda_n >= 0 for all n >= 1.

Robin's inequality can only fail at colossally abundant (CA) numbers if it fails
at all (Robin), so we check it both by brute force up to N and at CA numbers
far beyond any sieve (log n ~ 10^6).
"""
from __future__ import annotations

import math

import mpmath as mp
import numpy as np

from .primes import sieve

EULER_GAMMA = 0.5772156649015329
E_GAMMA = math.exp(EULER_GAMMA)


# ------------------------------------------------------------ sigma, mu
def sigma_array(N: int) -> np.ndarray:
    """sigma(n) for 0 <= n <= N (divisor sums by a numpy sieve, O(N log N))."""
    s = np.zeros(N + 1, dtype=np.int64)
    for d in range(1, N + 1):
        s[d::d] += d
    return s


def mobius_array(N: int) -> np.ndarray:
    mu = np.ones(N + 1, dtype=np.int8)
    mu[0] = 0
    for p in sieve(N):
        mu[p::p] *= -1
        mu[p * p::p * p] = 0
    return mu


# ------------------------------------------------------------ Robin
def robin_bruteforce(N: int = 10**6) -> dict:
    """Check Robin's inequality for all 5040 < n <= N; also report the worst n."""
    s = sigma_array(N)
    n = np.arange(N + 1, dtype=float)
    lo = 5041
    ratio = s[lo:] / (n[lo:] * np.log(np.log(n[lo:])))
    k = int(np.argmax(ratio))
    viol_small = [int(m) for m in range(3, 5041) if s[m] >= E_GAMMA * m * math.log(math.log(m))]
    return {"N": N, "holds": bool((ratio < E_GAMMA).all()), "max_ratio": float(ratio[k]),
            "argmax_n": lo + k, "e_gamma": E_GAMMA, "violations_n_le_5040": viol_small}


def colossally_abundant(count: int = 2000, pmax: int = 10**6):
    """Yield (log n, log(sigma(n)/n), n_prime_factors_dict) for successive CA numbers.

    A CA number for parameter eps has exponent a_p maximising sigma(p^a)/p^(a(1+eps)).
    Increasing a_p from k-1 to k happens at the critical value
        eps_{p,k} = log((p^(k+1)-1)/(p^(k+1)-p)) / log p,
    so sorting the critical values in decreasing order gives the CA sequence,
    each step multiplying n by one prime p.
    """
    import heapq
    primes = sieve(pmax)
    def crit(p, k):
        return math.log((p ** (k + 1) - 1) / (p ** (k + 1) - p)) / math.log(p)
    heap = [(-crit(int(p), 1), int(p), 1) for p in primes[:1]]
    next_prime_idx = 1
    logn, logsig = 0.0, 0.0
    expo: dict[int, int] = {}
    for _ in range(count):
        # make sure the next unused prime is in the heap
        while next_prime_idx < len(primes) and (not heap or -heap[0][0] <= crit(int(primes[next_prime_idx]), 1)):
            p = int(primes[next_prime_idx]); heapq.heappush(heap, (-crit(p, 1), p, 1)); next_prime_idx += 1
        _, p, k = heapq.heappop(heap)
        expo[p] = k
        logn += math.log(p)
        # sigma(p^k)/p^k over sigma(p^(k-1))/p^(k-1)
        logsig += math.log((1 - p ** -(k + 1.0)) / (1 - p ** -float(k)))
        heapq.heappush(heap, (-crit(p, k + 1), p, k + 1))
        yield logn, logsig, dict(expo)


def robin_at_ca(count: int = 5000, pmax: int = 10**6) -> dict:
    """Robin margin e^gamma - sigma(n)/(n log log n) along the CA sequence."""
    rows = []
    for logn, logsig, _ in colossally_abundant(count, pmax):
        if logn > math.log(5040):
            ratio = math.exp(logsig) / math.log(logn)
            rows.append((logn, ratio))
    arr = np.array(rows)
    return {"count": len(arr), "log10_n_max": float(arr[-1, 0] / math.log(10)),
            "max_ratio": float(arr[:, 1].max()), "holds": bool((arr[:, 1] < E_GAMMA).all()),
            "log_n": arr[:, 0], "ratio": arr[:, 1]}


# ------------------------------------------------------------ Lagarias
def lagarias_bruteforce(N: int = 10**6) -> dict:
    s = sigma_array(N)[1:].astype(float)
    n = np.arange(1, N + 1)
    H = np.cumsum(1.0 / n)
    rhs = H + np.exp(H) * np.log(H)
    slack = rhs - s
    k = int(np.argmin(slack[1:])) + 1
    return {"N": N, "holds": bool((slack >= -1e-9).all()), "min_slack_n": int(n[k]),
            "min_relative_slack": float(slack[k] / rhs[k])}


# ------------------------------------------------------------ Mertens
def mertens(N: int = 10**7) -> np.ndarray:
    """M(x) for 0 <= x <= N."""
    return np.cumsum(mobius_array(N).astype(np.int64))


def mertens_summary(N: int = 10**7) -> dict:
    M = mertens(N)
    x = np.arange(1, N + 1)
    r = np.abs(M[1:]) / np.sqrt(x)
    k = int(np.argmax(r[1:])) + 1
    return {"N": N, "max_abs_M_over_sqrt_x": float(r[k]), "at_x": int(x[k]), "M": M}


# ------------------------------------------------------------ Li / Keiper
def _log_xi_taylor(nmax: int):
    """Taylor coefficients of log xi(s) at s = 1, xi(s) = s/2 pi^(-s/2) Gamma(s/2) (s-1) zeta(s).

    (s-1) zeta(s) is expanded with the Stieltjes constants,
        (s-1) zeta(s) = 1 + sum_{n>=0} (-1)^n gamma_n / n! (s-1)^(n+1),
    and its logarithm is taken as a power series, avoiding the pole at s = 1.
    """
    a = [mp.mpf(1)] + [(-1) ** n * mp.stieltjes(n) / mp.factorial(n) for n in range(nmax)]
    b = [mp.mpf(0)] * (nmax + 1)                       # log of the series a
    for n in range(1, nmax + 1):
        b[n] = a[n] - mp.fsum(k * b[k] * a[n - k] for k in range(1, n)) / n
    # log(s/2) - (s/2) log pi + log Gamma(s/2), expanded exactly at s = 1
    c = [mp.log(mp.mpf(1) / 2) - mp.log(mp.pi) / 2 + mp.loggamma(mp.mpf(1) / 2)]
    for k in range(1, nmax + 1):
        d = (-1) ** (k - 1) * mp.factorial(k - 1)                 # d^k log s at s=1
        d += mp.polygamma(k - 1, mp.mpf(1) / 2) / mp.mpf(2) ** k   # d^k logGamma(s/2)
        if k == 1:
            d -= mp.log(mp.pi) / 2
        c.append(d / mp.factorial(k))
    return [b[k] + c[k] for k in range(nmax + 1)]


def li_coefficients(nmax: int = 20, dps: int = 60) -> np.ndarray:
    """Keiper-Li coefficients lambda_1..lambda_nmax from the Taylor series of log xi at s=1.

    lambda_n = n * sum_{i=0}^{n-1} C(n-1, i) a_{n-i},  log xi(s) = sum a_k (s-1)^k.
    Needs high precision because of cancellation; raise dps for larger nmax.
    """
    with mp.workdps(dps):
        a = _log_xi_taylor(nmax)
        lam = []
        for n in range(1, nmax + 1):
            lam.append(n * mp.fsum(mp.binomial(n - 1, i) * a[n - i] for i in range(n)))
        return np.array([float(v) for v in lam])


def li_from_zeros(n: int, zero_ordinates: np.ndarray) -> float:
    """lambda_n ~ sum over zeros rho, 1-rho of 1 - (1 - 1/rho)^n (truncated; underestimates)."""
    rho = 0.5 + 1j * np.asarray(zero_ordinates)
    terms = 1 - (1 - 1 / rho) ** n
    return float(2 * np.sum(terms.real))   # rho and its conjugate give equal real parts
