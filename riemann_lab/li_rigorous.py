"""Keiper-Li coefficients lambda_n to n ~ 10^4 with rigorous interval (ball) arithmetic.

Li (1997):  RH  <=>  lambda_n >= 0 for every n >= 1, where

    lambda_n = sum_rho [1 - (1 - 1/rho)^n]
             = n [z^n] log xi(1/(1 - z)),        xi(s) = s(s-1)/2 pi^(-s/2) Gamma(s/2) zeta(s).

Using xi(s) = xi(1-s) we expand at s = 0, where zeta is regular:

    xi(s) = (1 - s) pi^(-s/2) Gamma(1 + s/2) (-zeta(s)),     xi(0) = 1/2,
    log xi(1/(1-z)) = L(-z/(1-z)),   L(x) = log xi(x) as a power series at x = 0.

Backends
--------
* ``"arb"`` (default when python-flint is installed): every series operation is done in
  Arb ball arithmetic (Johansson), so each lambda_n comes back as an interval
  [mid - rad, mid + rad] that provably contains the true value. ``lambda_n > 0``
  certified this way is a theorem for that n, not a floating-point observation.
  Working precision is raised automatically until every ball is narrow.
* ``"mpmath"``: the same algorithm with mpmath's interval context ``mp.iv`` for the
  series algebra. mpmath's interval special functions are not fully rigorous, so
  results are labelled ``certified=False``; use it to cross-check Arb.

Under RH (Keiper 1992, Bombieri-Lagarias 1999),
    lambda_n = (n/2)(log n - 1 + gamma - log 2pi) + O(sqrt(n) log n),
while a zero off the line would eventually make lambda_n oscillate with
exponentially growing amplitude. ``asymptotic`` and ``summary`` check that trend.
"""
from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np

EULER_GAMMA = 0.5772156649015329

try:                                    # optional, gives true ball arithmetic
    import flint
    HAVE_FLINT = True
except Exception:                       # pragma: no cover
    flint = None
    HAVE_FLINT = False


@dataclass
class LiResult:
    n: np.ndarray            # 1..N
    mid: np.ndarray          # float midpoints
    rad: np.ndarray          # float radii (upper bounds on |true - mid|)
    lower: np.ndarray        # mid - rad, rounded down to float
    certified: bool          # True for the Arb backend
    prec_bits: int
    backend: str

    @property
    def all_positive(self) -> bool:
        return bool((self.lower > 0).all())

    @property
    def first_nonpositive(self):
        bad = np.nonzero(self.lower <= 0)[0]
        return int(self.n[bad[0]]) if bad.size else None


def asymptotic(n):
    """Leading behaviour of lambda_n under RH."""
    n = np.asarray(n, dtype=float)
    return n / 2 * (np.log(n) - 1 + EULER_GAMMA - math.log(2 * math.pi))


# --------------------------------------------------------------------- Arb backend
def _li_arb(N: int, prec: int):
    from flint import arb, arb_series, ctx
    old_prec, old_cap = ctx.prec, ctx.cap
    ctx.prec, ctx.cap = prec, N + 1
    try:
        x = arb_series([0, 1], prec=N + 1)
        L = (arb_series([1, -1], prec=N + 1).log()
             - x * (arb.pi().log() / 2)
             + (1 + x / 2).lgamma()
             + (-arb_series.zeta(x)).log())
        z = x
        w = -z * (1 - z).inv()                 # w = -z/(1-z), w(0) = 0
        F = L(w)
        c = F.coeffs()
        out = []
        for n in range(1, N + 1):
            v = c[n] * n if n < len(c) else arb(0)
            out.append(v)
        return out
    finally:
        ctx.prec, ctx.cap = old_prec, old_cap


def _arb_to_floats(vals):
    mid = np.array([float(v.mid()) for v in vals])
    rad = np.array([float(v.rad()) for v in vals])
    lower = np.array([float(v.lower()) for v in vals])
    return mid, rad, lower


# --------------------------------------------------------------------- mpmath backend
def _li_mpmath(N: int, dps: int):
    """Same series algebra with mp.iv intervals; Taylor coeffs of zeta/loggamma via mpmath."""
    import mpmath as mp
    iv = mp.iv
    old_iv = iv.dps
    iv.dps = dps
    with mp.workdps(dps + 20):
        # Taylor coefficients at 0: zeta^(k)(0)/k! from mpmath's derivative evaluation
        zc = [mp.zeta(0, 1, k) / mp.factorial(k) for k in range(N + 1)]
        a = [iv.mpf(-v) for v in zc]                     # -zeta(x), a[0] = 1/2
        b = [iv.mpf(0)] * (N + 1)                        # log of the series a
        b[0] = iv.log(a[0])
        for n in range(1, N + 1):
            s = iv.mpf(0)
            for k in range(1, n):
                s += k * b[k] * a[n - k]
            b[n] = (a[n] - s / n) / a[0]
        L = [iv.mpf(0)] * (N + 1)
        L[0] = b[0]
        for k in range(1, N + 1):
            L[k] = b[k] - iv.mpf(1) / k                  # log(1-x)
            # log Gamma(1+x/2) = -gamma x/2 + sum_{k>=2} (-1)^k zeta(k)/k (x/2)^k
            if k == 1:
                L[k] += -iv.mpf(mp.euler) / 2 - iv.log(iv.pi) / 2
            else:
                L[k] += (-1) ** k * iv.mpf(mp.zeta(k)) / k / iv.mpf(2) ** k
        # compose with w = -z/(1-z): w^k = (-1)^k z^k (1-z)^-k, [z^n] = (-1)^k C(n-1, k-1)
        out = []
        for n in range(1, N + 1):
            s = iv.mpf(0)
            for k in range(1, n + 1):
                s += (-1) ** k * iv.mpf(mp.binomial(n - 1, k - 1)) * L[k]
            out.append(n * s)
        mid = np.array([float(v.mid) for v in out])
        rad = np.array([float(v.delta) / 2 for v in out])
        lower = np.array([float(v.a) for v in out])
    iv.dps = old_iv
    return mid, rad, lower


# --------------------------------------------------------------------- public API
def li_coefficients_rigorous(N: int = 2000, backend: str | None = None,
                             rel_rad: float = 1e-20, max_tries: int = 6) -> LiResult:
    """lambda_1..lambda_N as certified enclosures.

    Precision starts at ~1.1 N + 128 bits (cancellation in the composition costs about
    N bits) and is doubled until every radius is below ``rel_rad * |mid|``.
    """
    backend = backend or ("arb" if HAVE_FLINT else "mpmath")
    if backend == "arb":
        if not HAVE_FLINT:
            raise ImportError("pip install python-flint for the Arb backend")
        prec = int(1.1 * N) + 128
        for _ in range(max_tries):
            vals = _li_arb(N, prec)
            mid, rad, lower = _arb_to_floats(vals)
            if np.all(np.isfinite(rad)) and np.all(rad <= rel_rad * np.abs(mid)):
                break
            prec *= 2
        return LiResult(np.arange(1, N + 1), mid, rad, lower, True, prec, "arb")
    if backend == "mpmath":                      # slow: meant for N <~ 100 cross-checks
        dps = int(0.35 * N) + 40
        mid, rad, lower = _li_mpmath(N, dps)
        return LiResult(np.arange(1, N + 1), mid, rad, lower, False, int(dps * 3.33), "mpmath-iv")
    raise ValueError(backend)


def summary(res: LiResult) -> dict:
    """Positivity plus the RH-predicted trend (lambda_n - asymptotic) / (sqrt(n) log n)."""
    n = res.n.astype(float)
    dev = (res.mid - asymptotic(n)) / (np.sqrt(n) * np.log(n + 1))
    tail = dev[len(dev) // 2:]
    return {"N": int(res.n[-1]), "backend": res.backend, "certified": res.certified,
            "prec_bits": res.prec_bits, "all_positive": res.all_positive,
            "first_nonpositive": res.first_nonpositive,
            "min_lambda": float(res.mid.min()), "lambda_1": float(res.mid[0]),
            "lambda_N": float(res.mid[-1]), "max_rel_radius": float(np.max(res.rad / np.abs(res.mid))),
            "max_abs_dev_second_half": float(np.abs(tail).max()),
            "lambda_N_over_asymptotic": float(res.mid[-1] / asymptotic(n[-1]))}
