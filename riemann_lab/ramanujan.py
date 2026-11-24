"""Ramanujan's tools applied to Masullo's programme (numerical evidence, not proof).

1. Ramanujan's Master Theorem (RMT), in Hardy's rigorous form (Amdeberhan et al., Thm 3.2): if
   f(x) = sum_k lambda(k) (-x)^k / k! and phi(z) = lambda(z)/Gamma(z+1) is analytic on Re z >= -delta
   with |phi(v + iw)| < C e^{Pv + A|w|}, A < pi, then int_0^oo x^(s-1) f(x) dx = Gamma(s) lambda(-s).
   Masullo's Hardy-Sobolev norms (ch. 1.1.3, ch. 9) are L2 norms of Mellin transforms on vertical
   lines, so RMT gives them in closed form for any f with a Taylor expansion.
2. The Hardy-Littlewood-Ramanujan function
       M_chi(x) = sum_n mu(n) chi(n)/n e^{-x/n^2} = sum_k (-x)^k / (k! L(2k+1, chi)).
   RMT with lambda(k) = 1/L(2k+1, chi) gives its Mellin transform Gamma(s)/L(1-2s, chi), whose poles
   at s = (1 - rho)/2 are the zeros of L. GRH for chi <=> M_chi(x) = O(x^(-1/4+eps)) (Hardy-Littlewood
   1918 for zeta). Hardy's RMT hypothesis on the half-plane Re z > -1/4 holds iff L(w, chi) != 0 for
   Re w > 1/2, i.e. iff GRH holds for chi.
3. Ramanujan's highly composite numbers (unpublished part, RH-conditional), Robin's constant, and
   Ramanujan sums c_q(n).
4. Ramanujan's tau function and L(Delta, s) (GL2, outside Masullo's GL1 setting: his 14.3).
"""
from __future__ import annotations

import math

import mpmath as mp
import numpy as np

from . import hecke
from .criteria import colossally_abundant, mobius_array, sigma_array
from .primes import sieve

E_GAMMA = math.exp(np.euler_gamma)
ROBIN_LIMIT = E_GAMMA * (2 * math.sqrt(2) - 4 - np.euler_gamma + math.log(4 * math.pi))   # 1.3932...


# ===================================================================== 1. Master Theorem
def rmt_examples(chi: hecke.Character | None = None):
    """(name, f(x), lambda(k) for integer k, Gamma(s) lambda(-s), (lo, hi) validity strip)."""
    a = mp.mpf(1.5)
    ex = [("(1+x)^-1.5", lambda x: (1 + x) ** (-a),
           lambda k: mp.gamma(k + a) / mp.gamma(a),
           lambda s: mp.gamma(s) * mp.gamma(a - s) / mp.gamma(a), (0, 1.5)),
          ("zeta: 1/(e^x-1) - 1/x", lambda x: 1 / mp.expm1(x) - 1 / x,
           lambda k: mp.zeta(-k),
           lambda s: mp.gamma(s) * mp.zeta(s), (0, 1))]
    if chi is not None:
        q = chi.q
        vals = [mp.mpc(v) for v in chi.values]

        def f(x):
            return sum(vals[r % q] * mp.exp(-r * x) for r in range(1, q + 1)) / (-mp.expm1(-q * x))

        def lam(k):  # L(-k, chi) = -B_{k+1, chi}/(k+1),  B_{m,chi} = q^(m-1) sum_r chi(r) B_m(r/q)
            m = k + 1
            B = q ** (m - 1) * sum(vals[r % q] * mp.bernpoly(m, mp.mpf(r) / q) for r in range(1, q + 1))
            return -B / m

        ex.append((f"L(s, {chi.label})", f, lam, lambda s: mp.gamma(s) * hecke.L(s, chi), (0, 3)))
    return ex


def rmt_mellin(f, s, dps: int = 20, hi: float = 3.0, lam=None, x0: float = 0.5):
    """int_0^oo x^(s-1) f(x) dx.

    [x0, oo): quadrature in u = log x (the oscillation x^{it} becomes e^{itu}), unit pieces.
    (0, x0]: term-by-term from the Taylor coefficients, sum_k lambda(k) (-1)^k x0^{s+k} / (k! (s+k)),
    which only uses lambda at the integers (the input of the Master Theorem). Without `lam` the
    whole range is done by quadrature (needs f to be numerically stable near 0)."""
    s = mp.mpc(s)
    dps = dps + int(0.75 * abs(float(s.imag)))      # Gamma(s) lambda(-s) ~ e^{-pi|t|/2}: cancellation
    with mp.workdps(dps):
        hi_u = 6.0 if hi > 2.5 else min(160.0, float(dps * 2.4 / (hi - s.real)) + 5)
        if lam is None:
            lo_u = -float(dps * 2.4 / s.real) - 5
            nodes = [mp.mpf(v) for v in np.linspace(lo_u, hi_u, int(hi_u - lo_u) + 1)]
            return mp.quad(lambda u: mp.exp(s * u) * f(mp.exp(u)), nodes)
        u0 = mp.log(mp.mpf(x0))          # exactly log x0 at working precision (a float log is off by 1e-17)
        nodes = [u0] + [mp.mpf(v) for v in np.arange(math.ceil(float(u0)), hi_u + 1)]
        right = mp.quad(lambda u: mp.exp(s * u) * f(mp.exp(u)), nodes)
        x0 = mp.mpf(x0)
        left, k, fact, small = mp.mpc(0), 0, mp.mpf(1), 0
        while k < 2000:
            term = lam(k) * (-1) ** k * x0 ** (s + k) / (fact * (s + k))
            left += term
            k += 1
            fact *= k
            # lambda(k) can vanish (zeta(-2m) = 0): stop only after 4 consecutive negligible terms
            small = small + 1 if abs(term) < mp.mpf(10) ** (-dps - 2) * abs(left) else 0
            if small >= 4:
                break
        return left + right


def rmt_check(chi: hecke.Character, points=None) -> dict:
    """Quadrature of the Mellin integral vs Gamma(s) lambda(-s), at two working precisions; the
    Taylor coefficients lambda(k) of each f vs its series; and Hardy's growth exponent A."""
    if points is None:
        points = [mp.mpc(0.3, 0), mp.mpc(0.5, 2), mp.mpc(0.5, 7), mp.mpc(0.7, -3), mp.mpc(0.25, 10), mp.mpc(0.5, 14.13)]
    rows = []
    for name, f, lam, mel, (lo, hi) in rmt_examples(chi):
        errs, prec = [], []
        for s in points:
            if not lo < float(s.real) < hi:
                continue
            series = lam
            a = rmt_mellin(f, s, 20, hi, series)
            b = rmt_mellin(f, s, 30, hi, series)
            with mp.workdps(40):
                ref = mel(s)
            errs.append(float(abs(b - ref) / abs(ref)))
            prec.append(float(abs(a - b) / abs(b)))
        # Taylor coefficients: f(x) ~ sum lambda(k)(-x)^k/k! near 0 (5 terms at x = 0.05)
        x = mp.mpf("0.05")
        series = sum(lam(k) * (-x) ** k / mp.factorial(k) for k in range(25))
        taylor = float(abs(series - f(x)) / abs(f(x)))
        A = hardy_growth_exponent(lam, name)
        rows.append({"name": name, "max_rel_err": max(errs), "precision_agreement": max(prec),
                     "taylor_err": taylor, "A": A, "points": len(errs)})
    return {"rows": rows}


def hardy_growth_exponent(lam, name: str, v: float = -0.1, w1: float = 20, w2: float = 40) -> float | None:
    """Slope of log|phi(v + iw)| in |w|, phi(z) = lambda(z)/Gamma(z+1); Hardy needs A < pi.
    lambda is continued off the integers by its natural formula (Gamma, zeta, L)."""
    cont = {"(1+x)^-1.5": lambda z: mp.gamma(z + 1.5) / mp.gamma(1.5),
            "zeta: 1/(e^x-1) - 1/x": lambda z: mp.zeta(-z)}
    if name in cont:
        g = cont[name]
    else:
        return None   # filled in by the caller for L(s, chi)
    phi = lambda z: abs(g(z) / mp.gamma(z + 1))
    return float((mp.log(phi(mp.mpc(v, w2))) - mp.log(phi(mp.mpc(v, w1)))) / (w2 - w1))


def hardy_growth_exponent_L(chi: hecke.Character, v: float = -0.1, w1: float = 20, w2: float = 40) -> float:
    phi = lambda z: abs(hecke.L(-z, chi) / mp.gamma(z + 1))
    return float((mp.log(phi(mp.mpc(v, w2))) - mp.log(phi(mp.mpc(v, w1)))) / (w2 - w1))


def hardy_sobolev_check(a_exp: float = 1.5, c_lo: float = 0.3, c_hi: float = 1.1) -> dict:
    """Masullo's Hardy-Sobolev norm on R>0 (Haar measure dx/x), base I = [c_lo, c_hi], for
    f = (1+x)^-a. x side: int |f|^2 max(x^2a', x^2b') (1 + log^2 x)^{s/2} dx/x with s = 0 and s = 2;
    Mellin side via RMT: Mf(s) = Gamma(s)Gamma(a-s)/Gamma(a) and Plancherel on Re s = c,
        int |f|^2 x^{2c} log(x)^{2k} dx/x = (1/2pi) int |d^k/ds^k Mf(c + it)|^2 dt.
    Returns both sides of each Plancherel identity and the norm-equivalence sandwich."""
    a = mp.mpf(a_exp)
    f = lambda x: (1 + x) ** (-a)
    M = lambda s: mp.gamma(s) * mp.gamma(a - s) / mp.gamma(a)
    dM = lambda s: M(s) * (mp.digamma(s) - mp.digamma(a - s))
    out = []
    with mp.workdps(25):
        for c in (c_lo, c_hi):
            for k, Mk in ((0, M), (1, dM)):
                xs = mp.quad(lambda x: f(x) ** 2 * x ** (2 * c - 1) * mp.log(x) ** (2 * k), [0, 1, mp.inf])
                ms = mp.quad(lambda t: abs(Mk(mp.mpc(c, t))) ** 2, [-mp.inf, -10, 0, 10, mp.inf]) / (2 * mp.pi)
                out.append({"c": c, "k": k, "x_side": float(xs), "mellin_side": float(ms),
                            "rel_diff": float(abs(xs - ms) / xs)})
        # the norm with weight max(x^2a, x^2b) for s = 0: x^(2 c_hi) above 1, x^(2 c_lo) below
        norm2 = mp.quad(lambda x: f(x) ** 2 * max(x ** (2 * c_lo), x ** (2 * c_hi)) / x, [0, 1, mp.inf])
    edge = [r["x_side"] for r in out if r["k"] == 0]
    sandwich = float(norm2) <= sum(edge) * (1 + 1e-12) and sum(edge) <= 2 * float(norm2) * (1 + 1e-12)
    return {"rows": out, "norm2": float(norm2), "edge_sum": sum(edge), "sandwich": sandwich}


# ===================================================================== 2. Hardy-Littlewood-Ramanujan
def hl_series(x, chi: hecke.Character | None = None, dps: int | None = None):
    """M_chi(x) = sum_k (-x)^k/(k! L(2k+1, chi)) (zeta if chi is None), in exact-enough precision."""
    x = mp.mpf(x)
    if dps is None:
        dps = int(20 + float(x) / 2.3)   # terms reach e^x / sqrt(2 pi x)
    with mp.workdps(dps):
        Lf = (lambda w: mp.zeta(w)) if chi is None else (lambda w: hecke.L(w, chi))
        tot, term, k = mp.mpf(0), mp.mpf(1), 0
        while True:
            t = term / Lf(2 * k + 1) if k > 0 else term / (Lf(1) if chi is not None else mp.inf)
            tot += t
            k += 1
            term *= -x / k
            if k > 3 * x + 30 and abs(term) < mp.mpf(10) ** (-dps + 5):
                break
        return complex(tot)


class MobiusTable:
    """mu(n) chi(n) for n <= N with the tails 1/L(1, chi) - sum_{n<=N} and 1/L(3, chi) - sum_{n<=N}."""

    def __init__(self, N: int, chi: hecke.Character | None = None):
        self.N = N
        mu = mobius_array(N).astype(np.float64)
        n = np.arange(N + 1, dtype=np.float64)
        with mp.workdps(30):
            if chi is None:
                c = mu.astype(complex)
                L1inv, L3inv = mp.mpf(0), 1 / mp.zeta(3)
            else:
                vals = np.array(chi.values, dtype=complex)
                c = mu * vals[np.arange(N + 1) % chi.q]
                L1inv, L3inv = 1 / hecke.L(1, chi), 1 / hecke.L(3, chi)
        self.c = c
        self.n = n
        # tails sum_{n > N}: head n <= 2000 in mpmath, the small remainder in float, then subtract,
        # so that x * tail3 keeps ~1e-25 absolute accuracy (a plain float difference gives 1e-16 x)
        K = min(N, 2000)
        with mp.workdps(30):
            h1 = mp.fsum(mp.mpc(c[k]) / k for k in range(1, K + 1))
            h3 = mp.fsum(mp.mpc(c[k]) / mp.mpf(k) ** 3 for k in range(1, K + 1))
            r1 = complex(np.sum(c[K + 1:] / n[K + 1:]))
            r3 = complex(np.sum(c[K + 1:] / n[K + 1:] ** 3))
            self.tail1 = complex(L1inv - h1 - r1)
            self.tail3 = complex(L3inv - h3 - r3)

    def __call__(self, x: float) -> tuple[complex, float]:
        """M(x) and a rigorous bound on the part of the n > N tail that is not summed exactly."""
        N = self.N
        n0 = min(N, int(math.sqrt(x)) + 1)
        nn = self.n[1:n0 + 1]
        head = np.sum(self.c[1:n0 + 1] / nn * np.exp(-x / nn**2))
        nm = self.n[n0 + 1:]
        y = x / nm**2
        mid = np.sum(self.c[n0 + 1:] / nm * np.exp(-y))
        val = head + mid + self.tail1 - x * self.tail3      # n > N: e^{-y} = 1 - y + O(y^2)
        bound = x**2 / (8 * N**4)
        return complex(val), bound


def hl_zero_expansion(x: float, chi: hecke.Character | None, zeros_pos, zeros_neg, n_trivial: int = 400) -> complex:
    """RMT + residues:  M_chi(x) = sum_rho Gamma((1-rho)/2) x^{-(1-rho)/2} / (2 L'(rho))
                                  + sum_m Gamma(s_m) x^{-s_m} / (2 L'(1 - 2 s_m)),
    s_m the poles from the trivial zeros w = -a - 2m of L(w, chi) (m >= 1 for zeta, m >= 0 for chi).
    zeros_pos: ordinates gamma > 0 of zeros 1/2 + i gamma of L(s, chi); zeros_neg: |gamma| of those below."""
    x = mp.mpf(x)
    if chi is None:
        Ld = lambda w: mp.zeta(w, derivative=1)
        a, m0 = 0, 1
    else:
        Ld = lambda w: mp.dirichlet(w, list(chi.values), 1)
        a, m0 = chi.parity, 0
    tot = mp.mpc(0)
    for g in list(zeros_pos) + [-g for g in zeros_neg]:
        rho = mp.mpc(0.5, g)
        s0 = (1 - rho) / 2
        tot += mp.gamma(s0) * x ** (-s0) / (2 * Ld(rho))
    for m in range(m0, m0 + n_trivial):
        w = -a - 2 * m
        s0 = mp.mpf(1 - w) / 2
        term = mp.gamma(s0) * x ** (-s0) / (2 * Ld(w))
        tot += term
        if abs(term) < 1e-30 * max(abs(tot), 1e-300):
            break
    return complex(tot)


def ramanujan_alpha_beta(alpha: float, zeros_pos, mob: MobiusTable | None = None) -> dict:
    """Ramanujan (lost notebook p. 332; Hardy-Littlewood 1918, eq. 2.516): for alpha beta = pi,
       sqrt(alpha) sum mu(n)/n e^{-(alpha/n)^2} - sqrt(beta) sum mu(n)/n e^{-(beta/n)^2}
           = -1/(2 sqrt(beta)) sum_rho Gamma((1-rho)/2) beta^rho / zeta'(rho),
    assuming the zeros are simple. Both sides by independent means (power series / zero sum)."""
    beta = math.pi / alpha
    lhs = math.sqrt(alpha) * hl_series(alpha**2).real - math.sqrt(beta) * hl_series(beta**2).real
    rhs = mp.mpc(0)
    for g in list(zeros_pos) + [-g for g in zeros_pos]:
        rho = mp.mpc(0.5, g)
        rhs += mp.gamma((1 - rho) / 2) * mp.mpf(beta) ** rho / mp.zeta(rho, derivative=1)
    rhs = -rhs / (2 * math.sqrt(beta))
    return {"alpha": alpha, "beta": beta, "lhs": lhs, "rhs": complex(rhs), "diff": abs(lhs - complex(rhs))}


# ===================================================================== 3. HCN / Robin / Ramanujan sums
def robin_ramanujan_constant(count: int = 90000, pmax: int = 2 * 10**6) -> dict:
    """(e^gamma log log n - sigma(n)/n) sqrt(log n) along the colossally abundant numbers.
    Ramanujan (HCN, unpublished part) and Robin (1984): under RH this tends to e^gamma(2 sqrt 2 - 4 -
    gamma + log 4 pi) = 1.3932 at CA numbers; if RH fails it is negative for infinitely many n."""
    L, S = [], []
    for logn, logsig, _ in colossally_abundant(count, pmax):
        if logn > math.log(5040) + 1e-9:
            L.append(logn)
            S.append((E_GAMMA * math.log(logn) - math.exp(logsig)) * math.sqrt(logn))
    return {"log_n": np.array(L), "scaled": np.array(S), "limit": ROBIN_LIMIT}


def ramanujan_sum(q: int, n: int) -> int:
    """c_q(n) = sum_{d | gcd(q, n)} mu(q/d) d."""
    g = math.gcd(q, n)
    tot = 0
    for d in range(1, g + 1):
        if g % d == 0:
            tot += _mu(q // d) * d
    return tot


def _mu(n: int) -> int:
    r, p = 1, 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            if n % p == 0:
                return 0
            r = -r
        p += 1
    return -r if n > 1 else r


def ramanujan_sum_direct(q: int, n: int) -> float:
    return sum(math.cos(2 * math.pi * a * n / q) for a in range(1, q + 1) if math.gcd(a, q) == 1)


def ramanujan_sigma_expansion(n: int, Q: int) -> float:
    """zeta(2) sum_{q<=Q} c_q(n)/q^2  (Ramanujan 1918: = sigma(n)/n as Q -> oo)."""
    return math.pi**2 / 6 * sum(ramanujan_sum(q, n) / q**2 for q in range(1, Q + 1))


def ramanujan_pnt_sums(N: int = 10**7) -> dict:
    """Ramanujan: sum_q c_q(n)/q = 0 for every n (equivalent to the PNT). The partial sums are
    sum_{d | n} m(Q/d) with m(x) = sum_{k <= x} mu(k)/k, so their rate is that of m(x): RH gives
    m(x) = O(x^(-1/2+eps)). Returns m(x) sqrt(x) on a log grid and its growth exponent."""
    mu = mobius_array(N).astype(np.float64)
    k = np.arange(1, N + 1, dtype=np.float64)
    m = np.cumsum(mu[1:] / k)
    xs = np.unique(np.logspace(3, math.log10(N), 300).astype(np.int64))
    vals = m[xs - 1]
    expo = np.log(np.maximum(np.abs(vals), 1e-300)) / np.log(xs)
    return {"x": xs, "m": vals, "scaled": vals * np.sqrt(xs), "max_scaled": float(np.abs(vals * np.sqrt(xs)).max()),
            "max_exponent": float(expo.max()), "m_full": m}


# ===================================================================== 4. tau and L(Delta, s)
def tau(N: int) -> list[int]:
    """tau(1..N) from Delta = q prod (1-q^n)^24 = q (prod (1-q^n)^3)^8, Jacobi: prod (1-q^n)^3 =
    sum_k (-1)^k (2k+1) q^{k(k+1)/2}. Exact integers (python-flint)."""
    import flint
    c = [0] * N
    k = 0
    while k * (k + 1) // 2 < N:
        c[k * (k + 1) // 2] = (-1) ** k * (2 * k + 1)
        k += 1
    P = flint.fmpz_poly(c)
    D = P.pow_trunc(8, N)
    co = [int(v) for v in D.coeffs()] + [0] * N
    return [0] + co[:N]          # tau[n] for n = 1..N  (tau[1] = 1)


def tau_checks(N: int = 2000) -> dict:
    t = tau(N)
    sig11 = [0] * (N + 1)
    for d in range(1, N + 1):
        d11 = d**11
        for m in range(d, N + 1, d):
            sig11[m] += d11
    mult = all(t[m * n] == t[m] * t[n] for m in range(2, 45) for n in range(2, 45)
               if math.gcd(m, n) == 1 and m * n <= N)
    ps = [int(p) for p in sieve(N)]
    hecke_ok = all(t[p * p] == t[p] ** 2 - p**11 for p in ps if p * p <= N)
    hecke3 = all(t[p**3] == t[p] * t[p * p] - p**11 * t[p] for p in ps if p**3 <= N)
    cong = all((t[n] - sig11[n]) % 691 == 0 for n in range(1, N + 1))
    x = np.array([t[p] / (2 * p**5.5) for p in ps])
    deligne = float(np.abs(x).max())
    moments = {k: float(np.mean((2 * x) ** k)) for k in (2, 4, 6)}
    st = {2: 1, 4: 2, 6: 5}
    st_var = {2: 2 - 1, 4: 14 - 4, 6: 132 - 25}
    st_ok = all(abs(moments[k] - st[k]) < 3 * math.sqrt(st_var[k] / len(ps)) for k in st)
    return {"tau": t, "multiplicative": mult, "hecke_p2": hecke_ok, "hecke_p3": hecke3, "congruence_691": cong,
            "max_|tau(p)|/(2p^5.5)": deligne, "sato_tate_moments": moments, "sato_tate_ok": st_ok,
            "nprimes": len(ps), "tau_small": t[1:11]}


class DeltaL:
    """Lambda(s) = (2pi)^-s Gamma(s) L(Delta, s) = sum_n tau(n) [(2 pi n)^-s Gamma(s, 2 pi n)
    + (2 pi n)^(s-12) Gamma(12-s, 2 pi n)]: entire, Lambda(s) = Lambda(12 - s), real on Re s = 6."""

    def __init__(self, nterms: int = 80):
        self.t = tau(nterms + 1)
        self.nterms = nterms

    def Lambda(self, s, dps: int | None = None):
        s = mp.mpc(s)
        if dps is None:
            dps = int(25 + 0.7 * abs(float(s.imag)))
        with mp.workdps(dps):
            tot = mp.mpc(0)
            for n in range(1, self.nterms + 1):
                x = 2 * mp.pi * n
                term = self.t[n] * (x ** (-s) * mp.gammainc(s, x) + x ** (s - 12) * mp.gammainc(12 - s, x))
                tot += term
                if n > 5 and abs(term) < abs(tot) * mp.mpf(10) ** (-dps + 3):
                    break
            return tot

    def Z(self, t: float) -> float:
        """Lambda(6 + it) / |(2 pi)^-s Gamma(s)|: real, same sign changes as L(Delta, 6 + it)."""
        s = mp.mpc(6, t)
        with mp.workdps(int(25 + 0.7 * abs(t))):
            v = self.Lambda(s) / abs((2 * mp.pi) ** (-s) * mp.gamma(s))
            return float(mp.re(v))

    def zeros(self, T: float, step: float = 0.1) -> np.ndarray:
        from scipy.optimize import brentq
        ts = np.arange(0.05, T + step / 2, step)
        v = np.array([self.Z(t) for t in ts])
        return np.array([brentq(self.Z, ts[i], ts[i + 1], xtol=1e-12)
                         for i in np.nonzero(np.sign(v[:-1]) * np.sign(v[1:]) < 0)[0]])

    def winding(self, T: float, sigma0: float = 4.5, sigma1: float = 7.5, max_darg: float = 0.5,
                max_step: float = 0.5) -> float:
        lam = lambda s: self.Lambda(s) if s.real >= 6 else self.Lambda(12 - s)
        corners = [complex(sigma0, 0), complex(sigma1, 0), complex(sigma1, T), complex(sigma0, T), complex(sigma0, 0)]
        total = 0.0
        for z0, z1 in zip(corners, corners[1:]):
            nseg = max(1, int(math.ceil(abs(z1 - z0) / max_step)))
            pts = [z0 + (z1 - z0) * k / nseg for k in range(nseg + 1)]
            vals = [lam(z) for z in pts]
            for k in range(nseg):
                stack = [(pts[k], pts[k + 1], vals[k], vals[k + 1], 0)]
                while stack:
                    a, b, fa, fb, d_ = stack.pop()
                    d = float(mp.im(mp.log(fb / fa)))
                    if abs(d) > max_darg and d_ < 40:
                        m = (a + b) / 2
                        fm = lam(m)
                        stack += [(m, b, fm, fb, d_ + 1), (a, m, fa, fm, d_ + 1)]
                    else:
                        total += d
        return total / (2 * math.pi)
