"""The Hardy-Littlewood-Ramanujan reformulation of GRH: precise statements, and what numerics can see.

For a primitive character chi mod q (chi = None means zeta) let
    M_chi(x) = sum_n mu(n) chi(n)/n e^{-x/n^2} = sum_k (-x)^k / (k! L(2k+1, chi)).

What is proved (none of it is new):
* Mellin. Termwise integration (absolute convergence) gives, unconditionally,
      int_0^oo x^(s-1) (M_chi(x) - 1/L(1, chi)) dx = Gamma(s) / L(1 - 2s, chi),   -1 < Re s < 0.
  For zeta the constant is 1/zeta(1) = 0. Gamma(s)/L(1-2s) continues meromorphically; in 0 < Re s < 1/2 its
  poles are s = 0 (residue 1/L(1, chi), only for chi != 1), s = (1 - rho)/2 for the nontrivial zeros rho, and
  s = 1/2 for even chi (trivial zero w = 0). That the integral of M_chi itself converges on 0 < Re s < 1/4 is
  equivalent to GRH: unconditionally it is not known to converge at any s with Re s > 0.
* Equivalence. GRH for chi <=> M_chi(x) = O(x^(-1/4+eps)) for every eps > 0 (Hardy-Littlewood, Acta Math. 41
  (1918), sec. 2.5, for zeta; Garg-Maji, arXiv:2208.07596, Thm 2.2, for primitive chi and the family
  sum mu chi(n) n^-k e^{-x/n^l}). "<=" is elementary (growth => analytic Mellin transform => no poles); "=>"
  is a contour shift that uses 1/L(w) << |t|^eps on Re w >= 1/2 + eps, which GRH gives. Simple zeros are not
  needed for the O-bound; they are needed for the residue (zero) expansion used below.
* Hardy's form of the Master Theorem needs phi(z) = 1/(Gamma(z+1) L(2z+1)) analytic, with growth A < pi, on a
  closed half-plane Re z >= -delta. For delta < 1/4 that holds iff L(w) != 0 on Re w > 1 - 2 delta. Under GRH
  it holds for every delta < 1/4 (A = pi/2) but never uniformly on the open half-plane Re z > -1/4: |phi| blows
  up like (1/4 - delta)^-1 at the points z = (rho - 1)/2 (check `hardy_edge`). Unconditionally it holds for no
  delta > 0, so RMT alone does not give the Mellin identity to the right of Re s = 0.
* Reciprocity (character analogue of Ramanujan's alpha beta = pi; Dixit, Pacific J. Math. 255 (2012), Thms
  1.9-1.10, there with alpha beta = 1). Our normalisation, derived by a contour shift and the functional
  equation, with alpha beta = pi/q and eps the root number:
    even chi:  M_chi(a^2)  = conj(eps) sqrt(pi/q)/a (M_chibar(b^2) - 1/L(1, chibar)) + Z_chi(a^2)
                             + sqrt(pi) / (2 a L'(0, chi)),
    odd chi:   N_chi(a^2)  = conj(eps) sqrt(pi/q)/a N_chibar(b^2) + Z^odd_chi(a^2),
  where N_chi(x) = sqrt(x) sum mu chi(n)/n^2 e^{-x/n^2} (Mellin transform Gamma(s + 1/2)/L(1 - 2s, chi)) and
  Z, Z^odd are the zero sums sum_rho Gamma(s_rho) x^{-(1-rho)/2} / (2 L'(rho)), s_rho = (1-rho)/2 (+1/2 if odd).
  zeta (q = 1, eps = 1) gives Hardy-Littlewood's 2.516 (Ramanujan, lost notebook p. 332).

What numerics can see: the zero sum is weighted by |Gamma((1 - rho)/2)| ~ e^{-pi |gamma| / 4}, so at any x that
can be reached, M_chi(x) is determined by the lowest few zeros (`amplitude`) and an off-line zero above height
~30-40 changes M_chi by less than double precision (`sensitivity`).
"""
from __future__ import annotations

import math

import mpmath as mp
import numpy as np

from . import hecke
from .criteria import mobius_array

PLATT_TRUDGIAN_HEIGHT = 3.0001753328e12     # RH verified to this height (Platt-Trudgian, Bull. LMS 2021)


# ------------------------------------------------------------------ L helpers
def _exact_index(chi) -> list:
    """chi(n) = exp(2 pi i k_n / m) exactly (m = 2 q (q - 1)), recovered from the double values: double-precision
    roots of unity carry 1e-16 errors, which x^j T_{2j+1} amplifies past 1e15 at x = 1e11 (found in the first full
    run for the complex characters mod 7, 11, 13)."""
    m = 2 * chi.q * (chi.q - 1)
    out = []
    for v in chi.values:
        if abs(v) < 0.5:
            out.append(None)
        else:
            k = round(np.angle(v) * m / (2 * math.pi)) % m
            assert abs(np.exp(2j * math.pi * k / m) - v) < 1e-9
            out.append(k)
    return out, m


def exact_values(chi) -> list:
    """chi(0), ..., chi(q-1) as mpc at the working precision."""
    idx, m = _exact_index(chi)
    return [mp.mpc(0) if k is None else mp.expjpi(mp.mpf(2 * k) / m) for k in idx]


def L_of(chi):
    if chi is None:
        return lambda w: mp.zeta(w)

    def L(w):
        vals = exact_values(chi)
        if w == 1:
            return -mp.fsum(vals[r] * mp.digamma(mp.mpf(r) / chi.q) for r in range(1, chi.q)) / chi.q
        return mp.dirichlet(w, vals)
    return L


def Ld_of(chi):
    if chi is None:
        return lambda w: mp.zeta(w, derivative=1)
    return lambda w: mp.dirichlet(w, exact_values(chi), 1)


def inv_L1(chi):
    return mp.mpf(0) if chi is None else 1 / L_of(chi)(1)


# ------------------------------------------------------------------ power series
class Series:
    """sum_k (-x)^k / (k! L(2k + 1 + shift, chi)) with the 1/L values precomputed at dps digits.
    shift = 0: M_chi; shift = 1: sum mu chi(n)/n^2 e^{-x/n^2} (so N_chi(x) = sqrt(x) * Series(1)(x))."""

    def __init__(self, chi, shift: int = 0, xmax: float = 100.0):
        self.dps = int(25 + xmax / 2.3)
        self.kmax = int(3 * xmax + 60)
        Lf = L_of(chi)
        with mp.workdps(self.dps):
            self.inv = []  # exact character values: see _exact_index
            for k in range(self.kmax + 1):
                w = 2 * k + 1 + shift
                self.inv.append(mp.mpf(0) if (chi is None and w == 1) else 1 / Lf(w))
        self.xmax = xmax

    def __call__(self, x) -> mp.mpc:
        if float(x) > self.xmax * (1 + 1e-12):
            raise ValueError("x beyond the precomputed range")
        with mp.workdps(self.dps):
            x = mp.mpf(x)
            tot, term = mp.mpf(0), mp.mpf(1)
            for k in range(self.kmax + 1):
                tot += term * self.inv[k]
                term *= -x / (k + 1)
            return +tot


# ------------------------------------------------------------------ zero (residue) expansion
class ZeroExpansion:
    """sum over poles s0 of Gamma(s)/L(1-2s) (or Gamma(s+1/2)/L(1-2s) with odd_kernel) right of Re s = 0:
    nontrivial zeros rho -> s0 = (1 - rho)/2, trivial zeros w = -a - 2m -> s0 = (1 + a)/2 + m.
    Terms c x^{-s0}, c = Gamma(s0 [+1/2]) / (2 L'(1 - 2 s0)); extra = [(s0, c)] adds hypothetical terms."""

    def __init__(self, chi, zeros_pos, zeros_neg, odd_kernel: bool = False, n_trivial: int = 60,
                 trivial: bool = True, extra=()):
        Ld = Ld_of(chi)
        sh = mp.mpf(0.5) if odd_kernel else 0
        s0, c = [], []
        for g in list(zeros_pos) + [-g for g in zeros_neg]:
            rho = mp.mpc(0.5, g)
            s = (1 - rho) / 2
            s0.append(complex(s))
            c.append(complex(mp.gamma(s + sh) / (2 * Ld(rho))))
        self.s0 = np.array(s0, dtype=complex)
        self.c = np.array(c, dtype=complex)
        self.triv = []
        if trivial:
            a, m0 = (0, 1) if chi is None else (chi.parity, 0)
            for m in range(m0, m0 + n_trivial):
                w = -a - 2 * m
                s = mp.mpf(1 - w) / 2
                self.triv.append((s, mp.gamma(s + sh) / (2 * Ld(w))))
        self.extra = list(extra)

    def nontrivial(self, x) -> np.ndarray:
        x = np.atleast_1d(np.asarray(x, dtype=float))
        lx = np.log(x)[:, None]
        return np.sum(self.c[None, :] * np.exp(-self.s0[None, :] * lx), axis=1)

    def trivial_part(self, x: float) -> complex:
        x = mp.mpf(x)
        tot = mp.mpc(0)
        for s, c in self.triv:
            t = c * x ** (-s)
            tot += t
            if abs(t) < 1e-30 * max(abs(tot), mp.mpf(10) ** -300):
                break
        return complex(tot)

    def extra_part(self, x) -> np.ndarray:
        x = np.atleast_1d(np.asarray(x, dtype=float))
        out = np.zeros(x.shape, dtype=complex)
        for s, c in self.extra:
            out += c * np.exp(-s * np.log(x))
        return out

    def __call__(self, x) -> np.ndarray:
        x = np.atleast_1d(np.asarray(x, dtype=float))
        return self.nontrivial(x) + np.array([self.trivial_part(v) for v in x]) + self.extra_part(x)

    @property
    def amplitude(self) -> float:
        """A = sum_rho |c_rho|: under GRH with simple zeros, x^(1/4) |M - trivial terms| <= A for all x."""
        return float(np.sum(np.abs(self.c)))


# ------------------------------------------------------------------ Moebius sum with higher-order tails
_MU: dict = {}


def _mu(N: int) -> np.ndarray:
    if N not in _MU:
        _MU.clear()
        _MU[N] = mobius_array(N)
    return _MU[N]


class MobiusSum:
    """M_chi(x) = sum_{n <= N} mu chi(n)/n e^{-x/n^2} + sum_{j <= J} (-x)^j/j! T_{2j+1}
                + (rigorous remainder <= x^{J+1} / ((J+1)! (2J+2) N^{2J+2})),
    T_m = 1/L(m, chi) - sum_{n <= N} mu chi(n) n^{-m} (head n <= K in mpmath, the rest in float; J = 3 keeps x <= 1e11 at N = 1e7 below ~1e-11 x^(-1/4)).
    Returns (value, bound) with bound = Taylor remainder + a floating-point estimate (3e-15 per unit of the
    absolute sums involved; that part is an estimate, not a certificate)."""

    U = 3e-15

    def __init__(self, N: int, chi=None, J: int = 3, K: int = 20000, K_hi: int = 200000):
        self.N, self.J = N, J
        mu = _mu(N).astype(np.float64)
        n = np.arange(N + 1, dtype=np.float64)
        if chi is None:
            c = mu.astype(complex)
        else:
            vals = np.array(chi.values, dtype=complex)
            c = mu * vals[np.arange(N + 1) % chi.q]
        self.c, self.n = c, n
        Lf = L_of(chi)
        self.T, self.Terr = [], []
        # x^j T_{2j+1} must be accurate to ~1e-16 absolute: T_m is a difference of O(1) numbers, so the
        # mpmath part needs ~ 16 + j log10(x) digits, and the float remainder sum_{n > K_m} (relative error
        # ~1e-16 of K_m^(1-m)) needs K_m large for m >= 5 (K_hi = 2e5 for x up to 1e11).
        with mp.workdps(70):
            for j in range(J + 1):
                m = 2 * j + 1
                Km = min(N, K if m <= 3 else K_hi)
                Linv = inv_L1(chi) if m == 1 else 1 / Lf(m)
                if chi is None:
                    head = mp.fsum(int(mu[k]) * mp.mpf(k) ** (-m) for k in range(1, Km + 1) if mu[k])
                else:
                    ev = exact_values(chi)
                    head = mp.fsum(int(mu[k]) * ev[k % chi.q] * mp.mpf(k) ** (-m) for k in range(1, Km + 1) if mu[k])
                rest = complex(np.sum(c[Km + 1:] / n[Km + 1:] ** m))
                self.T.append(complex(mp.mpc(Linv) - head - rest))
                restabs = math.log(N / Km) + 1 if m == 1 else Km ** (1 - m) / (m - 1)
                self.Terr.append(self.U * restabs + 1e-60)
        self.abs1 = float(np.sum(np.abs(c[1:]) / n[1:]))

    def __call__(self, x: float) -> tuple[complex, float]:
        N, J = self.N, self.J
        e = np.exp(-x / self.n[1:] ** 2)
        val = np.sum(self.c[1:] / self.n[1:] * e)
        bound = self.U * self.abs1
        fact = 1.0
        for j in range(J + 1):
            if j:
                fact *= j
            val += (-x) ** j / fact * self.T[j]
            bound += x ** j / fact * self.Terr[j]
        bound += x ** (J + 1) / (math.factorial(J + 1) * (2 * J + 2) * float(N) ** (2 * J + 2))
        return complex(val), bound


# ------------------------------------------------------------------ 1. Mellin transform on -1 < Re s < 0
def mellin_strip(chi, s, series: Series, zexp: ZeroExpansion, X0: float) -> dict:
    """int_0^oo x^(s-1) (M(x) - c0) dx, c0 = 1/L(1, chi): power series on [0, X0], then the expansion
    termwise and in closed form on [X0, oo): int_X0^oo x^(s-1-s0) dx = X0^(s-s0)/(s0-s), -c0 part = c0 X0^s/s."""
    s = mp.mpc(s)
    c0 = mp.mpc(inv_L1(chi))
    with mp.workdps(20):
        f = lambda x: x ** (s - 1) * (series(x) - c0)
        # [0, 1] termwise: int_0^1 x^(s-1+k) dx = 1/(s+k), k >= 1 (the k = 0 term is c0, subtracted)
        head = mp.fsum((-1) ** k / (mp.factorial(k) * (s + k)) * series.inv[k] for k in range(1, series.kmax + 1))
        pts = [1] + [p for p in (5, 20, 50, 80) if p < X0] + [X0]
        head += mp.quad(f, pts)
        tail = c0 * mp.mpf(X0) ** s / s
        for s0, c in zip(zexp.s0, zexp.c):
            tail += mp.mpc(c) * mp.mpf(X0) ** (s - s0) / (s0 - s)
        for s0, c in zexp.triv:
            t = c * mp.mpf(X0) ** (s - s0) / (s0 - s)
            tail += t
            if abs(t) < 1e-25:
                break
        val = head + tail
        exact = mp.gamma(s) / L_of(chi)(1 - 2 * s)
    return {"s": complex(s), "value": complex(val), "exact": complex(exact),
            "rel_err": float(abs(val - exact) / abs(exact))}


# ------------------------------------------------------------------ 2. edge of Hardy's hypothesis
def hardy_edge(chi, zeros_pos, deltas=(0.2, 0.24, 0.249, 0.2499)) -> dict:
    """max |phi(-delta + i gamma/2)| over the zeros 1/2 + i gamma, phi(z) = 1/(Gamma(z+1) L(2z+1)):
    2z + 1 = 1 - 2 delta + i gamma sits at distance 1/2 - 2 delta from the zero, so |phi| ~ C/(1/4 - delta)."""
    Lf = L_of(chi)
    rows = []
    for d in deltas:
        m = 0.0
        for g in zeros_pos:
            z = mp.mpc(-d, g / 2)
            m = max(m, float(abs(1 / (mp.gamma(z + 1) * Lf(2 * z + 1)))))
        rows.append({"delta": d, "max_phi": m, "scaled": m * (0.25 - d)})
    return {"rows": rows}


def hardy_A(chi, v: float = -0.2, w_lo: float = 10.0, w_hi: float = 60.0, n: int = 101) -> float:
    """Least-squares slope of log|phi(v + iw)| in w: Hardy's A (needs A < pi). 1/Gamma gives pi/2; 1/L adds
    only o(w) (log-size oscillations) under GRH."""
    Lf = L_of(chi)
    ws = np.linspace(w_lo, w_hi, n)
    ys = [float(mp.log(abs(1 / (mp.gamma(mp.mpc(v + 1, w)) * Lf(mp.mpc(2 * v + 1, 2 * w)))))) for w in ws]
    return float(np.polyfit(ws, ys, 1)[0])


# ------------------------------------------------------------------ 4. reciprocity (alpha beta = pi/q)
def reciprocity(chi, alpha: float, zp, zn, zp_bar, zn_bar, ser=None, ser_bar=None) -> dict:
    """Both sides of the character analogue of Ramanujan's alpha beta = pi identity (module docstring).
    zp, zn: positive ordinates of the zeros of L(chi) above / |ordinates| below the axis; same for chibar."""
    q = 1 if chi is None else chi.q
    cb = None if chi is None else chi.conj()
    odd = 0 if chi is None else chi.parity
    eps = 1 if chi is None else complex(chi.root_number())
    beta = math.pi / q / alpha
    ser = ser or Series(chi, odd, xmax=max(alpha, beta) ** 2 + 1)
    ser_bar = ser_bar or Series(cb, odd, xmax=max(alpha, beta) ** 2 + 1)
    z = ZeroExpansion(chi, zp, zn, odd_kernel=bool(odd), trivial=False)
    with mp.workdps(30):
        a2, b2 = mp.mpf(alpha) ** 2, mp.mpf(beta) ** 2
        k = mp.conj(eps) * mp.sqrt(mp.pi / q) / alpha
        if not odd:
            lhs = ser(a2)
            rhs = k * (ser_bar(b2) - inv_L1(cb)) + complex(z.nontrivial(float(a2))[0])
            if chi is not None:
                rhs += mp.sqrt(mp.pi) / (2 * alpha * Ld_of(chi)(0))
        else:
            lhs = alpha * ser(a2)
            rhs = k * beta * ser_bar(b2) + complex(z.nontrivial(float(a2))[0])
    return {"alpha": alpha, "beta": beta, "lhs": complex(lhs), "rhs": complex(rhs), "diff": float(abs(lhs - rhs))}


# ------------------------------------------------------------------ 5. amplitude
def amplitude_sup(zexp: ZeroExpansion, umax: float = 1e5, du: float = 0.01, chunk: int = 200000) -> float:
    """sup over u = log x in [0, umax] of |sum_rho c_rho e^{i gamma u / 2}| = x^(1/4) |M - trivial terms|."""
    w = np.imag(-zexp.s0)            # x^{-s0} = x^{-1/4} e^{i gamma/2 log x}
    best = 0.0
    u0 = 0.0
    while u0 < umax:
        u = u0 + du * np.arange(chunk)
        f = np.exp(1j * np.outer(u, w)) @ zexp.c
        best = max(best, float(np.max(np.abs(f))))
        u0 += du * chunk
    return best


# ------------------------------------------------------------------ 6. sensitivity to an off-line zero
def offline_pair_terms(gamma: float, delta: float, Lprime: float = 1.0, real: bool = True):
    """Extra residue terms for a hypothetical quadruple rho = 1/2 +- delta +- i gamma (functional equation and,
    for a real character, conjugation). |L'(rho)| is unknown for a zero that does not exist: modelled as Lprime."""
    out = []
    signs = (1, -1) if real else (1,)
    for sg in signs:
        for b in (0.5 + delta, 0.5 - delta):
            rho = complex(b, sg * gamma)
            s0 = (1 - rho) / 2
            out.append((s0, complex(mp.gamma(s0)) / (2 * Lprime)))
    return out


def log10_x_to_see(gamma: float, delta: float, eta: float) -> float:
    """Smallest log10 x at which the dominant term of an off-line zero at 1/2 + delta + i gamma exceeds
    eta x^(-1/4): |Gamma((1 - rho)/2)|/2 x^((delta)/2) > eta, i.e. log x > (2/delta) (log(2 eta) - log|Gamma|)."""
    lg = float(mp.re(mp.loggamma(mp.mpc((0.5 - delta) / 2, -gamma / 2))))
    lx = (2 / delta) * (math.log(2 * eta) - lg)
    return max(0.0, lx / math.log(10))


def detection_height(delta: float, eta: float, log10_xmax: float) -> float:
    """Largest gamma whose off-line zero (model |L'| = 1) is visible at x <= 10^log10_xmax with precision eta."""
    lo, hi = 0.1, 1e4
    for _ in range(80):
        mid = (lo + hi) / 2
        if log10_x_to_see(mid, delta, eta) <= log10_xmax:
            lo = mid
        else:
            hi = mid
    return lo
