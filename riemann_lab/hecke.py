"""Hecke L-functions over Q (Dirichlet L-functions): the GL(1) case of Masullo's GRH claim.

Masullo's manuscript treats every unitary Hecke character of every number field. Over F = Q those are
the Dirichlet characters, and Dedekind zeta functions of abelian fields factor into them:
    zeta_{Q(zeta_q)}(s) = prod_{chi mod q} L(s, chi*)            (chi* the primitive character inducing chi)
This module provides what the checks need:

* primitive characters mod q (q an odd prime, 4 or 8), their parity, Gauss sum and root number;
* the completed L-function Lambda(s, chi) = (q/pi)^((s+a)/2) Gamma((s+a)/2) L(s, chi) and the real
  Hardy-type function Z_chi(t) = eps^(-1/2) e^{i theta_chi(t)} L(1/2 + it, chi);
* zeros on the critical line (sign changes of Z_chi) and an independent count of *all* zeros with
  0 < Im rho <= T in the strip, by the argument principle around [-1/2, 3/2] x [0, T];
* Weil's explicit formula for a primitive chi with a Gaussian test function;
* partial Euler products on the 1-line (Masullo App. B.7) and their GRH rate of convergence.

Everything is floating point (mpmath at 15-20 digits): numerical evidence, not certification.
"""
from __future__ import annotations

import cmath
import math
from dataclasses import dataclass

import mpmath as mp
import numpy as np
from scipy.optimize import brentq

from .primes import sieve


# ------------------------------------------------------------------ characters
@dataclass(frozen=True)
class Character:
    q: int
    label: str
    values: tuple            # chi(0), ..., chi(q-1) as complex numbers

    def __call__(self, n: int) -> complex:
        return self.values[n % self.q]

    @property
    def parity(self) -> int:  # a = 0 for even, 1 for odd characters
        return 0 if abs(self.values[self.q - 1] - 1) < 1e-12 else 1

    @property
    def is_real(self) -> bool:
        return all(abs(v.imag) < 1e-12 for v in self.values)

    def conj(self) -> "Character":
        return Character(self.q, self.label + "bar", tuple(v.conjugate() for v in self.values))

    def gauss_sum(self) -> complex:
        return sum(self.values[n] * cmath.exp(2j * math.pi * n / self.q) for n in range(1, self.q))

    def root_number(self) -> complex:
        return self.gauss_sum() / ((1j) ** self.parity * math.sqrt(self.q))


def _primitive_root(p: int) -> int:
    for g in range(2, p):
        if len({pow(g, k, p) for k in range(p - 1)}) == p - 1:
            return g
    raise ValueError(p)


def primitive_characters(q: int) -> list[Character]:
    """All primitive Dirichlet characters mod q for q an odd prime, 4 or 8 (one of each conjugate pair
    is NOT dropped: complex characters come with their conjugates)."""
    if q == 4:
        return [Character(4, "chi4", (0, 1, 0, -1))]
    if q == 8:
        return [Character(8, "chi8a", tuple(complex(v) for v in (0, 1, 0, -1, 0, -1, 0, 1))),   # (2/n)-type, even
                Character(8, "chi8b", tuple(complex(v) for v in (0, 1, 0, 1, 0, -1, 0, -1)))]   # odd
    g = _primitive_root(q)
    ind = {pow(g, k, q): k for k in range(q - 1)}
    roots = _roots_of_unity(q - 1)
    out = []
    for j in range(1, q - 1):
        vals = [0j] * q
        for n in range(1, q):
            vals[n] = roots[(j * ind[n]) % (q - 1)]
        out.append(Character(q, f"chi{q}_{j}", tuple(vals)))
    return out


def _roots_of_unity(m: int) -> list[complex]:
    """e^{2 pi i k/m}, k < m, with exact 0/+-1 components where they are exact, and w^(m-k) the exact
    conjugate of w^k, so that real characters are exactly real and chi, chibar are exact conjugates."""
    r = []
    for k in range(m):
        if 2 * k > m:
            r.append(r[m - k].conjugate())
            continue
        c, s_ = math.cos(2 * math.pi * k / m), math.sin(2 * math.pi * k / m)
        c = 0.0 if abs(c) < 1e-12 else (math.copysign(1.0, c) if abs(abs(c) - 1) < 1e-12 else c)
        s_ = 0.0 if abs(s_) < 1e-12 else (math.copysign(1.0, s_) if abs(abs(s_) - 1) < 1e-12 else s_)
        r.append(complex(c, s_))
    return r


def all_characters_mod_prime(q: int) -> list[Character]:
    """Every character mod a prime q (principal first); the non-principal ones are primitive."""
    principal = Character(q, f"chi{q}_0", tuple([0j] + [1 + 0j] * (q - 1)))
    return [principal] + primitive_characters(q)


# ------------------------------------------------------------------ L, Lambda, Z
def L(s, chi: Character):
    if s == 1:   # mpmath's Hurwitz route at the pole is unreliable for complex chi; use the digamma formula
        return -sum(chi.values[r] * mp.digamma(mp.mpf(r) / chi.q) for r in range(1, chi.q)) / chi.q
    return mp.dirichlet(s, list(chi.values))


def Lambda(s, chi: Character):
    a = chi.parity
    s = mp.mpc(s)
    return (chi.q / mp.pi) ** ((s + a) / 2) * mp.gamma((s + a) / 2) * L(s, chi)


def theta(t, chi: Character):
    a = chi.parity
    return mp.im(mp.loggamma((mp.mpf(0.5) + 1j * t + a) / 2)) + t / 2 * mp.log(chi.q / mp.pi)


def Z(t: float, chi: Character, rotation: complex | None = None) -> float:
    """Real on the line: eps^(-1/2) e^{i theta(t)} L(1/2+it). Returns the real part (imag ~ 1e-16)."""
    if rotation is None:
        rotation = 1 / cmath.sqrt(chi.root_number())
    v = mp.exp(1j * theta(t, chi)) * L(mp.mpc(0.5, t), chi) * rotation
    return float(mp.re(v))


def line_zeros(chi: Character, T: float, step: float = 0.1, t0: float = 0.0) -> np.ndarray:
    """Zeros 1/2 + i gamma with t0 < gamma <= T: sign changes of Z_chi on a grid, polished by bisection-secant."""
    rot = 1 / cmath.sqrt(chi.root_number())
    n = max(2, int(math.ceil((T - t0) / step)) + 1)
    ts = np.linspace(t0 + 1e-9, T, n)
    vals = np.array([Z(t, chi, rot) for t in ts])
    out = []
    f = lambda t: Z(float(t), chi, rot)
    for i in np.nonzero(np.sign(vals[:-1]) * np.sign(vals[1:]) < 0)[0]:
        out.append(brentq(f, ts[i], ts[i + 1], xtol=1e-13))
    return np.array(out)


def Z_derivative(t: float, chi: Character, h: float = 1e-5) -> float:
    rot = 1 / cmath.sqrt(chi.root_number())
    return (Z(t + h, chi, rot) - Z(t - h, chi, rot)) / (2 * h)


def winding_count(chi: Character, T: float, sigma0: float = -0.5, sigma1: float = 1.5,
                  max_darg: float = 0.5, max_step: float = 0.5) -> float:
    """Number of zeros of Lambda(s, chi) in [sigma0, sigma1] x [0, T] by the argument principle.

    Lambda is entire for primitive non-principal chi, and its zeros are exactly the non-trivial zeros
    of L. Left-edge values use the functional equation Lambda(s, chi) = eps Lambda(1 - s, chibar), so
    only Re s >= 1/2 is ever evaluated. Steps are halved until every arg increment is < max_darg.
    Returns the (real) winding number; an integer up to rounding if the contour is well resolved.
    """
    eps = chi.root_number()
    cb = chi.conj()

    def lam(s: complex):
        if s.real >= 0.5:
            return Lambda(s, chi)
        return eps * Lambda(1 - s, cb)

    corners = [complex(sigma0, 0), complex(sigma1, 0), complex(sigma1, T), complex(sigma0, T), complex(sigma0, 0)]
    total = 0.0
    for z0, z1 in zip(corners, corners[1:]):
        nseg = max(1, int(math.ceil(abs(z1 - z0) / max_step)))
        pts = [z0 + (z1 - z0) * k / nseg for k in range(nseg + 1)]
        vals = [lam(z) for z in pts]
        for k in range(nseg):
            stack = [(pts[k], pts[k + 1], vals[k], vals[k + 1], 0)]
            while stack:
                a, b, fa, fb, depth = stack.pop()
                d = float(mp.im(mp.log(fb / fa)))
                if abs(d) > max_darg and depth < 40:
                    m = (a + b) / 2
                    fm = lam(m)
                    stack.append((m, b, fm, fb, depth + 1))
                    stack.append((a, m, fa, fm, depth + 1))
                else:
                    total += d
    return total / (2 * math.pi)


def N_smooth(T: float, chi: Character) -> float:
    """Main term of N(T, chi): (theta(T) - theta(0))/pi, ~ (T/2pi) log(qT/(2 pi e))."""
    return float((theta(T, chi) - theta(0, chi)) / mp.pi)


# ------------------------------------------------------------------ explicit formula
def explicit_formula(chi: Character, zeros_chi: np.ndarray, zeros_chibar: np.ndarray, width: float,
                     extra_zeros=()) -> dict:
    """Weil's explicit formula for primitive chi and h(r) = exp(-(r/width)^2) (even in r).

        sum_rho h(gamma_rho) = (1/2pi) int h(r) [log(q/pi) + Re psi((1/2 + a + ir)/2)] dr
                               - sum_n Lambda(n)/sqrt(n) (chi(n) + chibar(n)) g(log n),
    g(x) = (1/2pi) int h(r) e^{-irx} dr = width/(2 sqrt(pi)) exp(-(width x / 2)^2).
    Zeros of L(s, chi) with gamma < 0 are the conjugates of the zeros of L(s, chibar) with gamma > 0,
    so the zero side is sum h(gamma) over zeros_chi plus over zeros_chibar. `extra_zeros` adds
    hypothetical zeros beta + i gamma (paired with 1 - beta + i gamma, as the functional equation forces).
    """
    a = chi.parity
    h = lambda r: mp.exp(-(r / width) ** 2)
    zero_side = sum(float(h(g)) for g in zeros_chi) + sum(float(h(g)) for g in zeros_chibar)
    for beta, gam in extra_zeros:          # rho = 1/2 + i(gamma - i(beta - 1/2)), so "gamma_rho" is complex
        for b in (beta, 1 - beta):
            zero_side += float(mp.re(h(mp.mpc(gam, -(b - 0.5)))))
    with mp.workdps(25):
        arch = mp.quad(lambda r: h(r) * (mp.log(chi.q / mp.pi) + mp.re(mp.digamma((0.5 + a + 1j * r) / 2))),
                       [-mp.inf, -width, 0, width, mp.inf]) / (2 * mp.pi)
    g = lambda x: width / (2 * math.sqrt(math.pi)) * math.exp(-(width * x / 2) ** 2)
    # prime powers until g(log n) < 1e-30
    xmax = math.exp(2 * math.sqrt(70) / width) + 10
    ps = sieve(int(xmax) + 2)
    prime_side = 0.0
    for p in ps:
        p = int(p)
        pk = p
        while pk <= xmax:
            c = chi(pk)
            prime_side += math.log(p) / math.sqrt(pk) * 2 * c.real * g(math.log(pk))
            pk *= p
    rhs = float(arch) - prime_side
    return {"zero_side": zero_side, "rhs": rhs, "residual": zero_side - rhs, "width": width}


# ------------------------------------------------------------------ Euler products on the 1-line
def euler_product_1line(chi: Character, xs, primes: np.ndarray | None = None) -> dict:
    """Partial Euler products P(x) = prod_{p <= x} (1 - chi(p)/p)^-1 at the points xs, vs L(1, chi).

    Under GRH, log P(x) - log L(1, chi) = O(log(x)^2 / sqrt(x)) (from the explicit formula for
    sum_{p<=x} chi(p) p^-1). Returns the scaled error |P/L - 1| sqrt(x) / log(x)^2 at each x.
    """
    xs = np.asarray(xs, dtype=float)
    if primes is None:
        primes = sieve(int(xs.max()) + 1)
    p = primes.astype(np.float64)
    vals = np.array([chi(int(v)) for v in range(chi.q)])
    c = vals[(primes % chi.q).astype(np.int64)]
    terms = -np.log1p(-c / p)                    # complex log of each local factor
    cum = np.cumsum(terms)
    L1 = complex(L(1, chi))
    idx = np.searchsorted(p, xs, side="right") - 1
    logP = cum[idx]
    err = np.abs(np.exp(logP - cmath.log(L1)) - 1)
    return {"x": xs, "L1": L1, "rel_error": err, "scaled": err * np.sqrt(xs) / np.log(xs) ** 2}


def nicolas_primorials(pmax: int = 10**7) -> dict:
    """Nicolas (1983): RH <=> N_k / phi(N_k) > e^gamma log log N_k for every primorial N_k = p_1...p_k.

    N_k/phi(N_k) = prod_{p <= p_k} (1 - 1/p)^-1 is the partial Euler product of zeta at s = 1 (Masullo
    App. B.7) and log N_k = theta(p_k). Returns the margins and the scaled margin
    (prod - e^gamma log theta) * sqrt(log N_k), which under RH stays positive and bounded.
    """
    p = sieve(pmax).astype(np.float64)
    lhs_log = np.cumsum(-np.log1p(-1 / p))
    theta = np.cumsum(np.log(p))
    eg = math.exp(np.euler_gamma)
    k0 = 1                                       # skip N_1 = 2 (log log 2 < 0 is fine, but start at 6)
    ratio = np.exp(lhs_log[k0:]) / (eg * np.log(theta[k0:]))
    margin = np.exp(lhs_log[k0:]) - eg * np.log(theta[k0:])
    return {"count": len(ratio), "min_ratio": float(ratio.min()), "holds": bool((margin > 0).all()),
            "p": p[k0:], "scaled_margin": margin * np.sqrt(theta[k0:])}
