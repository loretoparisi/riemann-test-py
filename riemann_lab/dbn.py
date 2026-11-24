"""The de Bruijn-Newman constant Lambda: heat flow of the Riemann xi function.

    H_t(z) = int_0^inf e^{t u^2} Phi(u) cos(z u) du,
    Phi(u) = sum_n (2 pi^2 n^4 e^{9u} - 3 pi n^2 e^{5u}) exp(-pi n^2 e^{4u}),
    H_0(z) = (1/8) xi(1/2 + i z/2)       (zeros of H_0 at z = 2 gamma).

There is a constant Lambda with: H_t has only real zeros  <=>  t >= Lambda.
    * RH  <=>  Lambda <= 0.
    * Rodgers-Tao (2018): Lambda >= 0 (Newman's conjecture), so RH <=> Lambda = 0.
    * de Bruijn (1950): Lambda <= 1/2;  Polymath 15 (2019): Lambda <= 0.22 (0.2 with more work).

How H_t is computed. dH/dt = -d^2H/dz^2, so H_t = exp(-t d^2/dz^2) H_0, i.e.
    t > 0:  H_t(z) = E[ H_0(z + i sqrt(2t) G) ],      t < 0:  H_t(z) = E[ H_0(z + sqrt(2|t|) G) ],
with G standard normal (check: E cos((z+sigma)u) = cos(zu) e^{-v u^2/2}). The
expectation is Gauss-Hermite quadrature and H_0 is mpmath's xi. ``H_direct`` evaluates
the defining integral as a cross-check for small |z|.

What is computed.
1. ``pair_collision_estimates`` (lower side). Backward in t, real zeros attract and a
   close pair collides and leaves the real axis. To first order, with
   d = z_{k+1} - z_k and A = sum over the other zeros of 1/(z_mid - z_j)^2,
       d(d^2)/dt = 8 - 4 A d^2   =>   collision at  t_c = log(1 - A d^2/2) / (4A) < 0,
   so the finite-window constant Lambda_X ~ max_k t_c is a numerical *estimate* of
   how close Lambda is to 0 from below. It should increase towards 0 with height
   (consistent with Rodgers-Tao). ``exact_collision_time`` finds the collision
   from H_t itself and checks the estimate.
2. ``rectangle_zero_free`` (upper side). If all zeros of H_{t0} satisfy |Im z| <= y0,
   then (de Bruijn) Lambda <= t0 + y0^2/2. We verify by the argument principle that
   H_{t0} has no zero in [0, X] x [y0, ymax] (ymax = sqrt(1 - 2 t0): by de Bruijn no
   zero lies above). This is the finite-range part of the Polymath 15 bound; the
   range x > X needs their asymptotic analysis and is NOT covered here.
"""
from __future__ import annotations

import math
from dataclasses import dataclass

import mpmath as mp
import numpy as np
from numpy.polynomial.hermite import hermgauss


def H0(z):
    """(1/8) xi(1/2 + iz/2), mpmath, any complex z."""
    s = mp.mpf(1) / 2 + 0.5j * mp.mpmathify(z)
    return s * (s - 1) / 16 * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def H(t: float, z, nodes: int = 40, dps: int = 20):
    """H_t(z) by Gauss-Hermite averaging of H_0 (real shifts for t < 0, imaginary for t > 0)."""
    if t == 0:
        with mp.workdps(dps):
            return H0(z)
    x, w = hermgauss(nodes)
    shift = math.sqrt(4 * abs(t)) * x        # sqrt(2v) x_i with v = 2|t|
    with mp.workdps(dps):
        z = mp.mpmathify(z)
        unit = 1j if t > 0 else 1
        return mp.fsum(wi * H0(z + unit * si) for wi, si in zip(w, shift)) / mp.sqrt(mp.pi)


def Phi(u):
    u = mp.mpf(u)
    return mp.nsum(lambda n: (2 * mp.pi**2 * n**4 * mp.exp(9 * u) - 3 * mp.pi * n**2 * mp.exp(5 * u))
                   * mp.exp(-mp.pi * n**2 * mp.exp(4 * u)), [1, mp.inf])


def H_direct(t: float, z, dps: int = 30):
    """The defining integral (slow; for |z| <~ 30 cross-checks)."""
    with mp.workdps(dps):
        return mp.quad(lambda u: mp.exp(t * u * u) * Phi(u) * mp.cos(z * u), [0, 0.5, 1, 2, 4])


# ------------------------------------------------------------------ lower side
def _tail_density(zm: float) -> float:
    """Zero density in the z = 2 gamma variable: dN/dz = log(z/4pi) / (4pi)."""
    return math.log(max(zm, 13.0) / (4 * math.pi)) / (4 * math.pi)


def pair_collision_estimates(gammas) -> dict:
    """First-order backward-heat-flow collision time for every adjacent pair of zeros.

    ``gammas`` must be a complete run of consecutive zero ordinates (e.g. from a
    verified window). Returns t_c per pair and the largest (closest to 0) one.
    """
    z = 2 * np.sort(np.asarray(gammas, dtype=float))
    d = np.diff(z)
    zm = 0.5 * (z[1:] + z[:-1])
    zlo, zhi = z[0], z[-1]
    # A_k = sum_{j not in pair} 1/(zm - z_j)^2 over z_j and -z_j, plus a density tail
    inv = 1.0 / (zm[:, None] - z[None, :]) ** 2
    idx = np.arange(len(zm))
    inv[idx, idx] = 0.0
    inv[idx, idx + 1] = 0.0
    A = inv.sum(axis=1) + (1.0 / (zm[:, None] + z[None, :]) ** 2).sum(axis=1)
    dens = np.array([_tail_density(v) for v in zm])
    A += dens * (1.0 / (zm - zlo + 1e-9) + 1.0 / (zhi - zm + 1e-9))
    arg = 1 - A * d**2 / 2
    tc = np.where(arg > 0, np.log(np.clip(arg, 1e-300, None)) / (4 * A), -np.inf)
    k = int(np.argmax(tc))
    return {"n_pairs": int(len(d)), "t_c": tc, "A": A, "d": d,
            "max_t_c": float(tc[k]), "at_gamma": float(zm[k] / 2), "gap_gamma": float(d[k] / 2)}


def exact_collision_time(g1: float, g2: float, t_lo: float, t_hi: float = 0.0,
                         xtol: float = 1e-5, nodes: int = 40) -> float:
    """Time at which the adjacent real zeros 2 g1 < 2 g2 of H_t collide (from H_t itself).

    Between the pair, H_t has one bump of fixed sign s0. F(t) = max_x s0 H_t(x) e^{pi x/8}
    over the pair is > 0 while both zeros are real and < 0 once they have left the
    axis; we solve F(t) = 0 with Brent's method. Needs F(t_hi) > 0 > F(t_lo).
    """
    from scipy.optimize import brentq, minimize_scalar
    za, zb = 2 * g1, 2 * g2
    pad = 0.25 * (zb - za)
    s0 = float(np.sign(mp.re(H0(0.5 * (za + zb)))))

    def F(t):
        f = lambda x: -s0 * float(mp.re(H(t, x, nodes=nodes)) * mp.exp(mp.pi * x / 8))
        r = minimize_scalar(f, bounds=(za - pad, zb + pad), method="bounded", options={"xatol": 1e-6})
        return -r.fun

    return brentq(F, t_lo, t_hi, xtol=xtol)


# ------------------------------------------------------------------ upper side
@dataclass
class RectangleResult:
    t0: float
    y0: float
    ymax: float
    X: float
    winding: float
    samples: int

    @property
    def zero_free(self) -> bool:
        return abs(self.winding) < 0.5

    @property
    def bound(self) -> float:
        return self.t0 + self.y0**2 / 2


def _arg_change(f, a: complex, b: complex, n0: int, max_depth: int = 14):
    """Total change of arg f along the segment a -> b, refining until steps are < pi/4."""
    ts = np.linspace(0, 1, n0 + 1)
    vals = [complex(f(a + (b - a) * t)) for t in ts]
    total, count = 0.0, len(vals)
    stack = [(ts[i], ts[i + 1], vals[i], vals[i + 1], 0) for i in range(n0)][::-1]
    while stack:
        t1, t2, v1, v2, depth = stack.pop()
        dphi = np.angle(v2 / v1)
        if abs(dphi) < math.pi / 4 or depth >= max_depth:
            total += dphi
            continue
        tm = 0.5 * (t1 + t2)
        vm = complex(f(a + (b - a) * tm))
        count += 1
        stack.append((tm, t2, vm, v2, depth + 1))
        stack.append((t1, tm, v1, vm, depth + 1))
    return total, count


def rectangle_zero_free(t0: float = 0.2, y0: float = 0.2, X: float = 200.0, nodes: int = 30,
                        dps: int = 20) -> RectangleResult:
    """Winding number of H_{t0} around [0, X] x [y0, ymax]; 0 means no zeros there."""
    ymax = math.sqrt(max(1 - 2 * t0, 0.0)) + 0.05
    if ymax <= y0:
        return RectangleResult(t0, y0, ymax, X, 0.0, 0)
    # normalise by the smooth size e^{-pi x / 8} so complex() stays in float range
    f = lambda z: H(t0, z, nodes=nodes, dps=dps) * mp.exp(mp.pi * mp.re(z) / 8)
    corners = [complex(0, y0), complex(X, y0), complex(X, ymax), complex(0, ymax)]
    total, samples = 0.0, 0
    for a, b in zip(corners, corners[1:] + corners[:1]):
        n0 = max(8, int(abs(b - a) * 4))
        d, c = _arg_change(f, a, b, n0)
        total += d
        samples += c
    return RectangleResult(t0, y0, ymax, X, total / (2 * math.pi), samples)


def window_estimate(T1: float, T2: float, polish: int = 5, edge: float = 0.1) -> dict:
    """Lambda_X-style estimate from the zeros in (T1, T2]: the latest backward collision.

    Zeros come from ``zeros.verify_window`` (so the list is complete); the ``polish``
    closest pairs are re-located with mpmath before the final estimate. Pairs within
    ``edge`` of either end are skipped (the density tail is cruder there).
    """
    from . import zeros
    if T1 < 100:
        low = zeros.first_zeros(29)                      # the 29 zeros below t = 100
        rep, high = zeros.verify_window(100, T2)
        g = np.concatenate((low[low > T1], high))
    else:
        rep, g = zeros.verify_window(T1, T2)
        if not rep.all_on_line:
            raise RuntimeError(f"window not verified: {rep}")
    p = pair_collision_estimates(g)
    zm = (g[1:] + g[:-1]) / 2
    ok = (zm > T1 + edge * (T2 - T1)) & (zm < T2 - edge * (T2 - T1))
    tc = np.where(ok, p["t_c"], -np.inf)
    g = g.copy()
    with mp.workdps(25):
        for k in np.argsort(-tc)[:polish]:
            for j in (k, k + 1):
                g[j] = float(mp.findroot(mp.siegelz, mp.mpf(g[j])))
    p = pair_collision_estimates(g)
    tc = np.where(ok, p["t_c"], -np.inf)
    k = int(np.argmax(tc))
    return {"T1": T1, "T2": T2, "pairs": int(ok.sum()), "max_t_c": float(tc[k]),
            "gamma_pair": (float(g[k]), float(g[k + 1])), "gap": float(g[k + 1] - g[k]),
            "median_t_c": float(np.median(tc[ok & np.isfinite(tc)]))}
