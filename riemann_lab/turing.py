"""Turing's method: an exact zero count N(T) that never uses the argument principle.

S(t) = N(t) - theta(t)/pi - 1 has mean zero, and Turing (1953) bounded its integral:

    | int_{t1}^{t2} S(t) dt |  <=  a + b log(t2 / 2pi)        (t2 > t1 > 168 pi).

Turing's constants were a = 2.30, b = 0.128; Trudgian (2011) improved them to
a = 2.067, b = 0.059 (default here).

Let N~(t) be the count we *believe*: anchor at a Gram point g_n with N~(g_n) = n + 1
(Gram's law guess), and move N~ by one at every sign change of Z we found. If the
believed count is off by E = N(g_n) - N~(g_n) (an integer), then because every
missing zero is missing for good,

    N(t) - N~(t) >= E  for t > g_n,         N(t) - N~(t) <= E  for t < g_n.

Integrating S = S~ + (N - N~) over [g_n, g_n + h] and [g_n - h, g_n] with the bound:

    E <= ( a + b log((g_n + h)/2pi) - int_{g_n}^{g_n+h} S~ ) / h,
    E >= (-a - b log( g_n     /2pi) - int_{g_n-h}^{g_n} S~ ) / h.

If both bounds lie strictly inside (-1, 1) then E = 0: N(g_n) = n + 1 exactly.
Doing that at both ends of a window and counting sign changes in between
certifies every zero in the window is on the critical line, independently of
``zeta.N_exact`` (Backlund's argument-principle count used by ``zeros.verify_window``).

Rigour: sign changes are found with the float64 Riemann-Siegel Z. Each sign is
accepted only if |Z| exceeds Gabcke's bound on the Riemann-Siegel remainder after
the C0 term (0.127 t^(-3/4) for t >= 200) plus float round-off; doubtful signs are
recomputed with mpmath. This is careful numerics, not interval arithmetic.
"""
from __future__ import annotations

from dataclasses import dataclass, field

import mpmath as mp
import numpy as np

from . import zeta

TRUDGIAN = (2.067, 0.059)
TURING = (2.30, 0.128)


def gabcke_bound(t):
    """Gabcke (1979): |Z(t) - (main sum + C0 term)| <= 0.127 t^(-3/4) for t >= 200."""
    return 0.127 * np.asarray(t, dtype=float) ** -0.75


def theta_integral(t1: float, t2: float) -> float:
    """int_{t1}^{t2} (theta(t)/pi + 1) dt, from the antiderivative of Stirling's theta, in mpmath."""
    def F(t):
        t = mp.mpf(t)
        return (t**2 / 4 * mp.log(t / (2 * mp.pi)) - 3 * t**2 / 8 - mp.pi * t / 8 + mp.log(t) / 48
                - 7 / (11520 * t**2)) / mp.pi + t
    with mp.workdps(30):
        return float(F(t2) - F(t1))


def certified_sign_changes(T1: float, T2: float, oversample: int = 16):
    """Sign changes of Z on (T1, T2] where both bracketing signs exceed the error bound.

    Returns (zeros, n_doubtful_recomputed). Signs with |Z| below bound are recomputed
    with mpmath.siegelz at 20 digits.
    """
    mean_gap = 2 * np.pi / np.log(T2 / (2 * np.pi))
    step = mean_gap / oversample
    grid = np.arange(T1, T2 + step, step)
    vals = zeta.Z(grid)
    tol = gabcke_bound(grid) + 1e-11 * np.sqrt(grid)
    doubtful = np.nonzero(np.abs(vals) <= tol)[0]
    with mp.workdps(20):
        for i in doubtful:
            vals[i] = float(mp.siegelz(grid[i]))
    sgn = np.sign(vals)
    idx = np.nonzero(sgn[:-1] * sgn[1:] < 0)[0]
    z = 0.5 * (grid[idx] + grid[idx + 1])          # midpoints suffice for counting
    return z, len(doubtful)


@dataclass
class TuringAnchor:
    n: int                 # Gram index
    g: float               # Gram point
    h: float               # integration length on each side
    E_upper: float
    E_lower: float
    constants: tuple = TRUDGIAN

    @property
    def certified(self) -> bool:
        return -1 < self.E_lower and self.E_upper < 1

    @property
    def N(self) -> int | None:
        """N(g_n), certified when both bounds are in (-1, 1)."""
        return self.n + 1 if self.certified else None


def _S_tilde_integral(zs, g, n, a, b):
    """int_a^b S~(t) dt with N~(g) = n+1, N~ stepping at each found sign change zs."""
    zs = np.sort(zs)
    pts = zs[(zs > a) & (zs < b)]
    # N~(t) = n + 1 + #(zs in (g, t]) - #(zs in (t, g])
    edges = np.concatenate(([a], pts, [b]))
    below_g = np.searchsorted(zs, g, side="right")
    total = 0.0
    for lo, hi in zip(edges[:-1], edges[1:]):
        mid = 0.5 * (lo + hi)
        k = np.searchsorted(zs, mid, side="right")
        Nt = n + 1 + (k - below_g)
        total += Nt * (hi - lo)
    return total - theta_integral(a, b)


def turing_anchor(n: int, h_gram: int = 40, constants=TRUDGIAN, zs=None, guess: int | None = None) -> TuringAnchor:
    """Certify N(g_n) = n + 1 by Turing's method using h_gram Gram intervals on each side.

    ``guess`` replaces the believed count n + 1 (to see the method reject a wrong count:
    the E bounds then bracket guess's error instead of 0).
    """
    m = n if guess is None else guess - 1
    g = zeta.gram_point(n)
    if g - 2 * h_gram * 2 * np.pi / np.log(g / (2 * np.pi)) < 168 * np.pi:
        raise ValueError("Turing's bound needs t > 168 pi; pick a larger Gram index")
    glo, ghi = zeta.gram_point(n - h_gram), zeta.gram_point(n + h_gram)
    h = min(g - glo, ghi - g)
    if zs is None:
        zs, _ = certified_sign_changes(g - h - 1, g + h + 1)
    a, b = constants
    up = (a + b * np.log((g + h) / (2 * np.pi)) - _S_tilde_integral(zs, g, m, g, g + h)) / h
    lo = (-a - b * np.log(g / (2 * np.pi)) - _S_tilde_integral(zs, g, m, g - h, g)) / h
    return TuringAnchor(n, g, h, float(up), float(lo), constants)


@dataclass
class TuringWindow:
    left: TuringAnchor
    right: TuringAnchor
    sign_changes: int
    doubtful_recomputed: int
    oversample: int = 16
    N_backlund: tuple = field(default=(None, None))

    @property
    def expected(self):
        if self.left.N is None or self.right.N is None:
            return None
        return self.right.N - self.left.N

    @property
    def all_on_line(self) -> bool:
        return self.expected is not None and self.sign_changes == self.expected

    def __str__(self):
        bl = ""
        if self.N_backlund[0] is not None:
            agree = self.N_backlund == (self.left.N, self.right.N)
            bl = f"; argument-principle N = {self.N_backlund} ({'agrees' if agree else 'DISAGREES'})"
        v = "ALL ZEROS ON THE CRITICAL LINE" if self.all_on_line else "NOT CERTIFIED"
        return (f"Turing window [g_{self.left.n}, g_{self.right.n}] = [{self.left.g:.3f}, {self.right.g:.3f}]: "
                f"N = {self.left.N} .. {self.right.N} (E bounds left [{self.left.E_lower:+.3f}, {self.left.E_upper:+.3f}], "
                f"right [{self.right.E_lower:+.3f}, {self.right.E_upper:+.3f}]), "
                f"sign changes {self.sign_changes} vs expected {self.expected} (grid oversample {self.oversample}){bl} -> {v}")


def turing_verify(T1: float, T2: float, h_gram: int = 40, compare_backlund: bool = True,
                  max_refine: int = 4) -> TuringWindow:
    """Certify all zeros between the Gram points nearest T1 and T2 lie on the line (Turing's method).

    If an anchor fails (E bounds not in (-1, 1)) it is moved to the next Gram point; if
    the anchors are certified but fewer sign changes than N(g_n2) - N(g_n1) were found
    (two close zeros between grid points), the grid is refined 4x and the search repeated.
    """
    n1 = int(np.floor(float(mp.siegeltheta(T1)) / np.pi))
    n2 = int(np.ceil(float(mp.siegeltheta(T2)) / np.pi))
    over = 16
    for attempt in range(max_refine):
        g1, g2 = zeta.gram_point(n1 - h_gram), zeta.gram_point(n2 + h_gram)
        zs, nd = certified_sign_changes(g1 - 2, g2 + 2, oversample=over)
        left = turing_anchor(n1, h_gram, zs=zs)
        right = turing_anchor(n2, h_gram, zs=zs)
        inside = int(np.sum((zs > left.g) & (zs <= right.g)))
        win = TuringWindow(left, right, inside, nd, oversample=over)
        if win.all_on_line:
            break
        # anchors failing (Gram-law exceptions) -> move them; count short (close pairs) -> finer grid
        if not left.certified:
            n1 -= 1
        if not right.certified:
            n2 += 1
        over *= 4
    if compare_backlund:
        win.N_backlund = (zeta.N_exact(left.g), zeta.N_exact(right.g))
    return win
