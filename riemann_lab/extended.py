"""The extended checks (Turing, de Bruijn-Newman, Nyman-Beurling, Weil, rigorous Li, Riesz,
Redheffer) with explicit convergence / consistency verdicts.

``run(quick)`` returns a list of ``Check`` records and prints a report. Each check
states what theory predicts and whether the numbers agree, including a
convergence test (two precisions, two node counts, two truncations, ...).
"""
from __future__ import annotations

import math
import time
from dataclasses import dataclass, field

import numpy as np

from . import dbn, li_rigorous, nyman_beurling, riesz_redheffer, turing, weil, zeros


@dataclass
class Check:
    name: str
    ok: bool
    lines: list = field(default_factory=list)
    seconds: float = 0.0

    def __str__(self):
        head = f"[{self.name}] {'CONSISTENT' if self.ok else 'NOT CONVERGED / INCONSISTENT'}  ({self.seconds:.1f}s)"
        return "\n".join([head] + ["    " + ln for ln in self.lines])


def _timed(fn):
    t = time.time()
    c = fn()
    c.seconds = time.time() - t
    return c


# ---------------------------------------------------------------- 1. Turing
def check_turing(quick: bool) -> Check:
    wins = [(1000, 1200), (1e5, 1.01e5)] + ([] if quick else [(1e6, 1.0005e6), (1e7, 1.0001e7)])
    lines, ok = [], True
    for T1, T2 in wins:
        w = turing.turing_verify(T1, T2, compare_backlund=T2 < 2e6)
        lines.append(str(w))
        ok &= w.all_on_line and (w.N_backlund[0] is None or w.N_backlund == (w.left.N, w.right.N))
    # robustness: Turing's original (weaker) constants must also certify, and a wrong guess must fail
    a = turing.turing_anchor(70000, constants=turing.TURING)
    bad = turing.turing_anchor(70000, guess=70002)
    lines.append(f"anchor g_70000 with Turing's 1953 constants: E in [{a.E_lower:+.3f}, {a.E_upper:+.3f}] -> N = {a.N}")
    lines.append(f"wrong guess N(g_70000) = 70002: E in [{bad.E_lower:+.3f}, {bad.E_upper:+.3f}] -> rejected: {not bad.certified}")
    ok &= a.certified and not bad.certified
    return Check("turing", ok, lines)


# ---------------------------------------------------------------- 2. de Bruijn-Newman
def check_de_bruijn_newman(quick: bool) -> Check:
    lines, ok = [], True
    errs = []
    for t, z in [(0.2, 10), (-0.3, 25 + 0.3j), (-1.0, 40.0)]:
        a, b = complex(dbn.H(t, z, nodes=40)), complex(dbn.H_direct(t, z))
        errs.append(abs(a - b) / abs(b))
    lines.append(f"H_t by Gauss-Hermite heat flow vs defining integral: max rel. error {max(errs):.1e}")
    ok &= max(errs) < 1e-9
    wins = [(14, 1000), (1e4, 1.1e4), (6900, 7100)] + ([] if quick else [(1e5, 1.02e5), (1e6, 1.002e6)])
    est = []
    for T1, T2 in wins:
        e = dbn.window_estimate(T1, T2, edge=0.0 if T1 == 6900 else 0.1)
        est.append(e)
        lines.append(f"zeros in ({T1:g}, {T2:g}]: latest backward collision t_c = {e['max_t_c']:+.3e} "
                     f"at the pair {e['gamma_pair'][0]:.4f}, {e['gamma_pair'][1]:.4f} (gap {e['gap']:.4f})")
    ok &= all(e["max_t_c"] < 0 for e in est)
    trend = [e["max_t_c"] for e in est if e["T1"] != 6900]
    mono = all(b > a for a, b in zip(trend, trend[1:]))
    lines.append(f"trend with height {['%.2e' % v for v in trend]}: increasing towards 0: {mono}")
    ok &= mono
    lehmer = [e for e in est if e["T1"] == 6900][0]
    lines.append(f"Lehmer's pair t = 7005.06: estimate {lehmer['max_t_c']:+.2e} vs the rigorous bound Lambda > -0.0991 "
                 f"(Csordas-Ruttan-Varga 1991) from that pair: consistent {lehmer['max_t_c'] > -0.0991}")
    ok &= lehmer["max_t_c"] > -0.0991
    # exact collision from H_t for the latest-colliding pair below t = 300
    g = zeros.first_zeros(29)
    _, hi = zeros.verify_window(100, 300)
    g = np.concatenate((g, hi))
    p = dbn.pair_collision_estimates(g)
    k = int(np.argmax(p["t_c"][3:-3])) + 3
    exact = dbn.exact_collision_time(g[k], g[k + 1], 3 * p["t_c"][k], 0.0)
    rel = abs(exact - p["t_c"][k]) / abs(exact)
    lines.append(f"pair {g[k]:.3f}, {g[k + 1]:.3f}: first-order t_c = {p['t_c'][k]:+.5f}, exact from H_t = {exact:+.5f} "
                 f"(rel. diff {rel:.1e})")
    ok &= rel < 0.02
    X = 120.0 if quick else 400.0
    for t0, y0 in [(0.2, 0.2), (0.0, 0.05)]:
        r = dbn.rectangle_zero_free(t0, y0, X)
        lines.append(f"H_{t0:g} has no zero in [0, {X:g}] x [{y0:g}, {r.ymax:.2f}] (winding {r.winding:+.1e}, "
                     f"{r.samples} samples) -> finite-range part of Lambda <= {r.bound:.4f}")
        ok &= r.zero_free
    lines.append("known: 0 <= Lambda <= 0.2 (Rodgers-Tao 2018; Polymath 15 2019). The finite-range checks above do not")
    lines.append("bound Lambda by themselves: the range beyond X needs Polymath's asymptotic analysis.")
    return Check("de-bruijn-newman", ok, lines)


# ---------------------------------------------------------------- 3. Nyman-Beurling
def check_nyman_beurling(quick: bool) -> Check:
    N = 60 if quick else 200
    s = nyman_beurling.summary(N, 60)
    d2, n = s["d2"], s["n"]
    scaled = d2 * np.log(np.maximum(n, 2))
    pts = [k for k in (10, 25, 50, 100, 150, 200) if k <= N]
    band = float(np.max(np.abs(scaled[49:N] / nyman_beurling.C0 - 1))) if N >= 50 else float("nan")
    lines = [f"d_N^2 at dps {s['dps'][0]} and {s['dps'][1]} agree to {s['precision_agreement']:.1e}",
             "d_N^2 log N: " + ", ".join(f"N={k}: {scaled[k - 1]:.5f}" for k in pts),
             f"Burnol's lower bound C0 = 2 + gamma - log 4pi = {s['C0_burnol']:.5f}; d_N^2 at N={N}: {s['d2_N']:.6f}",
             f"monotone: {s['monotone_nonincreasing']}; above C0 at N={N}: {s['above_burnol']}",
             f"for 50 <= N <= {N}, d_N^2 log N stays within {band:.1%} of C0 (conjecture: -> C0). Its approach is slow and",
             "irregular, as Landreau-Richard (Exp. Math. 2002) found to N = 20000 (fit d_N ~ 0.21377/sqrt(log N), i.e. 0.0457)"]
    ok = (s["precision_agreement"] < 1e-12 and s["monotone_nonincreasing"] and band < 0.05)
    return Check("nyman-beurling", ok, lines)


# ---------------------------------------------------------------- 4. Weil
def check_weil(quick: bool) -> Check:
    z = zeros.first_zeros(120)
    fake = ((0.6, 20.0), (0.55, 30.0))
    configs = ((0.1, 12, 0.35), (0.07, 16, 0.3), (0.05, 24, 0.25))
    lines, ok = [], True
    detect = []
    for s_, m, du in configs:
        r = weil.check_family(s_, m, du, z, extra_zeros=fake[:1])
        r2 = weil.check_family(s_, m, du, z, extra_zeros=fake[1:])
        lines.append(f"s={s_:g}, m={m}, du={du:g}: lambda_min(primes) = {r['lambda_min_primes']:.3e}, "
                     f"lambda_min(zeros) = {r['lambda_min_zeros']:.3e}, max |M_primes - M_zeros| = {r['max_entry_diff']:.1e}")
        ok &= r["positive_within_error"] and r["max_entry_diff"] < 1e-12
        detect.append(min(r["lambda_min_with_offline_zero"], r2["lambda_min_with_offline_zero"]))
    lines.append("adding a hypothetical off-line zero (0.6+20i or 0.55+30i) to the zero side gives lambda_min = "
                 + ", ".join(f"{v:.2e}" for v in detect) + "  (negative = the family would detect it)")
    ok &= min(detect) < 0
    sc = weil.scalar_scan()
    lines.append(f"scalar Gaussian family: {sc['count']} test functions, min W = {sc['min_W']:.2e} at (r0, sigma) = {sc['at']}; "
                 f"W >= -{sc['tol']:g}: {sc['nonnegative_within_tol']}")
    ok &= sc["nonnegative_within_tol"]
    return Check("weil-positivity", ok, lines)


# ---------------------------------------------------------------- 5. Li (rigorous)
def check_li_rigorous(quick: bool) -> Check:
    N = 1000 if quick else 10000
    r = li_rigorous.li_coefficients_rigorous(N)
    s = li_rigorous.summary(r)
    half = li_rigorous.li_coefficients_rigorous(N // 2)
    agree = float(np.max(np.abs(half.mid - r.mid[:N // 2]) / np.abs(r.mid[:N // 2])))
    n = r.n.astype(float)
    dev = (r.mid - li_rigorous.asymptotic(n)) / (np.sqrt(n) * np.log(n + 1))
    q = [dev[N // 8: N // 4], dev[N // 4: N // 2], dev[N // 2: 3 * N // 4], dev[3 * N // 4:]]
    amps = [float(np.abs(x).max()) for x in q]
    lines = [f"backend {s['backend']} (certified={s['certified']}), {s['prec_bits']} bits: lambda_1..lambda_{N} all > 0: {s['all_positive']}",
             f"lambda_1 = {s['lambda_1']:.15f}, lambda_{N} = {s['lambda_N']:.6f}, max relative ball radius {s['max_rel_radius']:.1e}",
             f"independent run to N/2 at its own precision agrees to {agree:.1e} (relative)",
             f"lambda_N / ((N/2)(log N - 1 + gamma - log 2pi)) = {s['lambda_N_over_asymptotic']:.5f}",
             f"max |lambda_n - asymptotic| / (sqrt(n) log n) on n in (N/8, N/4], (N/4, N/2], (N/2, 3N/4], (3N/4, N]: "
             + ", ".join(f"{a:.4f}" for a in amps)
             + "  (RH predicts bounded; an off-line zero would make it grow exponentially)"]
    ok = s["all_positive"] and s["certified"] and agree < 1e-12 and amps[-1] <= 2 * amps[1]
    return Check("li-rigorous", ok, lines)


# ---------------------------------------------------------------- 6. Riesz + Redheffer
def check_riesz(quick: bool) -> Check:
    xmax = 1e8 if quick else 1e10
    s = riesz_redheffer.riesz_summary(xmax, 120 if quick else 200)
    x, R, Rz = s["x"], s["R"], s["R_zeros"]
    R2, _ = riesz_redheffer.riesz(x, c=6.0)              # different truncation point
    trunc_agree = float(np.max(np.abs(R2 - R) / x**0.25))
    big = x > 1e4
    amp = float(np.max(np.abs(R / x**0.25)[big]))
    rel = float(np.max(np.abs(R - Rz)[big] / x[big] ** 0.25) / amp)
    lines = [f"x up to {xmax:g}: max |R(x)|/x^(1/4) = {s['max_abs_R_over_x14']:.4f} (at x = {s['at_x']:.3g}, where the "
             f"trivial-zero term -16.4/x dominates); for x > 1e4 it is {amp:.2e} (RH: bounded)",
             f"R(x) vs the zero expansion with {s['nzeros']} zeros + 3 trivial terms, x > 1e4: max error "
             f"= {rel:.1e} of that amplitude",
             f"two truncation points (c = 4, 6) agree to {trunc_agree:.1e} x^(1/4); rigorous tail bound {s['max_truncation_bound_over_x14']:.1e} x^(1/4)",
             f"largest log|R(x)|/log x for x > 1e4: {s['max_growth_exponent_x>1e4']:.3f} (RH <=> eventually <= 1/4 + eps)"]
    ok = rel < 1e-3 and trunc_agree < 1e-6 and s["max_growth_exponent_x>1e4"] < 0.25
    return Check("riesz", ok, lines)


def check_redheffer(quick: bool) -> Check:
    nf = (200, 500, 1000) if quick else (200, 500, 1000, 2000, 3000)
    r = riesz_redheffer.redheffer_check(100 if quick else 200, nf)
    lines = [f"det A_n = M(n) exactly (integer Bareiss) for every n <= {r['exact_ok_n<=']}"]
    for row in r["float"]:
        lines.append(f"n = {row['n']}: det (LU) = {row['det_float']:+.6f}, M(n) = {row['M_n']:+d}, "
                     f"top eigenvalue / sqrt(n) = {row['top_eig_over_sqrt_n']:.4f}")
    ratios = [row["top_eig_over_sqrt_n"] for row in r["float"]]
    lines.append("top eigenvalue / sqrt(n) decreasing towards 1 (Vaughan: lambda_max = sqrt(n) + O(log n)): "
                 f"{all(b < a for a, b in zip(ratios, ratios[1:]))}")
    ok = r["all_match"] and all(b < a for a, b in zip(ratios, ratios[1:]))
    return Check("redheffer", ok, lines)


ALL = [check_turing, check_de_bruijn_newman, check_nyman_beurling, check_weil, check_li_rigorous, check_riesz, check_redheffer]


def run(quick: bool = False, only=None):
    t0 = time.time()
    print("== riemann-lab extended report: more RH criteria, with convergence verdicts ==")
    print("   (numerical evidence, not proof; 'CONSISTENT' = converged and in line with known theory)\n")
    out = []
    for f in ALL:
        name = f.__name__.replace("check_", "")
        if only and name not in only:
            continue
        c = _timed(lambda: f(quick))
        print(c, "\n", flush=True)
        out.append(c)
    print(f"{sum(c.ok for c in out)}/{len(out)} checks consistent; done in {time.time() - t0:.1f}s")
    return out
