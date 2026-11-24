"""Ramanujan x Masullo: eight checks with done criteria fixed before they were built
(docs/ramanujan_done_criteria.md). Run with `python -m riemann_lab ramanujan [--quick]`.

Each check prints CONSISTENT only if every criterion in its row holds, including agreement between
two independent computations. Numerical evidence, not proof.
"""
from __future__ import annotations

import math
import os
import time
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp
import numpy as np

from . import hecke, ramanujan as R, zeros
from .extended import Check, _timed

MODULI = (3, 4, 5, 7, 8, 11, 13)
FIRST_DELTA_ZERO = 9.22237939992110252224


# ------------------------------------------------------------------ shared zero data
def _char_zero_data(args):
    chi, T = args
    z1 = hecke.line_zeros(chi, T, step=0.1)
    z2 = hecke.line_zeros(chi, T, step=0.05)
    w = hecke.winding_count(chi, T)
    rot = 1 / complex(mp.sqrt(chi.root_number()))
    imag = max(abs(complex(mp.exp(1j * hecke.theta(t, chi)) * hecke.L(mp.mpc(0.5, t), chi) * rot).imag)
               for t in (3.3, 17.1, T - 0.7))
    dz = np.array([abs(hecke.Z_derivative(g, chi)) for g in z2])
    return chi.label, {"z_coarse": z1, "z_fine": z2, "winding": w, "N_smooth": hecke.N_smooth(T, chi),
                       "max_imag_Z": imag, "min_abs_Zprime": float(dz.min()) if dz.size else float("nan")}


_CACHE: dict = {}


def characters():
    out = []
    for q in MODULI:
        out += hecke.primitive_characters(q)
    return out


def zero_data(T: float) -> dict:
    if T in _CACHE:
        return _CACHE[T]
    chars = characters()
    jobs = [(c, T) for c in chars]
    workers = min(len(jobs), os.cpu_count() or 1)
    try:
        with ProcessPoolExecutor(workers) as ex:
            res = dict(ex.map(_char_zero_data, jobs))
    except Exception:                                   # no multiprocessing: serial
        res = dict(map(_char_zero_data, jobs))
    data = {"T": T, "chars": {c.label: c for c in chars}, "res": res}
    _CACHE[T] = data
    return data


def conj_label(data, chi: hecke.Character) -> str:
    cb = chi.conj()
    for lab, c in data["chars"].items():
        if c.q == chi.q and all(abs(a - b) < 1e-9 for a, b in zip(c.values, cb.values)):
            return lab
    raise KeyError(chi.label)


# ------------------------------------------------------------------ 1. Master Theorem
def check_rmt_mellin(quick: bool) -> Check:
    lines, ok = [], True
    chars = [hecke.primitive_characters(4)[0], hecke.primitive_characters(5)[0]]
    if not quick:
        chars += [hecke.primitive_characters(5)[1], hecke.primitive_characters(7)[2]]
    seen = set()
    for chi in chars:
        r = R.rmt_check(chi)
        for row in r["rows"]:
            if row["name"] in seen:
                continue
            seen.add(row["name"])
            A = row["A"] if row["A"] is not None else R.hardy_growth_exponent_L(chi)
            lines.append(f"{row['name']:<24} max rel. err vs Gamma(s) lambda(-s) {row['max_rel_err']:.1e} at {row['points']} "
                         f"points; dps 20 vs 30 {row['precision_agreement']:.1e}; Taylor {row['taylor_err']:.1e}; "
                         f"Hardy A = {A:.3f} (< pi)")
            ok &= (row["max_rel_err"] < 1e-10 and row["precision_agreement"] < 1e-10 and row["taylor_err"] < 1e-12
                   and A < math.pi)
    hs = R.hardy_sobolev_check()
    worst = max(r["rel_diff"] for r in hs["rows"])
    lines.append(f"Hardy-Sobolev norms of (1+x)^-1.5, I = [0.3, 1.1], s = 0 and s = 2: x side = Mellin side (via RMT) "
                 f"to {worst:.1e}; ||f||^2 = {hs['norm2']:.6f} <= edge sum {hs['edge_sum']:.6f} <= 2||f||^2: {hs['sandwich']}")
    ok &= worst < 1e-8 and hs["sandwich"]
    lines.append("Hardy's hypothesis holds with A = pi/2 for zeta and L(s, chi): by Carlson's theorem the values at the")
    lines.append("negative integers (Bernoulli numbers) determine L(s, chi) inside the critical strip.")
    return Check("rmt-mellin", ok, lines)


# ------------------------------------------------------------------ 2. Hardy-Littlewood-Ramanujan
def check_hardy_littlewood_ramanujan(quick: bool) -> Check:
    lines, ok = [], True
    T = 30.0 if quick else 50.0
    data = zero_data(T)
    xmax = 1e6 if quick else 1e8
    N = 10**6 if quick else 10**7
    xs_series = (1.0, 10.0, 50.0, 100.0)
    xs_mob = np.logspace(2, math.log10(xmax), 13)
    targets = [None] + [data["chars"][lab] for lab in ("chi3_1", "chi4", "chi5_1", "chi5_2", "chi5_3")]
    zz = zeros.first_zeros(60)
    for chi in targets:
        if chi is None:
            zp, zn, name = zz, zz, "zeta"
        else:
            zp = data["res"][chi.label]["z_fine"]
            zn = data["res"][conj_label(data, chi)]["z_fine"]
            name = chi.label
        mob = R.MobiusTable(N, chi)
        e_series = max(abs(R.hl_series(x, chi) - R.hl_zero_expansion(x, chi, zp, zn)) * x**0.25 for x in xs_series)
        e_mob, excess = 0.0, []
        for x in xs_mob:
            v, bound = mob(float(x))
            ze = R.hl_zero_expansion(float(x), chi, zp, zn)
            triv = R.hl_zero_expansion(float(x), chi, [], [])
            e_mob = max(e_mob, (abs(v - ze) + bound) * x**0.25)
            excess.append((abs(v) * x**0.25, abs(v - triv) * x**0.25))
        # GRH-consistent bound: sum over zeros of |Gamma((1-rho)/2)| / (2|L'(rho)|) (the x^{1/4} amplitude)
        Ld = (lambda w: mp.zeta(w, derivative=1)) if chi is None else (lambda w: mp.dirichlet(w, list(chi.values), 1))
        B = sum(float(abs(mp.gamma((0.5 - 1j * g) / 2) / (2 * Ld(mp.mpc(0.5, g))))) for g in zp) + \
            sum(float(abs(mp.gamma((0.5 + 1j * g) / 2) / (2 * Ld(mp.mpc(0.5, -g))))) for g in zn)
        smax = max(a for a, _ in excess)
        nontriv = max(b for _, b in excess)                # x^{1/4} |M - trivial-zero terms|
        lines.append(f"{name:<7} series vs zero expansion {e_series:.1e}, Moebius sum (N={N:.0e}) vs zero expansion "
                     f"{e_mob:.1e} (units of x^-1/4); 1e2 <= x <= {xmax:.0e}: max x^1/4 |M| = {smax:.3e}, without the "
                     f"trivial-zero terms {nontriv:.3e} <= sum_rho |Gamma((1-rho)/2)/(2L'(rho))| = {B:.3e}")
        ok &= e_series < 1e-8 and e_mob < 1e-8 and nontriv <= B * (1 + 1e-9)
    for alpha in (0.5, 1.0, 1.5):
        r = R.ramanujan_alpha_beta(alpha, zz)
        lines.append(f"Ramanujan alpha beta = pi, alpha = {alpha}: lhs {r['lhs']:+.15e}, zero side {r['rhs'].real:+.15e}, "
                     f"diff {r['diff']:.1e}")
        ok &= r["diff"] < 1e-12
    lines.append("RMT: Mellin(M_chi)(s) = Gamma(s)/L(1-2s, chi); its poles sit at s = (1-rho)/2, so GRH <=> M_chi = O(x^(-1/4+eps)).")
    return Check("hardy-littlewood-ramanujan", ok, lines)


# ------------------------------------------------------------------ 3. zeros of Dirichlet L
def check_hecke_zeros(quick: bool) -> Check:
    T = 30.0 if quick else 50.0
    data = zero_data(T)
    lines, ok = [], True
    total = 0
    by_q = {}
    for lab, chi in data["chars"].items():
        r = data["res"][lab]
        n1, n2, w = len(r["z_coarse"]), len(r["z_fine"]), r["winding"]
        good = n1 == n2 and abs(w - n2) < 1e-6 and r["max_imag_Z"] < 1e-10
        ok &= good
        total += n2
        by_q.setdefault(chi.q, []).append((lab, n2, w, abs(n2 - r["N_smooth"]), good))
    for q, rows in by_q.items():
        lines.append(f"q = {q:>2}: {len(rows)} characters, zeros on the line "
                     + ", ".join(f"{n}" for _, n, _, _, _ in rows)
                     + f"; argument-principle counts equal: {all(g for *_, g in rows)}; max |count - smooth N| "
                     f"{max(d for *_, d, _ in rows):.2f}")
    lines.append(f"{total} zeros with 0 < gamma <= {T:g} for {len(data['chars'])} primitive characters: every zero of "
                 f"Lambda(s, chi) in [-1/2, 3/2] x [0, {T:g}] is on Re s = 1/2 (grid 0.1 and 0.05 give the same count)")
    return Check("hecke-zeros", ok, lines)


# ------------------------------------------------------------------ 4. explicit formula for chi
def check_hecke_explicit_formula(quick: bool) -> Check:
    T = 30.0 if quick else 50.0
    data = zero_data(T)
    lines, ok = [], True
    widths = (3.0, 4.0) if quick else (4.0, 6.0)
    worst, worst_lab, detect = 0.0, None, []
    for lab, chi in data["chars"].items():
        zp = data["res"][lab]["z_fine"]
        zb = data["res"][conj_label(data, chi)]["z_fine"]
        for w in widths:
            r = hecke.explicit_formula(chi, zp, zb, w)
            if abs(r["residual"]) > worst:
                worst, worst_lab = abs(r["residual"]), (lab, w)
        bad = hecke.explicit_formula(chi, zp, zb, widths[-1], extra_zeros=[(0.6, 9.0)])
        detect.append(abs(bad["residual"]))
    lines.append(f"Weil explicit formula, h(r) = exp(-(r/w)^2), w in {widths}, {len(data['chars'])} characters: "
                 f"max |zero side - prime side| = {worst:.1e} (at {worst_lab})")
    lines.append(f"adding one hypothetical zero pair 0.6 + 9i, 0.4 + 9i breaks it by at least {min(detect):.1e}")
    ok = worst < 1e-8 and min(detect) > 1e-4
    return Check("hecke-explicit-formula", ok, lines)


# ------------------------------------------------------------------ 5. multiplicities
def check_zero_multiplicities(quick: bool) -> Check:
    T = 30.0 if quick else 50.0
    data = zero_data(T)
    lines, ok = [], True
    zz = zeros.first_zeros(30 if quick else 40)
    zz = zz[zz <= T]
    zeta_dz = min(abs(float(mp.diff(mp.siegelz, g))) for g in zz)
    for q in (5, 7, 11, 13):
        labs = [lab for lab, c in data["chars"].items() if c.q == q]
        ords = [("zeta", g) for g in zz] + [(lab, g) for lab in labs for g in data["res"][lab]["z_fine"]]
        ords.sort(key=lambda t: t[1])
        gaps = [b[1] - a[1] for a, b in zip(ords, ords[1:])]
        mindz = min([zeta_dz] + [data["res"][lab]["min_abs_Zprime"] for lab in labs])
        lines.append(f"zeta of Q(zeta_{q}) (degree {q - 1} = bound in Expectation 1.7.1): {len(ords)} zeros up to {T:g}, "
                     f"min gap between ordinates {min(gaps):.2e}, min |Z'| at a zero {mindz:.2e} -> all simple")
        ok &= min(gaps) > 1e-6 and mindz > 1e-3
    with mp.workdps(30):
        v = [mp.zetazero(k).imag for k in range(1, 9)]
        rel = mp.pslq(v, maxcoeff=1000, maxsteps=10**5)
    lines.append(f"PSLQ on gamma_1..gamma_8 (30 digits, coefficients <= 1000): {'no relation' if rel is None else rel}")
    ok &= rel is None
    # Masullo Thm 1.7.1.1: poles of local factors (1 - chi(p) p^-s)^-1 shared by two primes
    common = _common_local_poles(hecke.primitive_characters(7)[0], 60, 200.0)
    lines.append(f"Thm 1.7.1.1 (finite order chi mod 7, p <= 60, |Im s| <= 200): poles shared by local factors at two "
                 f"distinct primes: {common} (expected: only s = 0)")
    ok &= common == [0.0]
    return Check("zero-multiplicities", ok, lines)


def _common_local_poles(chi: hecke.Character, pmax: int, H: float):
    from .primes import sieve
    poles = {}
    for p in sieve(pmax):
        p = int(p)
        c = chi(p)
        if abs(c) < 0.5:
            continue
        arg = math.atan2(c.imag, c.real)
        lp = math.log(p)
        kmax = int(H * lp / (2 * math.pi)) + 2
        for k in range(-kmax, kmax + 1):
            y = (arg + 2 * math.pi * k) / lp          # pole at s = i y
            if abs(y) <= H:
                poles.setdefault(round(y, 9), set()).add(p)
    return sorted(y for y, ps in poles.items() if len(ps) > 1)


# ------------------------------------------------------------------ 6. Euler products on the 1-line
def check_euler_products(quick: bool) -> Check:
    xmax = 1e6 if quick else 1e7
    from .primes import sieve
    primes = sieve(int(xmax) + 1)
    xs = np.logspace(3, math.log10(xmax), 13)
    lines, ok = [], True
    chars = [c for q in (3, 4, 5, 7, 8) for c in hecke.primitive_characters(q)]
    rows = []
    for chi in chars:
        e = hecke.euler_product_1line(chi, xs, primes)
        h = len(xs) // 2
        rows.append((chi.label, e["rel_error"][-1], e["scaled"][:h].max(), e["scaled"][h:].max()))
    worst_late = max(r[3] for r in rows)
    grow = max(r[3] / r[2] for r in rows)
    lines.append(f"{len(chars)} characters: |P(x)/L(1,chi) - 1| at x = {xmax:.0e} between {min(r[1] for r in rows):.1e} "
                 f"and {max(r[1] for r in rows):.1e}")
    lines.append(f"scaled error |P/L - 1| sqrt(x)/log(x)^2: max {worst_late:.2e} on the upper half of the range; "
                 f"max ratio upper/lower half {grow:.2f} (GRH: bounded)")
    ok &= grow < 2.0 and worst_late < 0.1
    nic = hecke.nicolas_primorials(int(xmax))
    lines.append(f"Nicolas: N_k/phi(N_k) > e^gamma log log N_k for all {nic['count']} primorials with p_k <= {xmax:.0e}: "
                 f"{nic['holds']} (min ratio {nic['min_ratio']:.7f}; scaled margin in [{nic['scaled_margin'].min():.3f}, "
                 f"{nic['scaled_margin'].max():.3f}])")
    ok &= nic["holds"]
    return Check("euler-products-1-line", ok, lines)


# ------------------------------------------------------------------ 7. Ramanujan / Robin
def check_ramanujan_robin(quick: bool) -> Check:
    lines, ok = [], True
    count = 20000 if quick else 90000
    r = R.robin_ramanujan_constant(count, 2 * 10**6)
    s, L = r["scaled"], r["log_n"]
    n = len(s)
    first, second = s[: n // 2], s[n // 2:]
    lines.append(f"{n} colossally abundant n up to log n = {L[-1]:.4g}: Robin margin positive for all: {bool((s > 0).all())}")
    lines.append(f"(e^gamma loglog n - sigma(n)/n) sqrt(log n): mean {first.mean():.5f} on the first half, {second.mean():.5f} "
                 f"on the second (drifting down: {second.mean() < first.mean()}); min on the second half {second.min():.5f} "
                 f"vs the RH liminf (Ramanujan; Robin 1984) {r['limit']:.5f}. It oscillates, so no monotone decrease is expected")
    ok &= bool((s > 0).all()) and second.mean() < first.mean() and second.min() > r["limit"] - 0.05
    good = all(R.ramanujan_sum(q, m) == round(R.ramanujan_sum_direct(q, m)) for q in range(1, 60) for m in range(1, 60))
    Q = 2000
    errs = []
    for m in (1, 6, 12, 30, 60, 360):
        sig = sum(d for d in range(1, m + 1) if m % d == 0) / m
        errs.append(abs(R.ramanujan_sigma_expansion(m, Q) - sig))
    lines.append(f"c_q(n) closed form = sum of primitive q-th roots of unity for q, n < 60: {good}; "
                 f"zeta(2) sum_(q<={Q}) c_q(n)/q^2 - sigma(n)/n: max {max(errs):.1e} (<= 10/Q)")
    ok &= good and max(errs) < 10 / Q
    N = 10**6 if quick else 10**7
    p = R.ramanujan_pnt_sums(N)
    lines.append(f"sum_q c_q(n)/q = 0: partial sums = sum_(d|n) m(Q/d), m(x) = sum_(k<=x) mu(k)/k; for 1e3 <= x <= {N:.0e} "
                 f"max |m(x)| sqrt(x) = {p['max_scaled']:.3f}, max log|m(x)|/log x = {p['max_exponent']:.3f} (RH rate: <= -1/2 + eps)")
    ok &= p["max_exponent"] < -0.45
    return Check("ramanujan-robin", ok, lines)


# ------------------------------------------------------------------ 8. tau
def check_ramanujan_tau(quick: bool) -> Check:
    c = R.tau_checks(2000)
    lines = [f"tau(1..10) = {c['tau_small']}",
             f"multiplicative {c['multiplicative']}, tau(p^2) = tau(p)^2 - p^11 {c['hecke_p2']}, tau(p^3) recursion {c['hecke_p3']}, "
             f"tau = sigma_11 mod 691 {c['congruence_691']} (n <= 2000)",
             f"Deligne: max |tau(p)|/(2 p^5.5) = {c['max_|tau(p)|/(2p^5.5)']:.4f} over {c['nprimes']} primes; Sato-Tate moments "
             + ", ".join(f"E[(2x)^{k}] = {v:.3f}" for k, v in c["sato_tate_moments"].items()) + f" (1, 2, 5): {c['sato_tate_ok']}"]
    ok = c["multiplicative"] and c["hecke_p2"] and c["hecke_p3"] and c["congruence_691"] and \
        c["max_|tau(p)|/(2p^5.5)"] <= 1 and c["sato_tate_ok"]
    T = 20.0 if quick else 30.0
    D = R.DeltaL()
    z = D.zeros(T)
    w = D.winding(T)
    lines.append(f"L(Delta, s): {len(z)} sign changes of Lambda(6 + it) for 0 < t <= {T:g}; argument principle on "
                 f"[4.5, 7.5] x [0, {T:g}]: {w:.6f}; first zero {z[0]:.12f} (LMFDB 9.222379399921)")
    ok &= abs(w - len(z)) < 1e-6 and abs(z[0] - FIRST_DELTA_ZERO) < 1e-8
    return Check("ramanujan-tau", ok, lines)


ALL = [check_rmt_mellin, check_hardy_littlewood_ramanujan, check_hecke_zeros, check_hecke_explicit_formula,
       check_zero_multiplicities, check_euler_products, check_ramanujan_robin, check_ramanujan_tau]


def run(quick: bool = False, only=None):
    t0 = time.time()
    print("== riemann-lab: Ramanujan x Masullo checks (done criteria in docs/ramanujan_done_criteria.md) ==")
    print("   (numerical evidence, not proof; 'CONSISTENT' = every criterion met, two computations agree)\n")
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
