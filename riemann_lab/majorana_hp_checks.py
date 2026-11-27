"""Majorana's infinite-component tower as a Hilbert-Polya frame: five checks with done criteria fixed before they
were built (docs/majorana_hp_done_criteria.md). Run with `python -m riemann_lab majorana-hp [--quick]`.

The construction (riemann_lab/majorana_hp.py) is built from L itself, so it can locate zeros on a given line but
cannot exclude zeros off it. Numerical evidence about low zeros, not proof.
"""
from __future__ import annotations

import math
import os
import time
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp
import numpy as np

from . import combined as C, majorana_hp as H
from .extended import Check, _timed
from .hlr_checks import zero_table

T_Z = 40.0
HS = (1e-2, 1e-3, 1e-4)


def _pool(fn, jobs):
    try:
        with ProcessPoolExecutor(min(len(jobs), os.cpu_count() or 1)) as ex:
            return list(ex.map(fn, jobs))
    except Exception:
        return list(map(fn, jobs))


# ------------------------------------------------------------------ 1. the oscillator singleton
def check_oscillator_singleton(quick: bool) -> Check:
    lines, ok = [], True
    D = None
    for N in ((200, 400) if quick else (400, 800)):
        r = H.oscillator_check(N)
        D = r["D"]
        lines.append(f"N = {N}: su(1,1) relations {r['alg']:.1e}, Casimir even sector (k = 1/4) {r['cas_even']:.1e}, odd "
                     f"(k = 3/4) {r['cas_odd']:.1e} (relative); even sector vs Plyushchay D+_1/4 {r['plyushchay']:.1e}; "
                     f"(xp + px)/2 + 2 K2 {r['D_vs_K2']:.1e}")
        ok &= max(r["alg"], r["cas_even"], r["cas_odd"], r["plyushchay"], r["D_vs_K2"]) < 1e-12
    worst = 0.0
    for n in (2, 3, 7):
        d = float(abs(H.squeezed_coeffs_closed(n, 40) - H.squeezed_coeffs_quad(n, 40)).max())
        worst = max(worst, d)
    lines.append(f"Hermite coefficients of e^(-x^2/2n^2), n = 2, 3, 7 (levels <= 80): quadrature vs squeezed-vacuum closed "
                 f"form, max diff {worst:.1e}")
    ok &= worst < 1e-12
    for lam in (0.5, 1.0, 2.0):
        m, f, ex = H.dilation_overlap_matrix(D, lam), H.dilation_overlap_fourier(lam), math.cosh(lam) ** -0.5
        lines.append(f"<phi0, e^(-i {lam} D) phi0>: tower {m:.15f}, Fourier of |Gamma(1/4 + iE/2)|^2 {f:.15f}, "
                     f"(cosh)^(-1/2) {ex:.15f}")
        ok &= abs(m - ex) < 1e-10 and abs(f - ex) < 1e-10
    lines.append("So at Bargmann index 1/4 the Majorana representation is the even oscillator sector, its boost is")
    lines.append("Berry-Keating's xp (D = -2 K2), and the spectral measure of D on the ground state is |Gamma(1/4 + iE/2)|^2,")
    lines.append("the weight of Masullo's critical line. M_chi(x^2) = sum mu chi(n)/n e^(-x^2/n^2) is a Moebius sum of")
    lines.append("squeezed vacua U(log n) phi0.")
    return Check("oscillator-singleton", ok, lines)


# ------------------------------------------------------------------ 2. the boost's spectral measure from the tower
def check_boost_spectral_measure(quick: bool) -> Check:
    lines, ok = [], True
    from .majorana import sl2_matrices
    for k in (0.05, 0.1, 0.15, 0.2, 0.25):
        _, Jp, Jm = sl2_matrices(k, 199)
        jdiff = float(abs((Jp + Jm) / 2 - H.boost_matrix(k, 200)).max())
        mass_c = 2 * math.pi * math.gamma(2 * k) / 4 ** k
        with mp.workdps(25):
            mass_q = float(2 * mp.quad(lambda E: abs(mp.gamma(mp.mpc(k, E))) ** 2, [0, 1, 3, 10, 30, mp.inf]))
        errs = {}
        for n in (200, 400):
            E, W = H.tower_rule(k, n)
            errs[n] = max(abs(np.sum(W * np.cos(l * E)) - H.gamma_charfun(k, l)) / H.gamma_charfun(k, l) for l in (0.5, 1.0))
            mass_t = float(W.sum())
        mom = max(abs(H.tower_moment(k, m) / H.gamma_moment(k, m) - 1) for m in range(11))
        lines.append(f"k = {k}: K1 = (J+ + J-)/2 {jdiff:.0e}; mass tower {mass_t:.15f}, closed {mass_c:.15f}, quad "
                     f"{mass_q:.15f}; moments E^(2m), m <= 10: {mom:.1e}; char. function n = 200: {errs[200]:.1e}, "
                     f"n = 400: {errs[400]:.1e}")
        ok &= (jdiff == 0 and abs(mass_t - mass_c) / mass_c < 1e-12 and abs(mass_q - mass_c) / mass_c < 1e-12
               and mom < 1e-10 and errs[400] < 1e-6 and errs[400] <= max(errs[200], 1e-14))   # 1e-14: rounding floor
    lines.append("The n-level Majorana tower in D+_k is the Gauss rule of |Gamma(k + iE)|^2 dE: its eigenvalues are the")
    lines.append("boost's 'discrete spectrum' at truncation n, and they fill the line as n grows.")
    return Check("boost-spectral-measure", ok, lines)


# ------------------------------------------------------------------ 3. the combined norm as a finite tower sum
def _tower_job(args):
    lab, chi, zp, ks, ns = args
    rows = []
    E0 = float(zp[0]) / 2
    for k in ks:
        ref = C.line_norm_mellin(chi, k)
        vals = [H.tower_norm(chi, k, n) for n in ns]
        ev, _ = H.tower_rule(k, ns[-1])
        j = int(np.argmin(abs(ev + E0)))
        spacing = float(abs(ev[j + 1] - ev[j - 1]) / 2)
        rows.append((k, ref, vals, [abs(v - ref) / ref for v in vals], spacing))
    return lab, rows


def check_tower_norm(quick: bool) -> Check:
    lines, ok = [], True
    tab = zero_table(T_Z, (3, 4, 5))
    ks = (0.05, 0.2) if quick else (0.05, 0.1, 0.15, 0.2)
    ns = (200, 400) if quick else (200, 400, 800)
    labs = ["zeta", "chi4"] if quick else list(tab)
    res = dict(_pool(_tower_job, [(lab, tab[lab][0], tab[lab][1], ks, ns) for lab in labs]))
    for lab in labs:
        parts = []
        for k, ref, vals, errs, sp in res[lab]:
            p = math.log(errs[0] / errs[-1]) / math.log(ns[-1] / ns[0])
            parts.append(f"k={k}: {vals[-1]:.10g} (err {', '.join(f'{e:.1e}' for e in errs)}; p = {p:.2f}; node spacing at "
                         f"-gamma1/2 {sp:.2f} vs peak width {0.25 - k:.2f})")
            if lab == "zeta":
                ok &= all(errs[i] / errs[i + 1] >= 3 for i in range(len(errs) - 1)) and (quick or errs[-1] < 1e-6)
            else:
                pred_sp = math.pi / math.log(ns[-1] / (float(tab[lab][1][0]) / 2))
                ok &= errs[-1] < 2e-2 and abs(sp / pred_sp - 1) < 0.25
        lines.append(f"{lab:<7} tower sum, n = {', '.join(map(str, ns))}, vs adaptive quadrature: " + "; ".join(parts))
    lines.append("No zeros are used: (1/2pi) sum_j w_j / |L(1 - 2k - 2i E_j)|^2 over the eigenvalues of the truncated boost.")
    lines.append("Resolution limit: near height E the tower's eigenvalues are spaced ~ pi/log(n/E) (0.5 at n = 800, E = 3), so a")
    lines.append("peak of width 1/4 - k at a low zero is sampled with an aliasing error ~ exp(-2 pi (1/4 - k)/spacing) =")
    lines.append("(n/E)^(-2(1/4 - k)): negligible for zeta (first zero at E = 7, weight e^(-7 pi)), slow and non-monotone for")
    lines.append("characters with zeros near E = 3 (errors up to 1e-2 at n = 800).")
    lines.append("A finite Majorana tower cannot resolve the critical line (k -> 1/4) at any n.")
    return Check("tower-norm", ok, lines)


# ------------------------------------------------------------------ 4. zeros as point spectrum at k -> 1/4
def _tracked(lab, zp, zn):
    K = 4 if lab == "zeta" else 3
    out = [(-float(g) / 2, mp.mpc(0.5, g)) for g in zp[:K]]
    out += [(float(g) / 2, mp.mpc(0.5, -g)) for g in zn[:K]]
    return out


def _window(lab, zp, zn) -> float:
    """Half-width of the E window: the tracked zeros plus 4, at most 20. Beyond |E| ~ 12 the weight
    |Gamma(1/4 + iE)|^2 ~ e^(-pi |E|) is below double-precision rounding of the total, and Gauss nodes placed there
    are fixed by rounding noise (first full run: chi5_1 locked nodes moved by 1e-6 between panel orders at T = 20)."""
    if lab == "model":
        return 20.0
    m = max(abs(E0) for E0, _ in _tracked(lab, zp, zn))
    return min(20.0, math.ceil(2 * (m + 4)) / 2)


def _npeaks(zp, zn, T: float = 20.0) -> int:
    return sum(1 for g in zp if g / 2 < T) + sum(1 for g in zn if g / 2 < T)


def _point_job(args):
    lab, chi, zp, zn, h, nodes, ns, L_override, peaks_extra, k0 = args
    with mp.workdps(30):
        k = mp.mpf(k0) - mp.mpf(h)
    T = _window(lab, zp, zn)
    peaks = [-float(g) / 2 for g in zp if g < 2 * T] + [float(g) / 2 for g in zn if g < 2 * T] + list(peaks_extra)
    E, W = H.arithmetic_measure(chi, k, T, peaks, h, nodes=nodes, L_override=L_override)
    return (lab, h, nodes), {n: H.lanczos_rule(E, W, n) for n in ns}


HS4 = (1e-3, 1e-4, 1e-5)


def check_boost_point_spectrum(quick: bool) -> Check:
    lines, ok = [], True
    tab = zero_table(T_Z, (3, 4, 5))
    labs = ["zeta", "chi4"] if quick else ["zeta", "chi4", "chi3_1", "chi5_1"]
    jobs, nsz = [], {}
    for lab in labs:
        chi, zp, zn = tab[lab]
        npk = _npeaks(zp, zn, _window(lab, zp, zn))
        nsz[lab] = (npk + 32, npk + 16)
        for h in HS4:
            for nodes in ((24,) if (quick or h != HS4[-1]) else (24, 32)):
                jobs.append((lab, chi, zp, zn, h, nodes, nsz[lab], None, (), 0.25))
    res = dict(_pool(_point_job, jobs))
    for lab in labs:
        chi, zp, zn = tab[lab]
        n1, n2 = nsz[lab]
        tot_w, tot_B = 0.0, 0.0
        lines.append(f"{lab}: window |E| < {_window(lab, zp, zn)}, {n1 - 32} peaks in it, Jacobi matrix of size n = {n1} (and {n2})")
        for E0, rho in _tracked(lab, zp, zn):
            pred = H.point_mass_pred(chi, rho)
            errs = []
            for h in HS4:
                e, w = H.locate(*res[(lab, h, 24)][n1], E0)
                errs.append(abs(e - E0))
            ratio = HS4[-1] * w / pred
            e2, w2 = H.locate(*res[(lab, HS4[-1], 24)][n2], E0)
            dec = [errs[i] / errs[i + 1] for i in range(len(errs) - 1)]
            g = abs(float(rho.imag))
            d32 = None
            if not quick:
                d32 = abs(H.locate(*res[(lab, HS4[-1], 32)][n1], E0)[0] - H.locate(*res[(lab, HS4[-1], 24)][n1], E0)[0])
            lines.append(f"  gamma = {float(rho.imag):+.6f}: |node - E0| at h = 1e-3, 1e-4, 1e-5: "
                         f"{', '.join(f'{x:.1e}' for x in errs)} (x{', x'.join(f'{d:.1f}' for d in dec)} per decade); "
                         f"h w / (|Gamma|^2/8|L'|^2) = {ratio:.6f}; n = {n2}: {abs(e2 - E0):.1e}, {HS4[-1] * w2 / pred:.6f}"
                         + ("" if d32 is None else f"; 24 vs 32 panel nodes {d32:.0e}"))
            ok &= all(5 <= d <= 20 for d in dec) and abs(ratio - 1) < 1e-2 and (g >= 16 or errs[-1] < 1e-3)
            if d32 is not None:
                ok &= d32 < 1e-9
            tot_w += HS4[-1] * w
            tot_B += pred
        lines.append(f"  sum of h w over the tracked zeros {tot_w:.6e} vs their share of B_chi {tot_B:.6e} "
                     f"(rel. {abs(tot_w - tot_B) / tot_B:.1e})")
        ok &= abs(tot_w - tot_B) / tot_B < 1e-2
    lines.append("The Jacobi matrix of |Gamma(k + iE)/L(1 - 2k - 2iE)|^2 dE (the Majorana boost in the Masullo norm) has")
    lines.append("eigenvalues within O(1/4 - k) of -gamma/2 for each tracked zero, carrying the zero's share of B_chi/(1/4 - k).")
    lines.append("Order of limits: h -> 0 at fixed n gives the point spectrum; n -> oo at fixed h resolves the peaks into a")
    lines.append("continuum again. n must exceed the number of peaks by enough nodes for the smooth part: with n = peaks + 16")
    lines.append("the third chi4 zero kept only 78% of its mass at h = 1e-5 (second full run).")
    return Check("boost-point-spectrum", ok, lines)


# ------------------------------------------------------------------ 5. an off-line zero
def check_off_line_control(quick: bool) -> Check:
    lines, ok = [], True
    tab = zero_table(T_Z, (3, 4, 5))
    _, zp, _ = tab["zeta"]
    with mp.workdps(35):
        g1 = mp.zetazero(1).imag
        Lmod = C.moved_zero_L(None, g1, mp.mpf(3) / 5)
    zrest = [z for z in zp if abs(z - float(g1)) > 1e-6]
    jobs = []
    for h in HS:
        # critical line: the moved pair has no peak there; the others do
        jobs.append((("crit", h), None, zrest, zrest, h, 24, (30,), Lmod, (-float(g1) / 2, float(g1) / 2), 0.25))
        # the line through the moved zero: 1 - 2k = 3/5 + 2h
        jobs.append((("off", h), None, [], [], h, 24, (30,), Lmod, (-float(g1) / 2, float(g1) / 2), mp.mpf(1) / 5))
    res = {}
    for key, rule in _pool(_point_job_keyed, jobs):
        res[key] = rule
    E1 = -float(g1) / 2
    with mp.workdps(30):
        rho_moved = mp.mpc(mp.mpf(3) / 5, g1)
    pred_moved = H.point_mass_pred(None, rho_moved, L_override=Lmod)
    pred_orig = H.point_mass_pred(None, mp.mpc(0.5, g1))
    crit = [HS[i] * H.locate(*res[("crit", HS[i])][30], E1)[1] for i in range(len(HS))]
    dec = [crit[i] / crit[i + 1] for i in range(len(crit) - 1)]
    lines.append(f"model zeta, first pair moved to 3/5 +- i gamma1: at k = 1/4 - h the node nearest -gamma1/2 has h w = "
                 f"{', '.join(f'{x:.2e}' for x in crit)} (x{', x'.join(f'{d:.1f}' for d in dec)} per decade -> 0: no point mass; "
                 f"the on-line zero would carry {pred_orig:.2e})")
    ok &= all(5 <= d <= 20 for d in dec)
    for g in zrest[:2]:
        E0 = -float(g) / 2
        pred = H.point_mass_pred(None, mp.mpc(0.5, g), L_override=Lmod)
        errs = [abs(H.locate(*res[("crit", h)][30], E0)[0] - E0) for h in HS]
        r = HS[-1] * H.locate(*res[("crit", HS[-1])][30], E0)[1] / pred
        d2 = [errs[i] / errs[i + 1] for i in range(len(errs) - 1)]
        lines.append(f"  on-line zero gamma = {g:.6f} of the model still locks: |node - E0| {', '.join(f'{x:.1e}' for x in errs)}, "
                     f"h w / pred = {r:.5f}")
        ok &= all(5 <= d <= 20 for d in d2) and abs(r - 1) < 1e-2
    errs = [abs(H.locate(*res[("off", h)][30], E1)[0] - E1) for h in HS]
    r = HS[-1] * H.locate(*res[("off", HS[-1])][30], E1)[1] / pred_moved
    d3 = [errs[i] / errs[i + 1] for i in range(len(errs) - 1)]
    lines.append(f"at k = 1/5 - h (the line through the moved zero) it locks: |node - E0| {', '.join(f'{x:.1e}' for x in errs)} "
                 f"(x{', x'.join(f'{d:.1f}' for d in d3)}), h w / (|Gamma((1-rho')/2)|^2/8|L~'(rho')|^2) = {r:.5f}")
    ok &= all(5 <= d <= 20 for d in d3) and abs(r - 1) < 1e-2
    for k in (0.05, 0.25):
        lines.append(f"visibility: in D+_{k} zeros above |gamma| = {C.visible_height(k):.1f} carry weight below 1e-16 of the "
                     "total and are invisible to every check here")
    lines.append("So the Majorana boost sees a zero beta + i gamma as point spectrum only in D+_k with k = (1 - beta)/2. The")
    lines.append("critical space k = 1/4 sees exactly the zeros on the line; an off-line zero is simply absent there. Proving")
    lines.append("that no D+_k with k < 1/4 carries point spectrum is the statement L != 0 on 1/2 < Re s < 1: GRH itself.")
    return Check("off-line-control", ok, lines)


def _point_job_keyed(args):
    key, *rest = args
    return key, _point_job(("model", *rest))[1]


ALL = [check_oscillator_singleton, check_boost_spectral_measure, check_tower_norm, check_boost_point_spectrum,
       check_off_line_control]


def run(quick: bool = False, only=None):
    t0 = time.time()
    print("== riemann-lab: Majorana's infinite-component tower as a Hilbert-Polya frame "
          "(criteria in docs/majorana_hp_done_criteria.md) ==")
    print("   (the operator is built from L itself: it locates zeros on a line, it cannot exclude zeros off it;")
    print("    numerical evidence, not proof; 'CONSISTENT' = every criterion met)\n")
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
