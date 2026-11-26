"""Ramanujan + Majorana + Masullo combined formulation: five checks with done criteria fixed before they were
built (docs/combined_done_criteria.md). Run with `python -m riemann_lab combined [--quick]`.

The combined statement (see riemann_lab/combined.py) is a reformulation of GRH: Hardy-Littlewood (1918) and
Garg-Maji (2022) in Hilbert-space form. Numerical evidence, not proof.
"""
from __future__ import annotations

import math
import os
import time
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp
import numpy as np

from . import combined as C, hlr, hecke
from .extended import Check, _timed
from .hlr_checks import zero_table

LINE_MODULI = (3, 4, 5, 7)
BLOWUP_MODULI = (3, 4, 5)
T_Z = 80.0


def _pool(fn, jobs):
    try:
        with ProcessPoolExecutor(min(len(jobs), os.cpu_count() or 1)) as ex:
            return list(ex.map(fn, jobs))
    except Exception:
        return list(map(fn, jobs))


def _select(tab, moduli):
    return [(lab, v) for lab, v in tab.items() if v[0] is None or v[0].q in moduli]


# ------------------------------------------------------------------ 1. line norms, x side vs Mellin side
def _line_job(args):
    lab, chi, zp, zn, cs = args
    ze = hlr.ZeroExpansion(chi, zp, zn)
    ser = hlr.Series(chi, 0, xmax=50.0)
    rows = []
    c0 = hlr.inv_L1(chi)
    for c in cs:
        sub = c0 if c < 0 else 0            # c < 0: M - 1/L(1), unconditional; c > 0: M itself, GRH-equivalent
        x30, x50 = C.line_norm_x(c, ser, ze, 30.0, sub), C.line_norm_x(c, ser, ze, 50.0, sub)
        m = C.line_norm_mellin(chi, c)
        rows.append((c, x50, m, abs(x30 - m) / m, abs(x50 - m) / m))
    return lab, rows


def check_line_norm(quick: bool) -> Check:
    lines, ok = [], True
    tab = zero_table(T_Z)
    cs = (-0.5, 0.1, 0.2) if quick else (-0.6, -0.3, 0.05, 0.1, 0.15, 0.2)
    sel = _select(tab, (3, 4) if quick else LINE_MODULI)
    res = dict(_pool(_line_job, [(lab, chi, zp, zn, cs) for lab, (chi, zp, zn) in sel]))
    for lab, rows in res.items():
        worst = max(max(r[3], r[4]) for r in rows)
        lines.append(f"{lab:<7} ||M||^2 on Re z = c: " + ", ".join(f"c={r[0]}: {r[2]:.10g}" for r in rows) +
                     f"; x side (X0 = 30, 50) vs Mellin side max rel. diff {worst:.1e}")
        ok &= worst < 1e-9
    lines.append("Mellin side uses only |Gamma/L|^2 on the line (no zeros); x side uses the power series and, beyond X0,")
    lines.append("the zero expansion (checked against the Moebius sum to 1e11 in `python -m riemann_lab hlr`).")
    lines.append("Equal norms = M_chi in Masullo's line space for c and in Majorana's D+_alpha, alpha = 1 - c.")
    lines.append("c < 0 (alpha in (1, 2)): the identity for M - 1/L(1, chi) is a theorem. c in (0, 1/4) (alpha in (3/4, 1)): it")
    lines.append("holds for all such c iff GRH; here it is only verified, with zeros below height ~25 doing all the work.")
    return Check("line-norm", ok, lines)


# ------------------------------------------------------------------ 2. Majorana holomorphic side (Paley-Wiener)
def _holo_job(args):
    lab, chi, zp, zn, vs = args
    ze = hlr.ZeroExpansion(chi, zp, zn)
    ser = hlr.Series(chi, 0, xmax=30.0)
    F1, F2 = C.Holo(chi, 1000), C.Holo(chi, 3000)
    rows = []
    for v in vs:
        h1, h2 = C.hline_integral(F1, v), C.hline_integral(F2, v)
        lap = 2 * math.pi * C.laplace_weighted(v, ser, ze, 30.0)
        rows.append((v, h2, lap, abs(h1 - lap) / lap, abs(h2 - lap) / lap))
    return lab, rows


def check_majorana_holomorphic(quick: bool) -> Check:
    lines, ok = [], True
    tab = zero_table(T_Z)
    vs = (0.05, 1.0) if quick else (0.05, 0.2, 1.0)
    labs = ["zeta", "chi4"] + ([] if quick else ["chi5_2"])
    res = dict(_pool(_holo_job, [(lab, *tab[lab], vs) for lab in labs]))
    for lab, rows in res.items():
        worst = max(max(r[3], r[4]) for r in rows)
        lines.append(f"{lab:<7} int |F(u+iv)|^2 du (n-sum, N = 1e3 and 3e3) vs 2pi int |M|^2 e^(-2vt) dt: " +
                     ", ".join(f"v={r[0]}: {r[1]:.10g}" for r in rows) + f"; max rel. diff {worst:.1e}")
        ok &= worst < 1e-8
    lines.append("F_chi(w) = sum mu chi(n) n/(1 - i n^2 w) is the holomorphic (Majorana-Plyushchay) vector; integrating")
    lines.append("v^(2alpha-2) over v turns these into ||F||^2_{D+_alpha} = the line norm of check 1 at c = 1 - alpha.")
    return Check("majorana-holomorphic", ok, lines)


# ------------------------------------------------------------------ 3. blow-up at the critical line
def _blow_job(args):
    lab, chi, zp, zn, fac = args
    if chi is None:
        with mp.workdps(35):
            zp = [mp.zetazero(k).imag for k in range(1, 9)]
        zn = zp
    ze = hlr.ZeroExpansion(chi, [float(z) for z in zp], [float(z) for z in zn])
    B = C.B_from_zeros(ze)
    with mp.workdps(40):
        zt = [-mp.mpf(z) / 2 for z in zp] + [mp.mpf(z) / 2 for z in zn]
    Nbg = C.line_norm_mellin(chi, 0.2, t_max=24.0)
    h0 = B / Nbg
    rows = []
    for f in fac:
        h = h0 * f
        dps = 20 + max(0, int(round(-math.log10(h))) - 4)
        with mp.workdps(dps):              # c = 1/4 - h at full precision: at 15 digits h = 2e-12 is off by 5e-5
            c = mp.mpf(1) / 4 - mp.mpf(h)
        v = C.line_norm_mellin(chi, c, t_max=24.0, zeros_t=zt, h_hint=h, dps=dps)
        rows.append((h, v * h))
    hs = np.array([r[0] for r in rows])
    Vs = np.array([r[1] for r in rows])
    # Richardson to second order on the three smallest h (V = B + a h + b h^2 + O(h^3)): the first full pass used
    # the two smallest h only, which leaves b h^2 ~ 1e-6 B for chi5_1, whose h0 is 3e-4
    coef = np.polyfit(hs[-3:] / h0, Vs[-3:] / B, 2)
    return lab, {"B": B, "Nbg": Nbg, "rows": rows, "limit": float(coef[-1]) * B}


def check_critical_blowup(quick: bool) -> Check:
    lines, ok = [], True
    tab = zero_table(T_Z)
    fac = (10.0, 1.0, 0.1, 0.01)
    sel = _select(tab, (4,) if quick else BLOWUP_MODULI)
    res = dict(_pool(_blow_job, [(lab, chi, zp, zn, fac) for lab, (chi, zp, zn) in sel]))
    for lab, r in res.items():
        errs = [abs(v - r["B"]) for _, v in r["rows"]]
        ratios = [errs[i] / errs[i + 1] for i in range(len(errs) - 1)]
        rel = abs(r["limit"] - r["B"]) / r["B"]
        lines.append(f"{lab:<7} B = (1/8) sum |Gamma((1-rho)/2)/L'(rho)|^2 = {r['B']:.6e}; (1/4 - c) ||M||_c^2 at h = 1/4 - c = "
                     + ", ".join(f"{h:.1e}: {v / r['B']:.9f} B" for h, v in r["rows"]) +
                     f"; error ratios per decade {', '.join(f'{x:.2f}' for x in ratios)}; extrapolated {rel:.1e} from B")
        ok &= all(5 <= x <= 20 for x in ratios) and rel < 1e-6
    lines.append("h is scaled to h0 = B/||M||^2_{0.2}: below h0 the zeros on the line dominate the norm. For zeta")
    lines.append("B = 2e-10, so the critical-line blow-up only shows up at 1/4 - c ~ 1e-10.")
    return Check("critical-blowup", ok, lines)


# ------------------------------------------------------------------ 4. an off-line zero in coarse and fine spaces
def _offline_job(args):
    kind, h = args
    with mp.workdps(35):
        g1 = mp.zetazero(1).imag
        Lmod = C.moved_zero_L(None, g1, mp.mpf(3) / 5)     # exact 3/5: float 0.6 is off by 2e-17 ~ 1e-5 h
    if kind == "fine":
        dps = 20 + max(0, int(round(-math.log10(h))) - 4)
        with mp.workdps(dps):
            c = mp.mpf(2) / 10 - mp.mpf(h)
            zt = [-g1 / 2, g1 / 2]
        v = C.line_norm_mellin(None, c, t_max=24.0, zeros_t=zt, h_hint=h, dps=dps, L_override=Lmod)
        return kind, h, v
    c = h
    return kind, c, (C.line_norm_mellin(None, c, t_max=24.0, dps=25, L_override=Lmod),
                     C.line_norm_mellin(None, c, t_max=24.0, dps=25))


def check_off_line_control(quick: bool) -> Check:
    lines, ok = [], True
    hs = (1e-10, 1e-11, 1e-12) if not quick else (1e-10, 1e-11)
    jobs = [("fine", h) for h in hs] + [("coarse", c) for c in (0.05, 0.1, 0.15)]
    res = _pool(_offline_job, jobs)
    fine = [(h, v) for k, h, v in res if k == "fine"]
    coarse = [(c, v) for k, c, v in res if k == "coarse"]
    true02 = C.line_norm_mellin(None, 0.2, t_max=24.0)
    # h ||M||^2 = K + h N_bg + O(h^2): Richardson in decades removes the smooth background
    hv = [h * v for h, v in fine]
    Ks = [(10 * hv[i + 1] - hv[i]) / 9 for i in range(len(hv) - 1)]
    with mp.workdps(30):
        g1 = mp.zetazero(1).imag
        Lmod = C.moved_zero_L(None, g1, mp.mpf(3) / 5)
        K_pred = 0
        for rho in (mp.mpc(mp.mpf(3) / 5, g1), mp.mpc(mp.mpf(3) / 5, -g1)):
            K_pred += abs(mp.gamma((1 - rho) / 2)) ** 2 / (8 * abs(mp.diff(Lmod, rho)) ** 2)
        K_pred = float(K_pred)
    lines.append(f"model zeta with its first zero pair moved to beta = 0.6 / 0.4: h ||M||^2 at c = 0.2 - h: " +
                 ", ".join(f"h={h:.0e}: {h * v:.6e}" for h, v in fine) +
                 f"; Richardson K = {', '.join(f'{k:.6e}' for k in Ks)} vs predicted (1/8) sum |Gamma((1-rho)/2)/L'(rho)|^2 "
                 f"over the moved zeros = {K_pred:.6e}: norm ~ K/h, diverges at c = 0.2")
    lines.append(f"true zeta at c = 0.2: {true02:.10g} (finite)")
    spread = max(abs(k - K_pred) / K_pred for k in Ks)
    ok &= spread < 1e-2 and true02 < 10
    for c, (vm, vt) in coarse:
        d = abs(vm - vt) / vt
        lines.append(f"coarse space c = {c} (alpha = {1 - c:.2f}): model norm {vm:.12g} (finite), true norm {vt:.12g}, "
                     f"rel. diff {d:.1e} (the global factor 1 - delta^2/(w - rho)^2 of the model, delta^2/gamma^2 ~ 5e-5)")
        ok &= math.isfinite(vm) and d < 1e-3
    lines.append("In the coarse spaces (c < 0.2) the model with an off-line zero is a perfectly good element: finite norm,")
    lines.append("within 2e-4 of the true one. It leaves the space only at c >= (1 - beta)/2 = 0.2. A coarse space does")
    lines.append("not exclude off-line zeros; only the finest spaces (c -> 1/4) do, and membership there is GRH itself.")
    return Check("off-line-control", ok, lines)


# ------------------------------------------------------------------ 5. what the checks can see
def check_visibility(quick: bool) -> Check:
    lines = []
    for c in (0.05, 0.1, 0.2, 0.25):
        lines.append(f"line Re z = {c}: zeros above |gamma| = {C.visible_height(c):.1f} carry weight |Gamma(c + i gamma/2)|^2 "
                     f"< 1e-16 |Gamma(c)|^2 (invisible in double precision)")
    lines.append(f"for comparison: RH is verified to height {hlr.PLATT_TRUDGIAN_HEIGHT:.2e} (Platt-Trudgian 2021), GRH for")
    lines.append("q <= 4e5 to height 1e8/q (Platt 2016). Every check here only sees zeros far below those heights.")
    return Check("visibility", True, lines)


ALL = [check_line_norm, check_majorana_holomorphic, check_critical_blowup, check_off_line_control, check_visibility]


def run(quick: bool = False, only=None):
    t0 = time.time()
    print("== riemann-lab: Ramanujan + Majorana + Masullo combined formulation (criteria in docs/combined_done_criteria.md) ==")
    print("   (a reformulation of GRH, known in substance: Hardy-Littlewood 1918, Garg-Maji 2022, Dixit 2012;")
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
