"""Majorana regularisation of the combined norm: five checks with criteria fixed before they were built
(docs/majorana_reg_done_criteria.md). Run with `python -m riemann_lab majorana-reg [--quick]`.

Verdict stated in advance and tested here: a regularisation that is finite at a fixed parameter for every chi
is not a GRH criterion; in the limit it gives back `grh_iff_finite_norm` (Lean: `grh_iff_truncNorm_bounded`).
Numerical evidence, not proof.
"""
from __future__ import annotations

import math
import os
import time
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp
import numpy as np

from . import combined as C, majorana_reg as R
from .extended import Check, _timed
from .hlr_checks import zero_table

NS = (256, 1024, 4096)


def _pool(fn, jobs):
    try:
        with ProcessPoolExecutor(min(len(jobs), os.cpu_count() or 1)) as ex:
            return list(ex.map(fn, jobs))
    except Exception:
        return list(map(fn, jobs))


def _tab():
    return zero_table(40.0, (3, 4))


# ------------------------------------------------------------------ 1. coefficients
def _coef_job(args):
    lab, chi, a = args
    c15 = R.tower_coeffs_true(chi, a, 4096, 2 ** 15)
    c16 = R.tower_coeffs_true(chi, a, 4096, 2 ** 16)
    return (lab, a), (float(abs(c15 - c16).max() / abs(c16).max()), float(np.sum(abs(c16) ** 2)),
                      C.line_norm_mellin(chi, 1 - a))


def check_tower_coefficients(quick: bool) -> Check:
    lines, ok = [], True
    tab = _tab()
    res = dict(_pool(_coef_job, [(lab, tab[lab][0], a) for lab in ("zeta", "chi4") for a in (0.8, 0.9)]))
    for (lab, a), (d, tot, N) in res.items():
        rel = abs(tot - N) / N
        lines.append(f"{lab:<6} alpha = {a}: FFT 2^15 vs 2^16 {d:.1e}; sum_(m<4096) |c_m|^2 = {tot:.10f}, line norm {N:.10f} "
                     f"(rel. {rel:.1e})")
        ok &= d < 1e-9 and (lab != "zeta" or rel < 1e-6)
    chi, zp, _ = tab["chi4"]
    terms = R.model_terms(0.8, zp[0], chi=chi)
    for a in (0.8, 0.95):
        cm = R.tower_coeffs_model(terms, a, 4096, 2 ** 16)
        ce = R.tower_coeffs_model_exact(terms, a, 4096)
        d = float(abs(cm - ce).max() / abs(ce).max())
        lines.append(f"model terms (chi4, beta = 0.8), alpha = {a}: FFT vs exact binomial convolution {d:.1e}")
        ok &= d < 1e-9
    lines.append("c_m = <M_chi, psi_m> in Majorana's basis of D+ (Laguerre functions of L^2(t^(1-2alpha) dt)).")
    return Check("tower-coefficients", ok, lines)


# ------------------------------------------------------------------ 2. the cut-off for the true L
def _cut_job(args):
    lab, chi, a = args
    c = R.tower_coeffs_true(chi, a, 4096, 2 ** 16)
    Nn = R.partial_norms(c, NS)
    mono = bool(np.all(np.diff(np.cumsum(abs(c) ** 2)) >= 0))
    return (lab, a), (Nn, C.line_norm_mellin(chi, 1 - a), mono)


def check_tower_cutoff_true(quick: bool) -> Check:
    lines, ok = [], True
    tab = _tab()
    jobs = [(lab, tab[lab][0], a) for lab in ("zeta", "chi4", "chi3_1") for a in (0.8, 0.9)]
    res = dict(_pool(_cut_job, jobs))
    for (lab, a), (Nn, N, mono) in res.items():
        gaps = [(N - v) / N for v in Nn]
        if lab == "zeta":
            lines.append(f"{lab:<6} alpha = {a}: relative gap N - N_n at n = 256, 1024, 4096: "
                         f"{', '.join(f'{g:.1e}' for g in gaps)} (M(0) = 1/zeta(1) = 0: fast)")
            ok &= mono and abs(gaps[-1]) < 1e-6
            continue
        p = math.log(gaps[-2] / gaps[-1]) / math.log(NS[-1] / NS[-2])
        pred = 2 * (1 - a)
        lines.append(f"{lab:<6} alpha = {a}: relative gap at n = 256, 1024, 4096: {', '.join(f'{g:.2e}' for g in gaps)}; "
                     f"fitted exponent {p:.3f} vs 2(1 - alpha) = {pred:.3f}")
        ok &= mono and abs(p - pred) < 0.05
    lines.append("For chi != 1 the cut-off converges like n^(-2(1-alpha)): M_chi(0) = 1/L(1, chi) != 0 is a constant near x = 0,")
    lines.append("expanded in a basis that vanishes there like x^(2alpha-1). With the zeros' n^(-(2alpha-3/2)) this is slowest at both")
    lines.append("ends of (3/4, 1): the tower cut-off does not stabilise the norm, it converges more slowly than direct quadrature.")
    return Check("tower-cutoff-true", ok, lines)


# ------------------------------------------------------------------ 3. the cut-off with an off-line zero
def _off_job(args):
    kind, a = args
    tab = _tab()
    chi, zp, _ = tab["chi4"]
    terms = R.model_terms(0.8, zp[0], chi=chi)
    if kind == "fixed":
        ct = R.tower_coeffs_true(chi, a, 4096, 2 ** 16)
        cm = R.tower_coeffs_model(terms, a, 4096, 2 ** 16)
        ns = (64, 256, 1024, 4096)
        return (kind, a), (R.partial_norms(ct, ns), R.partial_norms(ct + cm, ns))
    cm = R.tower_coeffs_model(terms, a, 2 ** 17, 2 ** 20)
    ns = [2 ** j for j in range(6, 18)]
    D = R.partial_norms(cm, ns)
    inc = np.diff(D)
    ex = [math.log(inc[i + 1] / inc[i]) / math.log(2) for i in range(len(inc) - 1)]
    win = [float(np.mean(ex[i:i + 3])) for i in range(0, len(ex) - 2, 3)]
    return (kind, a), (D, win)


def check_tower_cutoff_offline(quick: bool) -> Check:
    lines, ok = [], True
    res = dict(_pool(_off_job, [("fixed", 0.8), ("grow", 0.8), ("grow", 0.95)]))
    T, M = res[("fixed", 0.8)]
    rel = [abs(m - t) / t for t, m in zip(T, M)]
    lines.append(f"chi4, first pair moved to beta = 0.8 (norm infinite for alpha < 0.9), alpha = 0.8: N_n true "
                 f"{', '.join(f'{t:.6f}' for t in T)}, model {', '.join(f'{m:.6f}' for m in M)} at n = 64 ... 4096; "
                 f"rel. diff max {max(rel):.1e}")
    ok &= max(rel) < 1e-4
    D8, w8 = res[("grow", 0.8)]
    D95, w95 = res[("grow", 0.95)]
    lines.append(f"off-line part sum_(m<n) |c_D,m|^2 at n = 2^6 ... 2^17: alpha = 0.8: {D8[0]:.2e} -> {D8[-1]:.2e}; "
                 f"alpha = 0.95: {D95[0]:.2e} -> {D95[-1]:.2e}")
    lines.append(f"growth exponents averaged over 3 doublings: alpha = 0.8: {', '.join(f'{x:.2f}' for x in w8)} "
                 f"(-> 0.2); alpha = 0.95: {', '.join(f'{x:.2f}' for x in w95)} (-> -0.1)")
    diffs = [x - y for x, y in zip(w8, w95)]
    lines.append(f"differences {', '.join(f'{d:.2f}' for d in diffs)} vs predicted 0.3")
    ok &= all(abs(d - 0.3) < 0.1 for d in diffs[-2:])
    lines.append("A fixed cut-off gives the model and the true L the same number to 1e-4: it cannot see the off-line zero.")
    lines.append("The divergence shows only as n -> oo, slowly and log-periodically, and still unresolved at n = 1.3e5.")
    return Check("tower-cutoff-offline", ok, lines)


# ------------------------------------------------------------------ 4. Tikhonov on the boost at the critical line
def _tik_job(args):
    kind, f = args
    tab = _tab()
    if kind == "model":
        chi = None
        with mp.workdps(35):
            g1 = mp.zetazero(1).imag
            Lmod = C.moved_zero_L(None, g1, mp.mpf(3) / 5)
        zp = [z for z in tab["zeta"][1] if abs(z - float(g1)) > 1e-6]
        zt = [-z / 2 for z in zp] + [z / 2 for z in zp] + [-float(g1) / 2, float(g1) / 2]
        rhos = [mp.mpc(0.5, z) for z in zp] + [mp.mpc(0.5, -z) for z in zp]
        S = R.tikhonov_limit_pred(None, rhos, L_override=Lmod)
        L_override, Nbg = Lmod, 1.25
    else:
        chi, zp, zn = tab[kind]
        zt = [-z / 2 for z in zp] + [z / 2 for z in zn]
        rhos = [mp.mpc(0.5, z) for z in zp] + [mp.mpc(0.5, -z) for z in zn]
        S = R.tikhonov_limit_pred(chi, rhos)
        L_override, Nbg = None, (1.25 if kind == "zeta" else 2.5)
    se = f * S / Nbg
    eps = se ** 2
    dps = 20 + max(0, int(-math.log10(se)) - 4)
    v = R.tikhonov_critical(chi, eps, zt, L_override=L_override, dps=dps)
    return (kind, f), (eps, v, S)


def check_tikhonov_critical(quick: bool) -> Check:
    lines, ok = [], True
    fs = (10.0, 1.0, 0.1, 0.01)
    jobs = [(k, f) for k in ("zeta", "chi4", "model") for f in fs]
    res = dict(_pool(_tik_job, jobs))
    for kind in ("zeta", "chi4", "model"):
        rows = [res[(kind, f)] for f in fs]
        S = rows[0][2]
        sv = [math.sqrt(e) * v for e, v, _ in rows]
        rich = [(10 * sv[i + 1] - sv[i]) / 9 for i in range(len(sv) - 1)]
        rel = abs(rich[-1] - S) / S
        name = {"zeta": "zeta", "chi4": "chi4", "model": "model zeta (pair 1 moved to 3/5)"}[kind]
        lines.append(f"{name}: N_eps at eps = {', '.join(f'{e:.1e}' for e, _, _ in rows)}: "
                     f"{', '.join(f'{v:.6g}' for _, v, _ in rows)} (all finite); sqrt(eps) N_eps Richardson "
                     f"{', '.join(f'{x:.6e}' for x in rich)} vs S = sum |Gamma((1-rho)/2)|^2/(4|L'(rho)|) = {S:.6e} "
                     f"(rel. {rel:.1e})")
        ok &= all(math.isfinite(v) for _, v, _ in rows) and rel < 1e-2
    lines.append("For the model, S is summed over the on-line zeros only: the moved pair contributes no eps^(-1/2) term.")
    lines.append("So at fixed eps the regularised critical norm is finite for every L, with or without off-line zeros; as")
    lines.append("eps -> 0 it diverges like S/sqrt(eps) from the zeros on the line, which says nothing about zeros off it.")
    return Check("tikhonov-critical", ok, lines)


# ------------------------------------------------------------------ 5. verdict
def check_verdict(quick: bool) -> Check:
    lines = [
        "regularisation            | finite at fixed parameter | GRH criterion at fixed parameter | in the limit",
        "tower cut-off N_n (x side)| yes, every chi (Lean: truncNorm_integrable) | no | GRH <=> bounded in n (Lean: grh_iff_truncNorm_bounded)",
        "Tikhonov on the boost     | yes, every L (check 4)    | no                               | diverges ~ S/sqrt(eps) from on-line zeros only",
        "Speed: the cut-off converges like n^(-2(1-alpha)) and n^(-(2alpha-3/2)) (check 2), slower than direct quadrature;",
        "Tikhonov trades the divergence for an eps^(-1/2) law. Neither stabilises the criterion; the term is rejected as a",
        "regularisation of the GRH criterion, as agreed. What remains useful is the tower itself (Lean: tower_casimir etc.).",
    ]
    return Check("verdict", True, lines)


ALL = [check_tower_coefficients, check_tower_cutoff_true, check_tower_cutoff_offline, check_tikhonov_critical, check_verdict]


def run(quick: bool = False, only=None):
    t0 = time.time()
    print("== riemann-lab: Majorana regularisation of the combined norm (criteria in docs/majorana_reg_done_criteria.md) ==")
    print("   (numerical evidence, not proof; 'CONSISTENT' = every criterion met)\n")
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
