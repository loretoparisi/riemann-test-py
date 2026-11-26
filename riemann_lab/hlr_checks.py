"""Hardy-Littlewood-Ramanujan reformulation of GRH: six checks with done criteria fixed before they were
built (docs/hlr_done_criteria.md). Run with `python -m riemann_lab hlr [--quick]`.

The equivalence GRH <=> M_chi(x) = O(x^(-1/4+eps)) is a theorem (Hardy-Littlewood 1918; Garg-Maji 2022).
These checks test the precise statements around it and measure what numerics can and cannot see.
CONSISTENT = every criterion in the row holds. Numerical evidence, not proof.
"""
from __future__ import annotations

import math
import os
import time
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp
import numpy as np

from . import hecke, hlr, zeros
from .extended import Check, _timed

MODULI = (3, 4, 5, 7, 8, 11, 13)
T_HI, T_LO = 80.0, 40.0


# ------------------------------------------------------------------ shared zero data
def characters(moduli=MODULI):
    out = []
    for q in moduli:
        out += hecke.primitive_characters(q)
    return out


def _zeros_job(args):
    chi, T = args
    return chi.label, hecke.line_zeros(chi, T, step=0.1)


_Z: dict = {}


def zero_table(T: float, moduli=MODULI) -> dict:
    """label -> (chi, positive ordinates of L(chi), |negative ordinates| = positive ordinates of L(chibar))."""
    key = (T, tuple(moduli))
    if key in _Z:
        return _Z[key]
    chars = characters(moduli)
    jobs = [(c, T) for c in chars]
    try:
        with ProcessPoolExecutor(min(len(jobs), os.cpu_count() or 1)) as ex:
            zs = dict(ex.map(_zeros_job, jobs))
    except Exception:
        zs = dict(map(_zeros_job, jobs))
    out = {"zeta": (None, zeros.first_zeros(int(T / 2.5) + 5), None)}
    out["zeta"] = (None, out["zeta"][1][out["zeta"][1] <= T], None)
    out["zeta"] = (None, out["zeta"][1], out["zeta"][1])
    for c in chars:
        cb = c.conj()
        lab_b = next(d.label for d in chars if d.q == c.q and all(abs(a - b) < 1e-9 for a, b in zip(d.values, cb.values)))
        out[c.label] = (c, zs[c.label], zs[lab_b])
    _Z[key] = out
    return out


def _cut(z, T):
    return np.asarray(z)[np.asarray(z) <= T]


# ------------------------------------------------------------------ 1. Mellin transform on -1 < Re s < 0
def check_mellin_strip(quick: bool) -> Check:
    lines, ok = [], True
    tab = zero_table(T_HI)
    labels = ["zeta", "chi4", "chi5_2"] + ([] if quick else ["chi7_1"])
    pts = (-0.3, -0.7, complex(-0.5, 3.0), -0.9)
    for lab in labels:
        chi, zp, zn = tab[lab]
        ser = hlr.Series(chi, 0, xmax=50.0)
        ze = hlr.ZeroExpansion(chi, zp, zn)
        worst = 0.0
        for s in pts:
            for X0 in (30.0, 50.0):
                worst = max(worst, hlr.mellin_strip(chi, s, ser, ze, X0)["rel_err"])
        lines.append(f"{lab:<7} int_0^oo x^(s-1) (M - 1/L(1)) dx vs Gamma(s)/L(1-2s) at s = -0.3, -0.7, -0.5+3i, -0.9, "
                     f"cut X0 = 30 and 50: max rel. err {worst:.1e}")
        ok &= worst < 1e-10
    lines.append("Unconditional on -1 < Re s < 0 (Fubini). For M itself on 0 < Re s < 1/4 the integral converges iff GRH.")
    return Check("mellin-strip", ok, lines)


# ------------------------------------------------------------------ 2. Hardy's hypothesis at the edge
def check_hardy_hypothesis_edge(quick: bool) -> Check:
    lines, ok = [], True
    tab = zero_table(T_HI)
    for lab in ("zeta", "chi5_2", "chi7_1"):
        chi, zp, _ = tab[lab]
        e = hlr.hardy_edge(chi, _cut(zp, 40.0))
        sc = [r["scaled"] for r in e["rows"]]
        A = hlr.hardy_A(chi)
        grow = min(sc[1:]) / max(sc[1:])            # (1/4 - delta) max|phi| ~ constant => |phi| ~ (1/4-delta)^-1
        lines.append(f"{lab:<7} max |phi(-delta + i gamma/2)| at delta = " +
                     ", ".join(f"{r['delta']}: {r['max_phi']:.2e}" for r in e["rows"]) +
                     f"; (1/4 - delta) max|phi| constant to {1 - grow:.1e}; Hardy A on Re z = -0.2: {A:.3f} (pi/2 = 1.571)")
        ok &= grow > 0.9 and A <= math.pi / 2 + 0.05
    lines.append("So Hardy's hypothesis holds on every closed half-plane Re z >= -delta, delta < 1/4 (under GRH), with")
    lines.append("constants that blow up as delta -> 1/4: not uniformly on the open half-plane Re z > -1/4.")
    return Check("hardy-hypothesis-edge", ok, lines)


# ------------------------------------------------------------------ 3. Moebius sum to x = 1e11
def _large_x_job(args):
    lab, chi, zp, zn, N, xs = args
    ze = hlr.ZeroExpansion(chi, zp, zn)
    ser = hlr.Series(chi, 0, xmax=100.0)
    e_ser = max(float(abs(complex(ser(x)) - ze(x)[0])) * x**0.25 for x in (1.0, 10.0, 50.0, 100.0))
    mob = hlr.MobiusSum(N, chi)
    e_mob, budget, x14 = 0.0, 0.0, []
    for x in xs:
        v, b = mob(float(x))
        z = ze(float(x))[0]
        e_mob = max(e_mob, (abs(v - z) + b) * x**0.25)
        budget = max(budget, b * x**0.25)
        x14.append(abs(v - ze.trivial_part(float(x))) * x**0.25)
    return lab, {"e_ser": e_ser, "e_mob": e_mob, "budget": budget, "max_nontriv": max(x14), "A": ze.amplitude}


def check_moebius_large_x(quick: bool) -> Check:
    lines, ok = [], True
    moduli = (3, 4, 5) if quick else MODULI
    tab = zero_table(T_HI, MODULI)
    N = 10**6 if quick else 10**7
    xs = np.logspace(2, 9 if quick else 11, 8 if quick else 10)
    jobs = [(lab, chi, zp, zn, N, xs) for lab, (chi, zp, zn) in tab.items() if chi is None or chi.q in moduli]
    workers = max(1, min(len(jobs), (os.cpu_count() or 1)))
    try:
        with ProcessPoolExecutor(workers) as ex:
            res = dict(ex.map(_large_x_job, jobs))
    except Exception:
        res = dict(map(_large_x_job, jobs))
    for lab, r in res.items():
        lines.append(f"{lab:<7} series vs zeros {r['e_ser']:.1e}; Moebius (N = {N:.0e}, J = 3) vs zeros incl. error budget "
                     f"{r['e_mob']:.1e} (budget {r['budget']:.1e}) for 1e2 <= x <= {xs[-1]:.0e}; "
                     f"max x^1/4 |M - trivial| = {r['max_nontriv']:.3e} <= A = {r['A']:.3e}")
        ok &= r["e_ser"] < 1e-10 and r["e_mob"] < 1e-8 and r["max_nontriv"] <= r["A"] * (1 + 1e-6)
    lines.append(f"{len(res)} functions (zeta and every primitive chi mod {', '.join(map(str, moduli))}), all in units of x^(-1/4).")
    return Check("moebius-large-x", ok, lines)


# ------------------------------------------------------------------ 4. reciprocity alpha beta = pi/q
def _recip_job(args):
    lab, chi, zps, zns, alphas = args
    rows = []
    cb = None if chi is None else chi.conj()
    odd = 0 if chi is None else chi.parity
    for alpha in alphas:
        beta = math.pi / (1 if chi is None else chi.q) / alpha
        xm = max(alpha, beta) ** 2 + 1
        ser, serb = hlr.Series(chi, odd, xm), hlr.Series(cb, odd, xm)
        d = []
        for zp, zn in zip(zps, zns):
            r = hlr.reciprocity(chi, alpha, zp, zn, zn, zp, ser, serb)
            d.append(r["diff"])
        rows.append((alpha, abs(r["lhs"]), d))
    return lab, rows


def check_reciprocity(quick: bool) -> Check:
    lines, ok = [], True
    moduli = (3, 4, 5) if quick else MODULI
    tab = zero_table(T_HI, MODULI)
    alphas = (0.7, 1.0, 1.6)
    jobs = [(lab, chi, (_cut(zp, T_LO), zp), (_cut(zn, T_LO), zn), alphas)
            for lab, (chi, zp, zn) in tab.items() if chi is None or chi.q in moduli]
    try:
        with ProcessPoolExecutor(min(len(jobs), os.cpu_count() or 1)) as ex:
            res = dict(ex.map(_recip_job, jobs))
    except Exception:
        res = dict(map(_recip_job, jobs))
    for lab, rows in res.items():
        chi = tab[lab][0]
        par = "zeta" if chi is None else ("even" if chi.parity == 0 else "odd")
        worst = max(max(d) for _, _, d in rows)
        lines.append(f"{lab:<7} ({par:<4}) alpha beta = pi/q, alpha = 0.7, 1, 1.6: max |lhs - rhs| = {worst:.1e} "
                     f"(zeros to T = {T_LO:.0f}: {max(d[0] for _, _, d in rows):.1e}, T = {T_HI:.0f}: "
                     f"{max(d[1] for _, _, d in rows):.1e})")
        ok &= worst < 1e-12
    lines.append("Character analogue of Ramanujan's alpha beta = pi (Dixit 2012, Thms 1.9-1.10, normalised as in hlr.py);")
    lines.append("it needs simple zeros and the convergence of the zero sum, both automatic in this range.")
    return Check("reciprocity", ok, lines)


# ------------------------------------------------------------------ 5. amplitude
def _amp_job(args):
    lab, chi, zp, zn, umax = args
    hi = hlr.ZeroExpansion(chi, zp, zn, trivial=False)
    lo = hlr.ZeroExpansion(chi, _cut(zp, 50.0), _cut(zn, 50.0), trivial=False)
    A, A50 = hi.amplitude, lo.amplitude
    srt = np.sort(np.abs(hi.c))[::-1]
    keep = np.abs(hi.c) > 1e-14 * A
    hi.c, hi.s0 = hi.c[keep], hi.s0[keep]
    sup = hlr.amplitude_sup(hi, umax)
    lowest = np.argsort(np.abs(np.imag(hi.s0)))[:2]
    low20 = float(np.abs(hi.c[np.abs(2 * np.imag(hi.s0)) <= 20.0]).sum() / A)
    return lab, {"A": A, "conv": abs(A - A50) / A, "top2": float(srt[:2].sum() / A), "low20": low20,
                 "lowest2": float(np.abs(hi.c[lowest]).sum() / A), "sup": sup}


def check_amplitude(quick: bool) -> Check:
    lines, ok = [], True
    moduli = (3, 4, 5) if quick else MODULI
    tab = zero_table(T_HI, MODULI)
    umax = 2e4 if quick else 1e5
    jobs = [(lab, chi, zp, zn, umax) for lab, (chi, zp, zn) in tab.items() if chi is None or chi.q in moduli]
    try:
        with ProcessPoolExecutor(min(len(jobs), os.cpu_count() or 1)) as ex:
            res = dict(ex.map(_amp_job, jobs))
    except Exception:
        res = dict(map(_amp_job, jobs))
    for lab, r in res.items():
        lines.append(f"{lab:<7} A = {r['A']:.4e} (T = 50 vs 80: {r['conv']:.0e}); two largest terms carry {100 * r['top2']:.2f}% "
                     f"(the two lowest zeros {100 * r['lowest2']:.2f}%, zeros with |gamma| <= 20: {100 * r['low20']:.4f}%); sup over log x <= {umax:.0e} of x^1/4|M - trivial| "
                     f"= {r['sup'] / r['A']:.6f} A")
        ok &= r["conv"] < 1e-12 and r["low20"] > 0.99 and 0.9 * r["A"] <= r["sup"] <= r["A"] * (1 + 1e-9)
    lines.append("A is the bound x^1/4 |M - trivial| <= A that GRH + simple zeros give; the sup approaching A is the")
    lines.append("Kronecker-type behaviour expected if the ordinates are linearly independent (Grand Simplicity).")
    return Check("amplitude", ok, lines)


# ------------------------------------------------------------------ 6. sensitivity to an off-line zero
def check_sensitivity(quick: bool) -> Check:
    lines, ok = [], True
    zp = zeros.first_zeros(30)
    ze = hlr.ZeroExpansion(None, zp, zp)
    N = 10**6 if quick else 10**7
    lx_max = 9 if quick else 11
    xs = np.logspace(2, lx_max, 2 * lx_max)
    mob = hlr.MobiusSum(N, None)
    eta = []
    for x in xs:
        v, b = mob(float(x))
        eta.append((abs(v - ze(float(x))[0]) + b) * x**0.25)
    eta = np.array(eta)
    delta = 0.2
    detected = {}
    for g in (15, 20, 25, 30, 35, 40, 45, 50, 60, 80):
        extra = hlr.offline_pair_terms(float(g), delta)
        eff = np.abs(np.array([sum(c * x ** (-s) for s, c in extra) for x in xs])) * xs**0.25
        detected[g] = bool(np.any(eff > eta))
    measured = max(g for g, d in detected.items() if d) if any(detected.values()) else 0
    first_missed = min((g for g, d in detected.items() if not d), default=None)
    # prediction from the dominant term with the budget at the top of the range
    pred = hlr.detection_height(delta, float(eta[-1]), lx_max)
    lines.append(f"zeta, Moebius sum N = {N:.0e} vs on-line zero expansion: error budget {eta.min():.1e} .. {eta.max():.1e} "
                 f"x^-1/4 for 1e2 <= x <= 1e{lx_max}")
    lines.append(f"injected quadruple 1/2 +- {delta} +- i gamma (|zeta'(rho)| modelled as 1): detected at gamma = "
                 + ", ".join(str(g) for g, d in detected.items() if d) + "; invisible at "
                 + ", ".join(str(g) for g, d in detected.items() if not d))
    lines.append(f"largest detected height {measured} (first missed {first_missed}); predicted from "
                 f"|Gamma((1-rho)/2)|/2 x^(delta/2) > eta: {pred:.1f}")
    ok &= detected.get(25, False) and not detected.get(60, True) and measured <= pred * 1.15 and \
        (first_missed is None or pred <= first_missed * 1.15)
    A = ze.amplitude
    lines.append(f"log10 x at which an off-line zero would dominate the on-line amplitude A = {A:.2e} (eta = A):")
    for g, src in ((14.13, "first zero"), (1e3, ""), (1e6, ""), (hlr.PLATT_TRUDGIAN_HEIGHT, "RH verified height (Platt-Trudgian)")):
        row = ", ".join(f"delta {d}: {hlr.log10_x_to_see(g, d, A):.3g}" for d in (0.01, 0.1, 0.5))
        lines.append(f"    gamma = {g:.4g} {src}: {row}")
    q, Tq = 13, 1e8 / 13
    lines.append(f"    chi mod {q} at Platt's GRH height 1e8/q = {Tq:.3g}: delta 0.5: {hlr.log10_x_to_see(Tq, 0.5, A):.3g}")
    lines.append("So agreement at reachable x tests only zeros below height ~40, already known to be on the line.")
    return Check("sensitivity", ok, lines)


ALL = [check_mellin_strip, check_hardy_hypothesis_edge, check_moebius_large_x, check_reciprocity, check_amplitude,
       check_sensitivity]


def run(quick: bool = False, only=None):
    t0 = time.time()
    print("== riemann-lab: Hardy-Littlewood-Ramanujan reformulation of GRH (done criteria in docs/hlr_done_criteria.md) ==")
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
