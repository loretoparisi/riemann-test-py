"""Majorana x Masullo: eight checks with done criteria fixed before they were built
(docs/majorana_done_criteria.md). Run with `python -m riemann_lab majorana [--quick]`.

Each check prints CONSISTENT only if every criterion in its row holds, including agreement between two
independent computations. Numerical evidence, not proof.
"""
from __future__ import annotations

import math
import os
import time
import warnings
from concurrent.futures import ProcessPoolExecutor

import mpmath as mp
import numpy as np

from . import majorana as M
from .extended import Check, _timed


def _pmap(fn, jobs):
    workers = min(len(jobs), os.cpu_count() or 1)
    try:
        with ProcessPoolExecutor(workers) as ex:
            return list(ex.map(fn, jobs))
    except Exception:                                   # no multiprocessing: serial
        return list(map(fn, jobs))


# ------------------------------------------------------------------ 1. Majorana's tower
def check_majorana_tower(quick: bool) -> Check:
    lines, ok = [], True
    for j0, name in ((0.0, "integer spins (j0, c) = (0, 1/2)"), (0.5, "half-integer spins (j0, c) = (1/2, 0)")):
        r40 = M.tower_check(j0, 12 + j0 if quick else 20 + j0, 40 + j0)
        r80 = M.tower_check(j0, 12 + j0 if quick else 20 + j0, 80 + j0)
        e80 = float(abs(r80["top_energies"] - r80["expected_energies"]).max())
        d = float(abs(r40["top_energies"] - r80["top_energies"]).max())
        neg = r80["negative"]
        spacelike = bool((abs(neg) < r80["p"]).all())
        rest = float(abs(r80["rest_masses"] - r80["rest_expected"]).max())
        lines.append(f"{name}: {r80['states']} states up to j = {12 + j0 if quick else 20 + j0:g}: so(3,1) error "
                     f"{r80['algebra_err']:.1e}, Hermitian (unitary) error {r80['hermitian_err']:.1e}, "
                     f"Gamma^mu 4-vector error {r80['vector_err']:.1e}")
        lines.append(f"   rest masses m/(s+1/2) = {np.round(r80['rest_masses'], 6).tolist()} (error {rest:.1e}); boosted p = 0.7m: "
                     f"E - sqrt(M_s^2 + p^2) = {e80:.1e} at J = 80, J = 40 vs 80: {d:.1e}; "
                     f"{len(neg)} negative-energy solutions, all spacelike (|E| < p): {spacelike}, max |E| = {abs(neg).max():.4f}")
        ok &= r80["algebra_err"] < 1e-12 and r80["hermitian_err"] < 1e-12 and r80["vector_err"] < 1e-11 \
            and rest < 1e-12 and e80 < 1e-6 and d < 1e-5 and spacelike
    worst = 0
    for half in (False, True):
        for s in (3, 4.5, 6):
            a, b = M.tower_spectral_zeta(s, half), M.tower_spectral_zeta_closed(s, half)
            worst = max(worst, float(abs(a - b) / abs(b)))
    lines.append(f"spectral zeta of the tower, sum over states of (M/m)^s by Euler-Maclaurin vs 2 zeta(s-1) (half-integer) "
                 f"and 2(2^(s-1) - 1) zeta(s-1) (integer) at s = 3, 4.5, 6: max rel. error {worst:.1e}")
    lines.append("   (so zeta(s - 1) is the trace of beta^s on Majorana's half-integer tower; a rewriting, not a spectral "
                 "realisation of the zeros)")
    ok &= worst < 1e-12
    return Check("majorana-tower", ok, lines)


# ------------------------------------------------------------------ 2. discrete series = Hardy-Sobolev lines
def check_discrete_series_hardy_sobolev(quick: bool) -> Check:
    lines, ok = [], True
    alphas = (0.6, 0.75, 1.0, 1.5)
    for a in alphas:
        r = M.sl2_check(a)
        merr = float(abs(r["masses"] - r["masses_expected"]).max())
        lines.append(f"D+_{a:g}: sl(2,R) error {r['comm_err']:.1e}, Casimir - a(a-1) {r['casimir_err']:.1e}, "
                     f"masses m a/(a+n) error {merr:.1e}, J0 = z d/dz + a and J+ = z^2 d/dz + 2a z match the matrices "
                     f"({r['diff_realization_err']:.1e}), Plyushchay basis orthonormal ({M.plyushchay_orthonormal(a):.1e})")
        ok &= r["comm_err"] < 1e-12 and r["casimir_err"] < 1e-12 and merr < 1e-14 and r["diff_realization_err"] < 1e-12 \
            and M.plyushchay_orthonormal(a) < 1e-12
    rng = np.random.default_rng(7)
    c = list(rng.standard_normal(9 if quick else 13))
    res = _pmap(_hs_job, [(a, c) for a in alphas + (0.5,)])
    for a, r in res:
        v = [r["coefficients"], r["laplace"], r["mellin"], r["disk"]]
        err = float(max(abs(x - v[0]) / v[0] for x in v))
        where = "circle" if a == 0.5 else "disk"
        lines.append(f"alpha = {a:g}: ||f||^2 = {mp.nstr(v[0], 12)} from coefficients, Laplace side, Mellin line "
                     f"Re z = {1 - a:g} and {where}: max rel. spread {err:.1e}")
        ok &= err < 1e-10
    for (a, b) in ((0.0, 0.4), (-0.5, 0.25)):
        r = M.masullo_two_line_norm(c[:6], 1.0, a, b)
        (xa, ma), (xb, mb) = r["lines"][a], r["lines"][b]
        hs = r["hardy_sobolev"]
        sandwich = max(xa, xb) <= hs <= xa + xb
        lines.append(f"Masullo W^0_[{a:g},{b:g}] norm^2 {mp.nstr(hs, 10)}; single-line norms (x side = Mellin side) "
                     f"{mp.nstr(xa, 10)} = {mp.nstr(ma, 10)}, {mp.nstr(xb, 10)} = {mp.nstr(mb, 10)}; max <= HS <= sum: {sandwich}")
        ok &= sandwich and abs(xa - ma) / xa < 1e-10 and abs(xb - mb) / xb < 1e-10
    lines.append("So D+_alpha (the internal space of the (2+1)-d Majorana equation) is, through Cayley + Laplace + Mellin, "
                 "the L2 space of the line Re z = 1 - alpha, and Masullo's W^0_[a,b] is D+_(1-a) + D+_(1-b) up to a factor 2")
    return Check("discrete-series-hardy-sobolev", ok, lines)


def _hs_job(args):
    a, c = args
    return a, M.hardy_sobolev_chain(a, c)


# ------------------------------------------------------------------ 3. local RH for the basis
def _local_rh_job(args):
    a, nmax = args
    worst = mp.mpf(0)
    for n in range(1, nmax + 1):
        worst = max(worst, M.local_rh(a, n)["max_dev"])
    sc1 = M.line_sign_changes(a, nmax, 1500)
    sc2 = M.line_sign_changes(a, nmax, 3000)
    q = M.mellin_quadrature_vs_closed(a, 8, [0.3 + 2j, 1, 0.25 + 7j, 2 - 3j, 0.6])
    o = M.line_orthonormality(a, [(0, 0), (3, 3), (2, 5), (7, 7), (1, 6)])
    ctrl = M.mixed_control(a, 6, 5)
    return a, float(worst), sc1, sc2, q, o, ctrl


def check_local_rh_majorana_basis(quick: bool) -> Check:
    lines, ok = [], True
    nmax = 16 if quick else 30
    for a, worst, sc1, sc2, q, o, ctrl in _pmap(_local_rh_job, [(a, nmax) for a in (0.6, 0.75, 1.0, 1.5)]):
        lines.append(f"alpha = {a:g}: zeros of Q_n, n <= {nmax}: max |Re z - {1 - a:g}| = {worst:.1e}; sign changes of "
                     f"i^-n Q_{nmax} on the line: {sc1['sign_changes']} and {sc2['sign_changes']} (two grids; imag/abs "
                     f"<= {max(sc1['max_rel_imag'], sc2['max_rel_imag']):.0e}); quadrature vs closed form {q:.1e}; "
                     f"orthonormal on the line {o:.1e}; control F_6^(a) + F_5^(a+1/2): Re z spread {ctrl:.3f}")
        ok &= worst < 1e-20 and sc1["sign_changes"] == nmax and sc2["sign_changes"] == nmax and q < 1e-15 \
            and o < 1e-12 and ctrl > 1e-2
    lines.append("Every Majorana basis vector satisfies a 'local Riemann hypothesis' on Masullo's line (Meixner-Pollaczek "
                 "zeros are real); a mixture of two different alpha does not")
    return Check("local-rh-majorana-basis", ok, lines)


# ------------------------------------------------------------------ 4. Xi in the basis
def _xi_coeff_job(args):
    lam, nmax, dps = args
    return (lam, dps), M.xi_mp_coefficients(lam, nmax, dps)


def check_xi_discrete_series_expansion(quick: bool) -> Check:
    lines, ok = [], True
    N2 = 140 if quick else 160
    N1 = N2 // 2
    lams = (0.75, 1.0)
    coeff = dict(_pmap(_xi_coeff_job, [(lam, N2, dps) for lam in lams for dps in (30, 40)]))
    gam = [mp.zetazero(k).imag for k in range(1, 5)]
    zeros_at = {}
    for lam in lams:
        a30, a40 = coeff[(lam, 30)], coeff[(lam, 40)]
        floor = min(abs(x) for x in a40[N2 - 20:N2 + 1:2])
        idx = [n for n in range(0, N2 + 1, 2) if abs(a40[n]) > max(mp.mpf(10) ** -20, 100 * floor)]
        agree = max(abs(a30[n] - a40[n]) / abs(a40[n]) for n in idx)
        with mp.workdps(40):
            rec = max(abs(M.xi_mp_partial(a40, lam, N2, mp.mpf(x)) - mp.re(M.xi(mp.mpf(0.5) + 2j * x)))
                      for x in np.linspace(0, 10, 21)) / M.xi(mp.mpf(0.5))
            z1 = M.xi_mp_zeros(a40, lam, N1, 4, 40)
            z2 = M.xi_mp_zeros(a40, lam, N2, 4, 40)
        e1 = [float(abs(z - g)) for z, g in zip(z1, gam)]
        e2 = [float(abs(z - g)) for z, g in zip(z2, gam)]
        zeros_at[lam] = z2
        lines.append(f"lambda = {lam:g}: |a_n| from {mp.nstr(abs(a40[0]), 4)} to {mp.nstr(abs(a40[N2]), 3)} at n = {N2} "
                     f"(smallest of the last ten {mp.nstr(floor, 2)}); dps 30 vs 40 agree to {mp.nstr(agree, 2)} on {len(idx)} coefficients; "
                     f"S_{N2} - Xi(2x) on [0, 10]: {mp.nstr(rec, 2)} of Xi(0)")
        lines.append(f"   zeros gamma_1..4 from real roots of S_N: errors at N = {N1}: {', '.join(f'{e:.1e}' for e in e1)}; "
                     f"at N = {N2}: {', '.join(f'{e:.1e}' for e in e2)}")
        ok &= agree < 1e-8 and rec < 1e-12 and all(b < 1e-4 for b in e2) and all(b <= a for a, b in zip(e1, e2))
    same = max(float(abs(x - y)) for x, y in zip(zeros_at[0.75], zeros_at[1.0]))
    lines.append(f"lambda = 3/4 and 1 give the same four zeros to {same:.1e}. Resolving the k-th zero needs degree N ~ gamma_k^2/3: "
                 "the expansion converges, but it is not an efficient route to the zeros")
    ok &= same < 1e-4
    return Check("xi-discrete-series-expansion", ok, lines)


# ------------------------------------------------------------------ 5. Majorana stars of Jensen polynomials
def check_majorana_stars_jensen(quick: bool) -> Check:
    lines, ok = [], True
    dmax, nmax = (8, 20) if quick else (10, 30)
    beta = M.xi_taylor_beta(dmax + nmax + 1, dps=60)
    with mp.workdps(60):
        tay = mp.taylor(lambda z: M.xi(mp.mpf(0.5) + z), 0, 12)
        terr = max(abs(tay[2 * k] - beta[k]) / beta[k] for k in range(7))
        gam = M.gorz_gamma(beta)
        bad, worstY, worst_pol = 0, 0.0, 0.0
        for d in range(1, dmax + 1):
            for n in range(0, nmax + 1):
                cf = M.jensen_coeffs(gam, d, n)
                if M.sturm_real_roots(cf) != d:
                    bad += 1
                st = M.majorana_stars(cf)
                worstY = max(worstY, float(abs(st[:, 1]).max()))
        lines.append(f"GORZ gamma(n), n <= {dmax + nmax}: quadrature of Riemann's Phi vs mpmath Taylor of xi (n <= 6): "
                     f"{mp.nstr(terr, 2)}")
        lines.append(f"Jensen J^(d,n), d <= {dmax}, n <= {nmax}: {(dmax) * (nmax + 1) - bad} of {dmax * (nmax + 1)} hyperbolic "
                     f"(exact Sturm counts); Majorana stars of the spin-d/2 states: max |Y| = {worstY:.1e} (all on the great "
                     f"circle Y = 0)")
        ok &= terr < 1e-20 and bad == 0 and worstY < 1e-12
        for (a, b, must) in ((2.0, 0.4, True), (1.0, 0.4, False), (3.0, 0.45, False)):
            pg = M.gorz_gamma(M.perturbed_beta(beta, a, b))
            found = []
            for d in range(1, dmax + 1):
                for n in range(0, nmax + 1):
                    cf = M.jensen_coeffs(pg, d, n)
                    if M.sturm_real_roots(cf) != d:
                        found.append((d, n, float(abs(M.majorana_stars(cf)[:, 1]).max())))
            s = f"s = {0.5 + b:g} +- {a:g}i, {0.5 - b:g} +- {a:g}i"
            if found:
                lines.append(f"control, Xi with an extra zero quadruple at {s}: {len(found)} non-hyperbolic J^(d,n), first "
                             f"(d, n) = {found[0][:2]}, stars leave the circle by up to {max(f[2] for f in found):.3f}")
            else:
                lines.append(f"control, Xi with an extra zero quadruple at {s}: not detected for d <= {dmax}, n <= {nmax} "
                             "(low-degree Jensen polynomials only see off-line zeros at small height)")
            if must:
                ok &= bool(found) and max(f[2] for f in found) > 1e-3
    return Check("majorana-stars-jensen", ok, lines)


# ------------------------------------------------------------------ 6. Majorana random matrices vs quadratic L
def _bins(edges, W):
    return np.array([np.mean(W(np.linspace(a, b, 400))) for a, b in zip(edges[:-1], edges[1:])])


def check_majorana_random_matrices_quadratic_L(quick: bool) -> Check:
    lines, ok = [], True
    samples = 6000 if quick else 20000
    edges = np.arange(0, 3.0001, 0.2)
    dist = {}
    for cls in ("D", "C"):
        x = M.bdg_samples(cls, 50, samples, seed=11 if cls == "D" else 12)
        dens = np.histogram(x, edges)[0] / (samples * 0.2)
        dist[cls] = {nm: float(np.sqrt(np.sum((dens - _bins(edges, W)) ** 2) * 0.2))
                     for nm, W in (("SO(even)", M.W_so_even), ("USp", M.W_usp))}
        lines.append(f"class {cls} BdG (2N = 100, {samples} samples, particle-hole symmetry error "
                     f"{M.bdg_particle_hole_err(cls):.0e}): L2 distance of the near-zero density to 1 + sinc "
                     f"{dist[cls]['SO(even)']:.3f}, to 1 - sinc {dist[cls]['USp']:.3f}")
    ok &= dist["D"]["SO(even)"] < 0.05 and dist["C"]["USp"] < 0.05 and dist["D"]["SO(even)"] < dist["D"]["USp"] \
        and dist["C"]["USp"] < dist["C"]["SO(even)"]
    # theta-integral zeros vs hecke (mpmath Hurwitz route)
    from . import hecke
    worst = 0.0
    for d in (5, 8, 12, 13, 17, -3, -4, -7, -8, -11):
        q = abs(d)
        chi = hecke.Character(q, f"kron{d}", tuple(complex(M.kronecker(d, n)) for n in range(q)))
        z1 = hecke.line_zeros(chi, 10.0, step=0.05)
        z2 = M.QuadraticL(d).zeros(10.0)
        worst = max(worst, float(abs(z1 - z2).max()) if len(z1) == len(z2) else math.inf)
    lines.append(f"zeros of L(s, chi_d) below 10 for 10 discriminants: theta integral vs hecke.Z agree to {worst:.1e}")
    ok &= worst < 1e-8
    D = 1000 if quick else 3000
    ds = M.fundamental_discriminants(100, D)
    res = [M._qL_zeros_job((d, 2.0)) for d in ds]          # serial: cheap, and numpy threads oversubscribe a pool
    xs = np.concatenate([z * math.log(abs(d)) / (2 * math.pi) for d, z in res])
    xs = xs[xs <= 2]
    e2 = np.arange(0, 2.0001, 0.25)
    dens = np.histogram(xs, e2)[0] / (len(ds) * 0.25)
    laws = {"USp (class C)": M.W_usp, "SO(even) (class D)": M.W_so_even, "U": lambda x: np.ones_like(np.asarray(x, float))}
    dd = {nm: float(np.sqrt(np.sum((dens - _bins(e2, W)) ** 2) * 0.25)) for nm, W in laws.items()}
    lines.append(f"{len(ds)} fundamental discriminants 100 < |d| <= {D}, zeros scaled by log|d|/2pi: one-level density "
                 f"on [0, 2] in bins of 1/4: {np.round(dens, 2).tolist()}")
    lines.append("   L2 distance to " + ", ".join(f"{k} {v:.3f}" for k, v in dd.items())
                 + f"; first bin {dens[0]:.3f} (U: 1, USp: {_bins(e2, M.W_usp)[0]:.3f})")
    ok &= dd["USp (class C)"] < dd["SO(even) (class D)"] and dd["USp (class C)"] < dd["U"] and dens[0] < 0.5
    lines.append("   the quadratic Dirichlet family (Masullo's GL(1) over Q) has the repulsion of class C, not of the "
                 "Majorana class D; at |d| ~ 10^3 the finite-conductor corrections are still large (cf. Rubinstein 2001)")
    return Check("majorana-random-matrices-quadratic-L", ok, lines)


# ------------------------------------------------------------------ 7. Thomas-Fermi
def check_majorana_thomas_fermi(quick: bool) -> Check:
    lines, ok = [], True
    nterms = 200 if quick else 400
    a = M.tf_series(nterms, dps=50)
    with mp.workdps(50):
        return _thomas_fermi_body(a, nterms, quick, lines, ok)


def _thomas_fermi_body(a, nterms, quick, lines, ok):
    lam = (mp.sqrt(73) - 7) / 2
    S = mp.fsum(a)
    tail = abs(a[-1]) * (a[-1] / a[-2]) / (1 - a[-1] / a[-2])
    slope = -mp.cbrt(mp.mpf(3) / 16) * S
    ratios = [float(a[n] / a[n - 1]) for n in (10, 50, 100, nterms - 1)]
    lines.append(f"a1 = {mp.nstr(a[1], 15)} = 9 - sqrt 73 ({mp.nstr(a[1] - (9 - mp.sqrt(73)), 2)}), = 2(1 - lambda) "
                 f"({mp.nstr(a[1] - 2 * (1 - lam), 2)}), lambda = (sqrt 73 - 7)/2 = {mp.nstr(lam, 12)}")
    lines.append(f"{nterms} terms: phi'(0) = -(3/16)^(1/3) sum a_n = {mp.nstr(slope, 18)} (tail ~{mp.nstr(tail, 2)}); "
                 f"literature {mp.nstr(M.TF_SLOPE, 18)}: {mp.nstr(abs(slope - M.TF_SLOPE), 2)}")
    lines.append(f"a_n/a_(n-1) at n = 10, 50, 100, {nterms - 1}: {', '.join(f'{r:.4f}' for r in ratios)} "
                 "(Majorana: ~4/5; it is ~0.80 at n ~ 10 and creeps up slowly)")
    ok &= abs(a[1] - (9 - mp.sqrt(73))) < 1e-40 and abs(a[1] - 2 * (1 - lam)) < 1e-40 and abs(slope - M.TF_SLOPE) < 1e-10
    sh = M.tf_shoot()
    lines.append(f"independent shooting (double precision, s = sqrt x): phi'(0) = {sh['slope']:.15f}, "
                 f"vs series {float(abs(sh['slope'] - slope)):.1e}")
    ok &= abs(sh["slope"] - float(slope)) < 1e-9
    with mp.workdps(25):
        tf = M.TFMajorana(a[:150], dps=25)
        ode = M.tf_ode_phi(M.TF_SLOPE)
        xs = [0.1, 0.3, 1, 2, 5, 10, 20]
        exact = {x: ode(x) for x in xs}
        full = max(abs(tf.phi_at(x) - exact[x]) / exact[x] for x in xs)
        errs = {}
        for k in (10, 12, 15):
            tk = M.TFMajorana(a[:k], dps=25, kmax=60)
            errs[k] = float(max(abs(tk.phi_at(x) - exact[x]) / exact[x] for x in xs))
        lines.append(f"phi(x) on [0.1, 20]: full series vs 30-digit ODE {mp.nstr(full, 2)}; truncated to 10, 12, 15 terms: "
                     f"max rel. error {errs[10] * 100:.2f}%, {errs[12] * 100:.2f}%, {errs[15] * 100:.2f}% (Esposito reports "
                     f"'order of 0.1%' for 10 terms; we find 0.1% needs ~15)")
        ok &= full < 1e-8 and errs[10] < 1e-2 and errs[15] < errs[12] < errs[10]
        pts = (0.5, 1.5, 1 + 1j, 2.5) if not quick else (0.5, 1 + 1j)
        worst = 0
        for s in pts:
            m1 = tf.mellin_truncated(s, 100)
            m2 = M.tf_ode_mellin_truncated(M.TF_SLOPE, s, 100)
            worst = max(worst, abs(m1 - m2) / abs(m1))
        full_m = [(s, tf.mellin(s), M.tf_ode_mellin(M.TF_SLOPE, s)) for s in (0.5, 1 + 1j)]
        lines.append(f"Mellin Int_0^100 x^(s-1) phi dx at s = {', '.join(str(p) for p in pts)}: Majorana's one quadrature vs "
                     f"ODE {mp.nstr(worst, 2)}; full Mellin M phi(0.5) = {mp.nstr(mp.re(full_m[0][1]), 12)}, "
                     f"M phi(1+i) = {mp.nstr(full_m[1][1], 10)} (ODE + fitted tail: within "
                     f"{mp.nstr(max(abs(x - y) / abs(x) for _, x, y in full_m), 2)})")
        ok &= worst < 1e-6
        res = [(e, e * tf.mellin(3 - e)) for e in (0.01, 0.005, 0.0025)]
        (e1, v1), (e2, v2), (e3, v3) = res
        r0 = (v1 * e2 * e3 / ((e1 - e2) * (e1 - e3)) + v2 * e1 * e3 / ((e2 - e1) * (e2 - e3))
              + v3 * e1 * e2 / ((e3 - e1) * (e3 - e2)))
        lfit = M.tf_lambda_fit(tf)
        lines.append(f"pole of M phi at s = 3: eps M phi(3 - eps) = {', '.join(mp.nstr(mp.re(v), 7) for _, v in res)}, "
                     f"extrapolated {mp.nstr(mp.re(r0), 7)} (Sommerfeld 144); exponent from x^3 phi/144 - 1 at x <= 10^6: "
                     f"{lfit:.5f} vs {float(lam):.5f}")
        ok &= abs(lfit - float(lam)) < 1e-3
    return Check("majorana-thomas-fermi", ok, lines)


# ------------------------------------------------------------------ 8. Majorana algebras and moonshine
def check_majorana_algebras_moonshine(quick: bool) -> Check:
    lines, ok = [], True
    for k in M.NS_KINDS:
        r = M.norton_sakuma_check(k, pairs=500 if quick else 2000)
        good = r["commutative"] and r["form_associative"] and r["norton_min"] >= 0 and r["semisimple"] \
            and r["dim_V1"] == 1 and r["fusion"] \
            and r["tau_automorphism"] and r["identity_length"] == r["length_expected"]
        good = good and all(x in (M.Fr(1), M.Fr(0), M.Fr(1, 4), M.Fr(1, 32)) for x in r["spectrum"])
        lines.append(f"V_{k} (dim {r['dim']}): M1 {r['form_associative']}, M2 min {r['norton_min']:.3g} >= 0, "
                     f"spec ad(a) = {{{', '.join(str(x) for x in r['spectrum'])}}}, dim V_1 = {r['dim_V1']}, fusion "
                     f"{r['fusion']}, tau(a) automorphism {r['tau_automorphism']}, |id| = {r['identity_length']} "
                     f"(Table 2.3: {r['length_expected']})")
        ok &= good
    c = M.j_coefficients(10)
    lines.append(f"j - 744 = q^-1 + {c[2]} q + {c[3]} q^2 + {c[4]} q^3 + ... (c(1) = 196884 = dim of the Griess "
                 f"algebra V_M, the Majorana algebra of the Monster)")
    ok &= c[2] == 196884 and c[3] == 21493760 and c[4] == 864299970
    errs = {}
    for K in ((100, 400) if quick else (200, 1000)):
        errs[K] = [abs(M.rademacher_j(n, K) - c[n + 1]) for n in range(1, 6)]
    k1, k2 = sorted(errs)
    lines.append(f"Rademacher's Kloosterman-Bessel series, |error| for n = 1..5: cutoff {k1}: "
                 f"{', '.join(f'{e:.3f}' for e in errs[k1])}; cutoff {k2}: {', '.join(f'{e:.3f}' for e in errs[k2])}")
    ok &= all(e < 0.5 for e in errs[k2]) and sum(errs[k2]) < sum(errs[k1])
    w = M.weil_bound_check(300 if quick else 1000)
    lines.append(f"Weil: max |K(m,n;c)| / (d(c) gcd(m,n,c)^(1/2) c^(1/2)) = {w['max_ratio']:.4f} for m, n <= 5, "
                 f"c <= {300 if quick else 1000} (RH for curves over F_p, a theorem)")
    ok &= w["max_ratio"] <= 1 + 1e-9
    dec = []
    for n, mult in M.MCKAY_THOMPSON.items():
        v = sum(m * dmn for m, dmn in zip(mult, M.MONSTER_DIMS))
        dec.append(v == c[n + 1])
    lines.append(f"McKay-Thompson: c(1) = 1 + 196883, c(2) = 1 + 196883 + 21296876, c(3) = 2 + 2*196883 + 21296876 + "
                 f"842609326: {all(dec)}")
    ok &= all(dec)
    return Check("majorana-algebras-moonshine", ok, lines)


ALL = [check_majorana_tower, check_discrete_series_hardy_sobolev, check_local_rh_majorana_basis,
       check_xi_discrete_series_expansion, check_majorana_stars_jensen, check_majorana_random_matrices_quadratic_L,
       check_majorana_thomas_fermi, check_majorana_algebras_moonshine]


def run(quick: bool = False, only=None):
    warnings.filterwarnings("ignore")
    t0 = time.time()
    print("== riemann-lab: Majorana x Masullo checks (done criteria in docs/majorana_done_criteria.md) ==")
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
