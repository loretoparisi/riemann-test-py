"""Example figures. ``python -m riemann_lab plots --out docs/plots`` writes them all."""
from __future__ import annotations

import math
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

from . import (criteria, dbn, explicit_formula, li_rigorous, nyman_beurling, primes, riesz_redheffer, rmt,
               toy_trace, turing, weil, zeros, zeta)

# Fixed categorical order (validated palette); text stays in neutral ink.
C = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4", "#008300", "#6250d6", "#e34948"]
INK, INK2, GRID, SURF = "#0b0b0b", "#52514e", "#e4e3df", "#fcfcfb"

plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "axes.edgecolor": INK2,
    "axes.labelcolor": INK, "text.color": INK, "xtick.color": INK2, "ytick.color": INK2,
    "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.8,
    "axes.spines.top": False, "axes.spines.right": False, "lines.linewidth": 2,
    "font.size": 10, "axes.titlesize": 12, "axes.titleweight": "bold", "legend.frameon": False,
    "figure.dpi": 110, "savefig.dpi": 160, "savefig.bbox": "tight",
})


def _save(fig, out, name):
    os.makedirs(out, exist_ok=True)
    path = os.path.join(out, name)
    fig.savefig(path)
    plt.close(fig)
    return path


def plot_Z(out):
    t = np.linspace(0.5, 60, 1500)
    Z = [float(mp.siegelz(x)) for x in t]
    absz = [float(abs(mp.zeta(mp.mpc(0.5, x)))) for x in t]
    z = zeros.first_zeros(13)
    fig, ax = plt.subplots(figsize=(9, 3.6))
    ax.plot(t, absz, color=C[1], lw=1.5, label="|ζ(1/2 + it)|")
    ax.plot(t, Z, color=C[0], label="Hardy Z(t)")
    ax.axhline(0, color=INK2, lw=0.8)
    ax.plot(z, np.zeros_like(z), "o", ms=6, color=C[0], mec=SURF, mew=2, label="zeros on the line")
    ax.set(title="Zeros of ζ on the critical line are sign changes of the real function Z(t)", xlabel="t")
    ax.legend(loc="upper left", ncol=3)
    return _save(fig, out, "01_hardy_Z.png")


def plot_pi(out):
    z = zeros.first_zeros(100)
    x = np.linspace(2, 60, 700)
    pr = primes.sieve(100)
    fig, ax = plt.subplots(figsize=(9, 4.2))
    ax.step(x, primes.prime_pi(x, pr), where="post", color=INK, lw=1.5, label="π(x)")
    ax.plot(x, primes.Li(x), color=C[3], label="Li(x)")
    ax.plot(x, primes.R(x), color=C[2], label="Riemann R(x)")
    for k, col in ((10, C[1]), (100, C[0])):
        ax.plot(x, primes.pi_explicit(x, z[:k]), color=col, lw=1.4, label=f"explicit formula, {k} zero pairs")
    ax.set(title="Each zero adds one harmonic: the explicit formula rebuilds the prime staircase",
           xlabel="x", ylabel="count")
    ax.legend(loc="upper left")
    return _save(fig, out, "02_prime_staircase.png")


def plot_robin(out):
    r = criteria.robin_at_ca(20000)
    lln = np.log(r["log_n"])
    fig, ax = plt.subplots(figsize=(9, 3.8))
    ax.plot(lln, r["ratio"], color=C[0], lw=1.5, label="σ(n) / (n log log n) at colossally abundant n")
    ax.axhline(criteria.E_GAMMA, color=C[7], lw=1.5, ls="--", label="e^γ (RH ⇔ always below, n > 5040)")
    ax.set(title=f"Robin's criterion holds at CA numbers up to n ≈ 10^{r['log10_n_max']:.0f}",
           xlabel="log log n", ylabel="ratio", ylim=(1.70, 1.79))
    ax.legend(loc="lower right")
    return _save(fig, out, "03_robin.png")


def plot_mertens(out, N=10**7):
    M = criteria.mertens(N)
    idx = np.unique(np.geomspace(1, N, 40000).astype(int))
    fig, ax = plt.subplots(figsize=(9, 3.6))
    ax.plot(idx, M[idx] / np.sqrt(idx), color=C[0], lw=1)
    for y in (1, -1):
        ax.axhline(y, color=C[7], lw=1, ls="--")
    ax.set_xscale("log")
    ax.set(title="Mertens function M(x)/√x up to 10^7 (RH ⇔ M(x) = O(x^{1/2+ε}))", xlabel="x", ylabel="M(x)/√x")
    return _save(fig, out, "04_mertens.png")


def plot_li(out, nmax=40):
    lam = criteria.li_coefficients(nmax, dps=90)
    n = np.arange(1, nmax + 1)
    asym = n / 2 * np.log(n) + (np.euler_gamma - 1 - math.log(2 * math.pi)) / 2 * n
    fig, ax = plt.subplots(figsize=(9, 3.6))
    ax.plot(n, lam, "o", ms=6, color=C[0], mec=SURF, mew=2, label="λ_n (Keiper-Li)")
    ax.plot(n, asym, color=C[1], lw=1.5, label="asymptotic (n/2)(log n − 1 + γ − log 2π)")
    ax.set(title="Li's criterion: RH ⇔ λ_n ≥ 0 for all n", xlabel="n", ylabel="λ_n")
    ax.legend(loc="upper left")
    return _save(fig, out, "05_li_coefficients.png")


def plot_gue(out, T1=1e5, T2=1.04e5):
    _, z = zeros.verify_window(T1, T2)
    s = rmt.spacings(z)
    ks = rmt.ks_distances(s)
    u = np.linspace(0, 3.2, 300)
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(11, 4))
    a1.hist(s, bins=50, density=True, color=C[0], alpha=0.35, edgecolor=SURF, label=f"{len(s)} spacings near t = {T1:.0e}")
    a1.plot(u, rmt.gue_pdf(u), color=C[0], label=f"GUE (KS {ks['GUE']:.3f})")
    a1.plot(u, rmt.goe_pdf(u), color=C[1], lw=1.5, label=f"GOE (KS {ks['GOE']:.3f})")
    a1.plot(u, rmt.poisson_pdf(u), color=C[3], lw=1.5, label=f"Poisson (KS {ks['Poisson']:.3f})")
    a1.set(title="Nearest-neighbour spacings", xlabel="normalised spacing s", ylabel="density")
    a1.legend()
    c, d = rmt.pair_correlation(z)
    a2.bar(c, d, width=c[1] - c[0], color=C[0], alpha=0.35, edgecolor=SURF, label="zeros")
    a2.plot(u, rmt.montgomery(u), color=C[0], label="Montgomery 1 − (sin πu / πu)²")
    a2.set(title="Pair correlation", xlabel="u", ylabel="density")
    a2.legend(loc="lower right")
    fig.suptitle("Zeta zeros follow random-matrix (GUE) statistics", fontweight="bold")
    return _save(fig, out, "06_gue.png")


def plot_explicit(out):
    z = zeros.first_zeros(80)
    centres = np.linspace(10, 60, 101)
    true = np.abs(explicit_formula.scan(z, centres))
    missing = np.abs(explicit_formula.scan(np.delete(z, 4), centres))   # drop the 5th zero (32.94)
    off = np.abs([explicit_formula.check(z, r0, 1.0, extra_zeros=[(0.55, 40.0)]).residual for r0 in centres])
    fig, ax = plt.subplots(figsize=(9, 3.8))
    ax.semilogy(centres, np.maximum(true, 1e-17), color=C[0], label="true zeros: residual at round-off")
    ax.semilogy(centres, missing, color=C[1], lw=1.5, label="one zero removed (γ = 32.94)")
    ax.semilogy(centres, off, color=C[7], lw=1.5, label="one off-line zero added (β = 0.55, t = 40)")
    ax.set(title="Weil explicit formula: primes pin down the zeros exactly",
           xlabel="test-function centre r₀", ylabel="|spectral − geometric|", ylim=(1e-17, 10))
    ax.legend(loc="upper left")
    return _save(fig, out, "07_explicit_formula_scan.png")


def plot_toy(out, gamma=7.0, width=0.5):
    L = math.log(gamma)
    centres = np.linspace(-0.8, L + 0.8, 120)
    geo, spec = [], []
    for c in centres:
        phi = lambda u, c=c: toy_trace.bump(u, c, width)
        a, b = c - width, c + width
        geo.append(toy_trace.trace_geometric(phi, gamma, a, b))
        spec.append(toy_trace.trace_spectral(phi, gamma, a, b, mmax=200))
    fig, ax = plt.subplots(figsize=(9, 3.6))
    ax.axvspan(width, L - width, color=C[2], alpha=0.12, label="support inside (1, γ): trace = 0")
    ax.plot(centres, geo, color=C[0], label="geometric: log γ · Σ φ(γ^k)")
    ax.plot(centres, spec, color=C[1], lw=1.2, ls="--", label="spectral: Σ M(φ)(2πim / log γ)")
    ax.set(title=f"Masullo's toy trace formula on R>0 / γ^Z (γ = {gamma:g})",
           xlabel="centre of φ in log t", ylabel="Trace A(φ)")
    ax.legend(loc="upper center")
    return _save(fig, out, "08_toy_trace.png")


def plot_turing(out, n=138067, h_gram=40):
    """Running integral of S~(t) from the Gram point g_n, against Turing's bound."""
    an = turing.turing_anchor(n, h_gram)
    g, h = an.g, an.h
    zs, _ = turing.certified_sign_changes(g - h - 1, g + h + 1)
    ts = np.linspace(g - h, g + h, 1201)
    S = np.array([np.sum((zs > g) & (zs <= t)) - np.sum((zs > t) & (zs <= g)) for t in ts]) + n + 1 \
        - (zeta.theta(ts) / np.pi + 1)
    dt = ts[1] - ts[0]
    I = np.concatenate(([0], np.cumsum(0.5 * (S[1:] + S[:-1]) * dt)))
    I -= I[600]                                         # integral from g_n
    a, b = turing.TRUDGIAN
    B = a + b * np.log(ts / (2 * np.pi))
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(11, 3.8))
    a1.plot(ts - g, S, color=C[0], lw=1, label="S~(t) = N~(t) − θ(t)/π − 1")
    a1.axhline(0, color=INK2, lw=0.8)
    a1.set(title=f"Believed S(t) around g_{n} ≈ {g:.1f}", xlabel="t − g_n", ylabel="S~(t)")
    a1.legend(loc="upper left")
    a2.plot(ts - g, I, color=C[0], label="∫ from g_n of S~")
    a2.fill_between(ts - g, -B, B, color=C[2], alpha=0.15, label="Trudgian bound ±(2.067 + 0.059 log(t/2π))")
    a2.plot(ts - g, (ts - g) * 1.0 + 0 * ts, color=C[7], lw=1, ls="--", label="what one missing zero would add")
    a2.set(title=f"E ∈ [{an.E_lower:+.2f}, {an.E_upper:+.2f}] ⇒ N(g_n) = {an.N} exactly",
           xlabel="t − g_n", ylabel="∫ S~ dt", ylim=(-3.5, 3.5))
    a2.legend(loc="lower right", fontsize=8)
    fig.suptitle("Turing's method: an exact zero count from an integral bound", fontweight="bold")
    return _save(fig, out, "09_turing.png")


def plot_dbn(out):
    wins = [(14, 1000), (1e4, 1.1e4), (1e5, 1.02e5), (1e6, 1.002e6)]
    est = [dbn.window_estimate(*w) for w in wins]
    # heat flow of Lehmer's pair
    g1, g2 = 7005.062866174921, 7005.100564672647
    p = dbn.window_estimate(6900, 7100, edge=0.0)
    tc = p["max_t_c"]
    x = np.linspace(2 * g1 - 0.12, 2 * g2 + 0.12, 161)
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(11, 3.8))
    for t, col in ((0.0, C[0]), (tc / 2, C[2]), (tc, C[3]), (2 * tc, C[7])):
        v = np.array([float(mp.re(dbn.H(t, xx, nodes=30)) * mp.exp(mp.pi * xx / 8)) for xx in x])
        a1.plot(x / 2, v / np.abs(v).max(), color=col, lw=1.5, label=f"t = {t:+.1e}")
    a1.axhline(0, color=INK2, lw=0.8)
    a1.set(title="Backward heat flow merges Lehmer's pair (γ ≈ 7005.06)", xlabel="γ = x/2",
           ylabel="H_t(x) (rescaled)")
    a1.legend(loc="lower left", fontsize=8)
    heights = [np.sqrt(w[0] * w[1]) if w[0] > 14 else 300 for w in wins]
    a2.semilogx(heights, [-e["max_t_c"] for e in est], "o-", color=C[0], mec=SURF, mew=2,
                label="−(latest collision time) in the window")
    a2.set_yscale("log")
    a2.set(title="Finite-window estimates creep up to Λ ≥ 0", xlabel="height t", ylabel="−t_c")
    a2.legend(loc="upper right")
    fig.suptitle("de Bruijn–Newman constant: RH ⇔ Λ = 0 (Λ ≥ 0 by Rodgers–Tao)", fontweight="bold")
    return _save(fig, out, "10_de_bruijn_newman.png")


def plot_nyman_beurling(out, N=200):
    d2 = nyman_beurling.distances(N, 60)
    n = np.arange(1, N + 1)
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(11, 3.8))
    a1.loglog(n, d2, color=C[0], label="d_N²")
    a1.loglog(n[1:], nyman_beurling.C0 / np.log(n[1:]), color=C[1], lw=1.5, ls="--", label="C0 / log N (conjectured)")
    a1.set(title="Báez-Duarte distances d_N² → 0", xlabel="N", ylabel="d_N²")
    a1.legend()
    a2.semilogx(n[1:], d2[1:] * np.log(n[1:]), color=C[0], label="d_N² log N")
    a2.axhline(nyman_beurling.C0, color=C[7], lw=1.5, ls="--", label="Burnol: liminf ≥ 2 + γ − log 4π")
    a2.set(title="Approaching Burnol's constant from above", xlabel="N", ylim=(0.04, 0.1))
    a2.legend()
    fig.suptitle("Nyman–Beurling criterion: RH ⇔ d_N → 0", fontweight="bold")
    return _save(fig, out, "11_nyman_beurling.png")


def plot_weil(out):
    z = zeros.first_zeros(120)
    s_, m, du = 0.07, 16, 0.3
    u = du * np.arange(m)
    Mg = weil.weil_matrix(s_, u)
    Ms = weil.weil_matrix(s_, u, z, side="spectral")
    Mf = weil.weil_matrix(s_, u, z, extra_zeros=[(0.6, 20.0)], side="spectral")
    k = np.arange(1, m + 1)
    fig, ax = plt.subplots(figsize=(9, 3.8))
    ax.semilogy(k, np.linalg.eigvalsh(Mg), "o", color=C[0], ms=7, mec=SURF, mew=2, label="from primes (geometric side)")
    ax.semilogy(k, np.linalg.eigvalsh(Ms), "x", color=C[1], ms=6, label="from zeros (spectral side)")
    ef = np.linalg.eigvalsh(Mf)
    ax.semilogy(k, np.abs(ef), "s", color=C[7], ms=4, mfc="none", label="zeros + one off-line zero 0.6+20i (|λ|)")
    neg = ef < 0
    ax.semilogy(k[neg], np.abs(ef[neg]), "s", color=C[7], ms=8, label="… negative eigenvalue")
    ax.set(title="Weil positivity: the 16×16 Weil matrix built from primes is positive definite",
           xlabel="eigenvalue index", ylabel="eigenvalue")
    ax.legend(loc="lower right", fontsize=8)
    return _save(fig, out, "12_weil.png")


def plot_li_rigorous(out, N=5000):
    r = li_rigorous.li_coefficients_rigorous(N)
    n = r.n.astype(float)
    dev = (r.mid - li_rigorous.asymptotic(n)) / (np.sqrt(n) * np.log(n + 1))
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(11, 3.8))
    a1.loglog(n, r.mid, color=C[0], label="λ_n (Arb enclosure midpoints)")
    a1.loglog(n, li_rigorous.asymptotic(n).clip(1e-3), color=C[1], lw=1.2, ls="--", label="(n/2)(log n − 1 + γ − log 2π)")
    a1.set(title=f"λ_1 … λ_{N} certified positive", xlabel="n", ylabel="λ_n")
    a1.legend(loc="upper left")
    a2.plot(n, dev, color=C[0], lw=0.8)
    a2.set(title="(λ_n − asymptotic) / (√n log n): bounded, as RH predicts", xlabel="n")
    fig.suptitle("Li's criterion with ball arithmetic", fontweight="bold")
    return _save(fig, out, "13_li_rigorous.png")


def plot_riesz_redheffer(out):
    s = riesz_redheffer.riesz_summary(1e10, 300)
    x, R, Rz = s["x"], s["R"], s["R_zeros"]
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(11, 3.8))
    a1.semilogx(x, R / x**0.25, color=C[0], label="R(x)/x^{1/4} (Möbius form)")
    a1.semilogx(x, Rz / x**0.25, color=C[1], lw=1.2, ls="--", label="zero expansion, 30 zeros")
    a1.set(title="Riesz: RH ⇔ R(x) = O(x^{1/4+ε})", xlabel="x", ylim=(-3e-4, 3e-4))
    a1.legend(loc="lower left", fontsize=8)
    ns = np.array([50, 100, 200, 400, 800, 1600, 3000])
    M = criteria.mertens(int(ns.max()))
    top, dets = [], []
    for n in ns:
        A = riesz_redheffer.redheffer_matrix(int(n)).astype(float)
        ev = np.linalg.eigvals(A)
        top.append(np.abs(ev).max())
        sg, ld = np.linalg.slogdet(A)
        dets.append(sg * math.exp(ld))
    a2.plot(ns, np.array(top) / np.sqrt(ns), "o-", color=C[0], mec=SURF, mew=2, label="largest eigenvalue / √n")
    a2b = a2.twinx()
    a2b.plot(ns, dets, "s", color=C[1], ms=5, label="det A_n")
    a2b.plot(ns, M[ns], "x", color=INK, ms=7, label="M(n)")
    a2b.set_ylabel("det A_n = M(n)")
    a2.set(title="Redheffer matrices", xlabel="n")
    a2.legend(loc="upper right", fontsize=8)
    a2b.legend(loc="lower right", fontsize=8)
    return _save(fig, out, "14_riesz_redheffer.png")


ALL = [plot_Z, plot_pi, plot_robin, plot_mertens, plot_li, plot_gue, plot_explicit, plot_toy,
       plot_turing, plot_dbn, plot_nyman_beurling, plot_weil, plot_li_rigorous, plot_riesz_redheffer]
NEW = ALL[8:]


def make_all(out="plots", only_new: bool = False):
    return [f(out) for f in (NEW if only_new else ALL)]
