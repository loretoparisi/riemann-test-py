"""Example figures. ``python -m riemann_lab plots --out docs/plots`` writes them all."""
from __future__ import annotations

import math
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp
import numpy as np

from . import criteria, explicit_formula, primes, rmt, toy_trace, zeros

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


ALL = [plot_Z, plot_pi, plot_robin, plot_mertens, plot_li, plot_gue, plot_explicit, plot_toy]


def make_all(out="plots"):
    return [f(out) for f in ALL]
