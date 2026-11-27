"""Lean 4 bridge for the combined norm identity (lean/RiemannLab/*.lean).

python -m riemann_lab lean runs three things and prints one report:

1. build:  `lake build` in lean/ (Lean 4 + Mathlib). Compiling means every proof in the
           library type-checks.
2. audit:  `lake env lean Audit.lean`, which prints `#print axioms` for each theorem. A theorem
           counts as PROVED only if it depends on nothing beyond Lean's three standard axioms
           (propext, Classical.choice, Quot.sound). A theorem that depends on `sorryAx` is OPEN:
           Lean checked that its statement is well-typed, not that it is true.
3. numerics: mpmath checks of the same statements (the Lean definitions transcribed to Python),
           so the two sides are seen to talk about the same objects.

The audit fails if a theorem we list as proved depends on sorryAx, if a theorem we list as open
has silently stopped depending on it (then the list is stale), or if any other axiom shows up.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import time
from pathlib import Path

import mpmath as mp

LEAN_DIR = Path(__file__).resolve().parent.parent / "lean"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# theorem -> what it says (kept in sync with lean/Audit.lean)
PROVED = {
    "RiemannLab.mellin_g": "int_0^oo x^(s-1) (e^-x - 1) dx = Gamma(s) on -1 < Re s < 0",
    "RiemannLab.integrableOn_g_norm": "x^(sigma-1) |e^-x - 1| is integrable on (0, oo) for -1 < sigma < 0",
    "RiemannLab.scale_identity": "x^-1 ((x^2)^-1)^(-s) = x^-(1-2s) for x > 0 (complex powers)",
    "RiemannLab.integral_norm_F": "int |n-th Mellin integrand| <= K(sigma) n^(2 sigma - 1) (Tonelli bound)",
    "RiemannLab.mellin_Mt_eq_LSeries": "Mellin(M~_chi)(s) = Gamma(s) L(mu chi, 1-2s) on -1 < Re s < 0 (Fubini)",
    "RiemannLab.mellin_Mt": "Mellin(M~_chi)(s) = Gamma(s) / L(1-2s, chi) on -1 < Re s < 0",
    "RiemannLab.combined_norm_identity": "int |M~_chi|^2 x^(1-2 alpha) dx = (1/2pi) int |Gamma/L|^2 dt, "
                                         "1 < alpha < 2, given the named hypothesis MellinPlancherel",
    "RiemannLab.plancherel": "int |F f|^2 = int |f|^2 for f in L1 n L2 (integral form of Plancherel)",
    "RiemannLab.mellin_plancherel": "int_0^oo |f|^2 x^(2c-1) dx = (1/2pi) int |Mellin f(c+it)|^2 dt",
    "RiemannLab.combined_norm_identity_unconditional": "the combined norm identity on 1 < alpha < 2 "
                                                       "with no hypothesis",
    "RiemannLab.mellinOn_differentiableAt": "int_S t^(s-1) f(t) dt is holomorphic where t^(sigma-1)|f| "
                                            "is integrable (dominated differentiation)",
    "RiemannLab.K_mul_LFunction_eq": "K(s) L(1-2s, chi) = Gamma(s+1) on -1 < Re s < 0",
    "RiemannLab.LFunction_ne_zero_of_finiteNorms": "finite norms for chi => L(w, chi) != 0 on 1/2 < Re w < 1",
    "RiemannLab.grh_of_finiteNorms": "finite norms for chi and chi^-1 => GRH(chi), chi primitive",
}
OPEN = {
    "RiemannLab.grh_iff_finite_norm": "GRH(chi) <=> int |M_chi|^2 x^(1-2 alpha) < oo for all alpha in (3/4, 1)",
    "RiemannLab.blowup_limit": "(alpha - 3/4) ||M_chi||^2 -> (1/8) sum |Gamma((1-rho)/2)/L'(rho)|^2, "
                               "given GRH, simple zeros, absolute convergence",
}
NAMED_HYPOTHESES = {
    "RiemannLab.MellinPlancherel": "Mellin-Plancherel on Re s = c; now proved (mellin_plancherel) and "
                                   "discharged for M~_chi in combined_norm_identity_unconditional",
}


def find_lake() -> str | None:
    p = shutil.which("lake")
    if p:
        return p
    cand = Path.home() / ".elan" / "bin" / "lake"
    return str(cand) if cand.exists() else None


def _run(cmd, timeout):
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan" / "bin") + os.pathsep + env.get("PATH", "")
    return subprocess.run(cmd, cwd=LEAN_DIR, capture_output=True, text=True, timeout=timeout, env=env)


def build(timeout: int = 4 * 3600) -> dict:
    lake = find_lake()
    if lake is None:
        return {"ok": False, "skipped": True, "log": "lake not found (install elan: https://lean-lang.org)"}
    t0 = time.time()
    r = _run([lake, "build"], timeout)
    out = r.stdout + r.stderr
    sorry_warnings = sorted(set(re.findall(r"(RiemannLab/\S+\.lean):\d+:\d+: warning: declaration uses 'sorry'", out)))
    return {"ok": r.returncode == 0, "skipped": False, "seconds": time.time() - t0,
            "sorry_files": sorry_warnings, "log": out[-4000:]}


_AX = re.compile(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]")
_NOAX = re.compile(r"'([\w.]+)' does not depend on any axioms")


def parse_axioms(text: str) -> dict[str, set[str]]:
    res = {m.group(1): {a.strip() for a in m.group(2).split(",") if a.strip()} for m in _AX.finditer(text)}
    res.update({m.group(1): set() for m in _NOAX.finditer(text)})
    return res


def classify(axioms: dict[str, set[str]]) -> dict:
    problems = []
    for name in PROVED:
        if name not in axioms:
            problems.append(f"{name}: missing from audit output")
        elif "sorryAx" in axioms[name]:
            problems.append(f"{name}: listed as proved but depends on sorryAx")
        elif axioms[name] - STANDARD_AXIOMS:
            problems.append(f"{name}: extra axioms {sorted(axioms[name] - STANDARD_AXIOMS)}")
    for name in OPEN:
        if name not in axioms:
            problems.append(f"{name}: missing from audit output")
        elif "sorryAx" not in axioms[name]:
            problems.append(f"{name}: listed as open but no longer uses sorryAx (update the lists)")
    return {"ok": not problems, "problems": problems,
            "proved": [n for n in PROVED if n in axioms and axioms[n] <= STANDARD_AXIOMS],
            "open": [n for n in OPEN if n in axioms and "sorryAx" in axioms[n]]}


def audit(timeout: int = 1800) -> dict:
    lake = find_lake()
    if lake is None:
        return {"ok": False, "skipped": True, "problems": ["lake not found"]}
    r = _run([lake, "env", "lean", "Audit.lean"], timeout)
    out = r.stdout + r.stderr
    res = classify(parse_axioms(out))
    res.update({"skipped": False, "raw": out, "returncode": r.returncode})
    res["ok"] = res["ok"] and r.returncode == 0
    return res


# ------------------------------------------------------------------ numerics of the Lean statements
def g(t):
    """Lean `RiemannLab.g`: e^-t - 1."""
    return mp.exp(-t) - 1


def mellin_g_numeric(s) -> dict:
    s = mp.mpc(s)
    with mp.workdps(30):
        # [0, 40] by quadrature; on [40, oo): int x^(s-1) e^-x by quadrature, int x^(s-1) = -40^s/s exactly
        # [0, 1] termwise: e^-x - 1 = sum_{k>=1} (-x)^k/k!, int_0^1 x^(s-1+k) dx = 1/(s+k)
        val = mp.nsum(lambda k: (-1) ** k / (mp.factorial(k) * (s + k)), [1, mp.inf])
        val += mp.quad(lambda x: x ** (s - 1) * g(x), [1, 10, 40])
        val += mp.quad(lambda x: x ** (s - 1) * mp.exp(-x), [40, mp.inf]) + mp.mpf(40) ** s / s
        ex = mp.gamma(s)
    return {"s": complex(s), "rel_err": float(abs(val - ex) / abs(ex))}


def K_numeric(sigma: float) -> dict:
    """K(sigma) = int t^(sigma-1) |e^-t - 1| dt = -Gamma(sigma) (closed form, not used by Lean: Lean only needs K finite)."""
    with mp.workdps(30):
        val = -mp.nsum(lambda k: (-1) ** k / (mp.factorial(k) * (sigma + k)), [1, mp.inf])
        val += mp.quad(lambda t: t ** (sigma - 1) * (1 - mp.exp(-t)), [1, 10, 40])
        val += -mp.quad(lambda t: t ** (sigma - 1) * mp.exp(-t), [40, mp.inf]) - mp.mpf(40) ** sigma / sigma
        ex = -mp.gamma(sigma)
    return {"sigma": sigma, "rel_err": float(abs(val - ex) / abs(ex))}


def scale_identity_numeric(x: float, s) -> float:
    s = mp.mpc(s)
    lhs = mp.mpf(1 / x ** 2) ** (-s) / x
    rhs = 1 / mp.mpf(x) ** (1 - 2 * s)
    return float(abs(lhs - rhs) / abs(rhs))


def Mt_direct(chi, x: float, nmax: int = 200000) -> complex:
    """Lean `RiemannLab.Mt`: sum_n mu(n) chi(n)/n (e^{-x/n^2} - 1), truncated (tail <= x/(2 nmax^2))."""
    from . import hlr
    import numpy as np
    mu = hlr._mu(nmax)
    n = np.arange(1, nmax + 1, dtype=float)
    if chi is None:
        cv = np.ones(nmax)
    else:
        vals = np.array([complex(v) for v in hlr.exact_values(chi)])
        cv = vals[np.arange(1, nmax + 1) % chi.q]
    return complex(np.sum(mu[1:nmax + 1] * cv / n * np.expm1(-x / n ** 2)))


def numerics() -> dict:
    from . import combined as C, hecke, hlr
    out = {}
    out["mellin_g"] = [mellin_g_numeric(s) for s in (-0.5, -0.25 + 3j, -0.9 + 1j, -0.1 - 2j)]
    out["K"] = [K_numeric(sg) for sg in (-0.5, -0.9, -0.1)]
    out["scale_identity"] = max(scale_identity_numeric(x, s) for x in (1, 2, 7) for s in (-0.5 + 1j, -0.3 - 4j))
    chi = hecke.primitive_characters(5)[1]  # complex character mod 5
    ser = hlr.Series(chi, 0, xmax=30)
    c0 = complex(hlr.inv_L1(chi))
    out["Mt_vs_M_minus_c0"] = max(abs(Mt_direct(chi, x) - (complex(ser(x)) - c0)) for x in (0.5, 3.0, 20.0))
    ze = hlr.ZeroExpansion(chi, hecke.line_zeros(chi, 40.0), hecke.line_zeros(chi.conj(), 40.0))
    out["mellin_Mt"] = [hlr.mellin_strip(chi, s, ser, ze, 30.0) for s in (-0.5 + 1j, -0.3 - 2j)]
    for c in (-0.5, -0.25):
        x = C.line_norm_x(c, ser, ze, 30.0, hlr.inv_L1(chi))
        m = C.line_norm_mellin(chi, c, t_max=40.0)
        out[f"combined_norm_c={c}"] = {"x_side": x, "L_side": m, "rel_err": abs(x - m) / m}
    tol = 1e-8
    ok = (all(r["rel_err"] < 1e-12 for r in out["mellin_g"]) and all(r["rel_err"] < 1e-12 for r in out["K"])
          and out["scale_identity"] < 1e-12 and out["Mt_vs_M_minus_c0"] < 1e-8
          and all(r["rel_err"] < tol for r in out["mellin_Mt"])
          and all(out[k]["rel_err"] < tol for k in out if k.startswith("combined_norm")))
    out["ok"] = ok
    return out


def run(skip_build: bool = False, skip_numerics: bool = False) -> bool:
    print("== riemann-lab lean: combined norm identity in Lean 4 + Mathlib ==\n")
    ok = True
    if not skip_build:
        b = build()
        if b["skipped"]:
            print("[build]    SKIPPED:", b["log"])
            ok = False
        else:
            print(f"[build]    lake build: {'OK' if b['ok'] else 'FAILED'} in {b['seconds']:.0f}s; "
                  f"files with sorry: {b['sorry_files'] or 'none'}")
            if not b["ok"]:
                print(b["log"])
            ok &= b["ok"]
    a = audit()
    if a.get("skipped"):
        print("[audit]    SKIPPED: lake not found")
        ok = False
    else:
        print(f"[audit]    {'OK' if a['ok'] else 'FAILED'}")
        for n in PROVED:
            print(f"   PROVED  {n.split('.')[-1]:24s} {PROVED[n]}")
        for n in NAMED_HYPOTHESES:
            print(f"   HYPOTH  {n.split('.')[-1]:24s} {NAMED_HYPOTHESES[n]}")
        for n in OPEN:
            print(f"   OPEN    {n.split('.')[-1]:24s} {OPEN[n]}  [sorry]")
        for p in a["problems"]:
            print("   problem:", p)
        ok &= a["ok"]
    if not skip_numerics:
        nm = numerics()
        print(f"[numerics] {'OK' if nm['ok'] else 'FAILED'}")
        print("   mellin_g rel errors:", ", ".join(f"{r['rel_err']:.1e}" for r in nm["mellin_g"]))
        print("   K(sigma) = -Gamma(sigma) rel errors:", ", ".join(f"{r['rel_err']:.1e}" for r in nm["K"]))
        print(f"   scale_identity max rel error: {nm['scale_identity']:.1e}")
        print(f"   Lean Mt (direct sum) vs M_chi - 1/L(1,chi), chi mod 5: max abs diff {nm['Mt_vs_M_minus_c0']:.1e}")
        print("   mellin_Mt rel errors (chi mod 5):", ", ".join(f"{r['rel_err']:.1e}" for r in nm["mellin_Mt"]))
        for k in nm:
            if k.startswith("combined_norm"):
                r = nm[k]
                print(f"   {k}: x side {r['x_side']:.12f}, L side {r['L_side']:.12f}, rel err {r['rel_err']:.1e}")
        ok &= nm["ok"]
    print("\nresult:", "PASS" if ok else "FAIL")
    return ok
