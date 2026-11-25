"""Command line: python -m riemann_lab {report,extended,ramanujan,plots,verify,turing} ..."""
from __future__ import annotations

import argparse
import time

from . import criteria, explicit_formula, primes, rmt, toy_trace, zeros


def report(quick: bool = False):
    t0 = time.time()
    N = 10**5 if quick else 10**6
    print("== riemann-lab report: numerical checks of RH and its equivalents ==\n")
    rep, z = zeros.verify_window(100, 1000 if quick else 5000)
    print("[zeros]   ", rep)
    print("[gram]    ", zeros.gram_law_stats(0, 1000))
    print("[primes]  ", primes.check_schoenfeld(N))
    r = criteria.robin_bruteforce(N)
    print(f"[robin]    n in (5040, {N}]: holds={r['holds']}, max ratio {r['max_ratio']:.6f} at n={r['argmax_n']} (e^γ={r['e_gamma']:.6f})")
    ca = criteria.robin_at_ca(2000 if quick else 20000)
    print(f"[robin-CA] {ca['count']} colossally abundant n up to 10^{ca['log10_n_max']:.0f}: holds={ca['holds']}, max ratio {ca['max_ratio']:.7f}")
    lg = criteria.lagarias_bruteforce(N)
    print(f"[lagarias] n <= {N}: holds={lg['holds']}")
    m = criteria.mertens_summary(N)
    print(f"[mertens]  x <= {N}: max |M(x)|/sqrt(x) = {m['max_abs_M_over_sqrt_x']:.4f} at x={m['at_x']}")
    lam = criteria.li_coefficients(20)
    print(f"[li]       lambda_1..20 all positive: {(lam > 0).all()}  (lambda_1 = {lam[0]:.12f})")
    first = zeros.first_zeros(60)
    print("[explicit] Weil/Guinand formula, Gaussian test function at r0=20:\n" +
          "\n".join("           " + line for line in str(explicit_formula.check(first, 20.0, 1.0)).splitlines()))
    print("[toy]      Masullo toy trace (spectral vs geometric):", toy_trace.demo(7.0, 0.6, 0.8))
    if not quick:
        _, zz = zeros.verify_window(1e5, 1.02e5)
        print("[gue]      KS distance of spacings near t=1e5:", rmt.ks_distances(rmt.spacings(zz)))
    print(f"\ndone in {time.time() - t0:.1f}s")


def main(argv=None):
    p = argparse.ArgumentParser(prog="riemann_lab")
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("report", help="run every check and print a summary")
    r.add_argument("--quick", action="store_true")
    pl = sub.add_parser("plots", help="write the example figures")
    pl.add_argument("--out", default="plots")
    e = sub.add_parser("extended", help="Turing, de Bruijn-Newman, Nyman-Beurling, Weil, rigorous Li, Riesz, Redheffer")
    e.add_argument("--quick", action="store_true")
    e.add_argument("--only", nargs="*", help="subset, e.g. turing de_bruijn_newman nyman_beurling weil li_rigorous riesz redheffer")
    rm = sub.add_parser("ramanujan", help="Ramanujan x Masullo: Master Theorem, Hardy-Littlewood-Ramanujan, Dirichlet L zeros, tau")
    rm.add_argument("--quick", action="store_true")
    rm.add_argument("--only", nargs="*", help="subset, e.g. rmt_mellin hardy_littlewood_ramanujan hecke_zeros "
                    "hecke_explicit_formula zero_multiplicities euler_products ramanujan_robin ramanujan_tau")
    v = sub.add_parser("verify", help="Turing-style check that all zeros in (T1,T2] are on the line")
    v.add_argument("T1", type=float)
    v.add_argument("T2", type=float)
    tu = sub.add_parser("turing", help="Turing's method: N(T) at both ends from the S(t) integral bound, no argument principle")
    tu.add_argument("T1", type=float)
    tu.add_argument("T2", type=float)
    a = p.parse_args(argv)
    if a.cmd == "report":
        report(a.quick)
    elif a.cmd == "extended":
        from . import extended
        extended.run(a.quick, a.only)
    elif a.cmd == "ramanujan":
        from . import ramanujan_checks
        ramanujan_checks.run(a.quick, a.only)
    elif a.cmd == "turing":
        from . import turing
        print(turing.turing_verify(a.T1, a.T2))
    elif a.cmd == "plots":
        from . import plots
        for path in plots.make_all(a.out):
            print("wrote", path)
    else:
        rep, _ = zeros.verify_window(a.T1, a.T2)
        print(rep)


if __name__ == "__main__":
    main()
