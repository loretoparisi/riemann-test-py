# Ramanujan + Majorana + Masullo: one combined formulation (done criteria written before building)

## The statement

For a primitive Dirichlet character chi (or chi = 1, zeta) put, as in the Hardy-Littlewood-Ramanujan check,
    M_chi(x) = sum_n mu(n) chi(n)/n e^{-x/n^2} = sum_k (-x)^k / (k! L(2k+1, chi))        (Ramanujan's form, RMT)
and let F_chi(w) = int_0^oo M_chi(t) e^{iwt} dt = sum_n mu(n) chi(n) n / (1 - i n^2 w), Im w > 0.

The three pieces meet at one norm. For 1/2 < alpha < 1 and c = 1 - alpha:
    ||F_chi||^2_{D+_alpha}                                         (Majorana: discrete series of SL(2,R), holomorphic side)
  = int_0^oo |M_chi(t)|^2 t^{1-2alpha} dt                             (Laplace side, Majorana-Plyushchay realisation)
  = int_0^oo |M_chi(x)|^2 x^{2c} dx/x                                (Masullo: Hardy-Sobolev seminorm on the line Re z = c)
  = (1/2pi) int |Gamma(c + i t) / L(1 - 2c - 2it, chi)|^2 dt          (Ramanujan's Master Theorem + Mellin-Plancherel)

Combined statement (a theorem, proof in the write-up; it is a reformulation of GRH, not a proof of it):
  GRH for chi  <=>  F_chi lies in D+_alpha for every alpha in (3/4, 1)  <=>  the four quantities above are finite for
  every c in (0, 1/4); and if the zeros are simple, the norm blows up at the critical line exactly like
      lim_{alpha -> 3/4+} (alpha - 3/4) ||F_chi||^2_{D+_alpha} = B_chi := (1/8) sum_rho |Gamma((1 - rho)/2) / L'(rho, chi)|^2.
An off-line zero with real part beta > 1/2 would make the norm infinite already at alpha = (1 + beta)/2 > 3/4.

Not included, with the reason: Ramanujan's highly composite numbers / Robin (an inequality for sigma(n), zeta only,
no Mellin-line structure), tau and L(Delta, s) (GL2), Majorana's Thomas-Fermi and Norton-Sakuma algebras (no link to
L(s, chi) found in the earlier runs). Numerical convergence of any of these cannot prove RH: the checks below test
the identities to high precision and measure what they can see.

| # | Check | Done when |
|---|-------|-----------|
| 1 | `line-norm` | for zeta and every primitive chi mod 3, 4, 5, 7: (added before the first complete run: also c = -0.6, -0.3, where the identity for M - 1/L(1, chi) is unconditional) x side (power series on [0, X0] + closed-form zero expansion beyond) equals the Mellin side (|Gamma/L|^2 on the line, no zeros used) to 1e-9 relative at c in {0.05, 0.1, 0.15, 0.2}, at two cut points X0 |
| 2 | `majorana-holomorphic` | for zeta and two characters, at alpha in {0.8, 0.9} and three heights v: the horizontal-line integral int |F_chi(u + iv)|^2 du of F computed from the n-sum (no zeros) equals 2pi int |M_chi|^2 e^{-2vt} dt (Paley-Wiener) to 1e-8, with two truncations N of the n-sum |
| 3 | `critical-blowup` | (1/4 - c) x Mellin-side norm at c = 1/4 - h, h = 10 h0 .. 0.01 h0 with h0 = B/||M||^2_{0.2} (amended before the first run: a trial showed the smooth part of the norm dominates until h ~ B, which for zeta is 2e-10, so a fixed 1e-2 .. 1e-5 range never reaches the regime): converges to B_chi with error O(h) (ratio of successive errors in [5, 20] per decade) and the Richardson limit matches B_chi from the zeros to 1e-6 relative, for zeta and every primitive chi mod 3, 4, 5 |
| 4 | `off-line-control` | a model L-function with one zero pair moved to beta = 0.6 (same functional-equation symmetry) makes the Mellin-side norm diverge at c = 0.2 (h x value at c = 0.2 - h -> K: amended after the first run, which showed h x value = K + h x (smooth background), so the test is now that Richardson estimates of K from h = 1e-10, 1e-11, 1e-12 match the predicted (1/8) sum |Gamma((1-rho)/2)/L~'(rho)|^2 over the moved zeros to 1%), while the true L stays finite there; and in the coarse spaces c = 0.05, 0.1, 0.15 the model norm is finite and within 1e-3 of the true norm (added before the first run, for the topological hypothesis; amended from "agree to 1e-8" after a trial: the model multiplies L by a rational factor 1 - delta^2/(w - rho)^2 that shifts the norm by delta^2/gamma^2 ~ 2e-4 everywhere, so the meaningful test is finiteness, not closeness) |
| 5 | `visibility` | for each check above, the height of the zeros it can resolve at double precision is reported (|Gamma(c + i gamma/2)|^2 above 1e-16 of the total), with the statement that higher zeros are invisible |

Iterate: run -> any NOT CONSISTENT -> fix numerics or the test (log why) -> rerun until 5/5 in one pass.
