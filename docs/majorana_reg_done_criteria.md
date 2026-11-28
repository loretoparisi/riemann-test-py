# Majorana regularisation of the combined norm: done criteria (written before building)

## The question

Can the Majorana tower / Hilbert-Polya operator be added to the combined norm
N(alpha) = int_0^oo |M_chi(x)|^2 x^(1-2alpha) dx as a regularisation term that stabilises its convergence for
alpha in (3/4, 1)? A term that breaks the GRH equivalence is rejected (Lean:
GRH(chi) <=> N(alpha) < oo for all alpha in (3/4, 1), `grh_iff_finite_norm`).

The analysis, stated before testing. Any regularisation R_eps with R_eps(alpha) < oo for every chi at a fixed
eps > 0 cannot be equivalent to GRH: it is finite whether or not GRH holds, so it cannot detect an off-line
zero. If R_eps increases to N as eps -> 0, then GRH <=> sup_eps R_eps(alpha) < oo for all alpha, which is the
original criterion, with the same difficulty (a bound uniform in eps). So a regularisation can stabilise the
numbers but it cannot make the criterion easier. The two regularisations tested:

* R1, tower cut-off (x side): N_n(alpha) = sum_{m < n} |c_m|^2, c_m the coefficients of M_chi in the orthonormal
  Majorana basis psi_m(t) ~ t^(2alpha-1) e^(-t) L_m^(2alpha-1)(2t) of L^2(t^(1-2alpha) dt) (level m lives on t < ~4m).
  Lean companion: `truncNorm_integrable` (a fixed cut-off is finite for every chi) and `grh_iff_truncNorm_bounded`.
* R2, Tikhonov on the Majorana boost (Mellin side, critical line): N_eps = <v0| (|L(1/2 - 2i K1)|^2 + eps)^-1 |v0>
  = (1/2pi) int |Gamma(1/4 + iE)|^2 / (|L(1/2 - 2iE)|^2 + eps) dE in D+_{1/4}.

Model with an off-line zero: zeta with its first zero pair replaced by beta + i gamma1, beta = 0.8 (and the
mirror 0.2), added on the x side as D(x) = sum_j d_j (1 - e^(-x)) x^(-s_j) (s_j = (1 - rho_j)/2, d_j the residue
coefficients of the moved and removed zeros; the factor 1 - e^(-x) keeps the model in the space near 0).
Its norm is infinite for alpha < (1 + beta)/2 = 0.9.

Numerical evidence, not proof. A check is CONSISTENT only if every item holds.

| # | Check | Done when |
|---|-------|-----------|
| 1 | `tower-coefficients` | c_m from the FFT of the generating function (1 - r)^(-2alpha) int M e^(-t(1+r)/(1-r)) dt on a circle (Laplace transform from the n-sum, `combined.Holo`) at two FFT sizes 2^15 and 2^16 agree to 1e-9 (relative to max abs(c_m)) for m < 4096; for the model terms the FFT coefficients equal an exact binomial convolution to 1e-9; for zeta sum_{m < 4096} abs(c_m)^2 equals the line norm (`combined.line_norm_mellin` at c = 1 - alpha) to 1e-6 at alpha in {0.8, 0.9} |
| 2 | `tower-cutoff-true` | chi4 and chi3_1 at alpha in {0.8, 0.9}: N_n is nondecreasing; the gap N - N_n at n = 256, 1024, 4096 decays with fitted exponent (last two points) within 0.05 of 2(1 - alpha), the rate set by M_chi(0) = 1/L(1, chi) != 0 (a constant near x = 0 in a basis that vanishes there like x^(2alpha-1)); zeta (M(0) = 0) converges much faster (gap below 1e-6 relative at n = 4096). So the cut-off converges slowest exactly where the criterion lives (alpha -> 3/4 for the zeros, alpha -> 1 for the constant) and does not stabilise anything |
| 3 | `tower-cutoff-offline` | chi4 with its first zero pair moved to beta = 0.8 (model norm infinite for alpha < 0.9): at every n <= 4096 the model's N_n differs from the true one by less than 1e-4 relative at alpha = 0.8, so no fixed cut-off can tell them apart; the off-line part sum_{m<n} abs(c_D,m)^2 computed to n = 2^17 oscillates log-periodically (period ~ 3 doublings, from x^(i gamma/2)); its growth exponent averaged over 3 doublings at alpha = 0.8 exceeds that at alpha = 0.95 by 0.3 +- 0.1 (prediction (beta + 1 - 1.6) - (beta + 1 - 1.9) = 0.3) in the last two windows |
| 4 | `tikhonov-critical` | zeta and chi4 at k = 1/4: N_eps finite for eps = 1e-4 ... 1e-10 (decades); sqrt(eps) N_eps -> S = sum_rho |Gamma((1-rho)/2)|^2 / (4 |L'(rho)|) over the zeros with |gamma| < 40, Richardson in sqrt(eps) within 1% of S; model zeta with its first pair moved to beta = 0.6: the limit equals S without the moved pair within 1%, i.e. the regularised critical norm sees only the zeros on the line, and at fixed eps the model value is finite |
| 5 | `verdict` | prints the table: for each regularisation, finite at fixed parameter for the true L and for the model (yes / yes expected), equivalent to GRH at fixed parameter (no), equivalent in the limit (yes, = `grh_iff_finite_norm`), and whether it speeds convergence (measured gap rates from 2 and the eps^-1/2 law from 4) |

Iterate: run -> any NOT CONSISTENT -> fix numerics or the test (log why) -> rerun until 5/5 in one pass.

## Amendments

1. Before the first run, after trials: rows 1-3 rewritten. For zeta the model terms carry |d|^2 ~ 1e-10 and are invisible,
   so the model uses chi4 (first zero at gamma = 6.02, |d| ~ 6e-3). For chi4 the true N_n converges like n^(-2(1-alpha))
   (0.05 relative gap at n = 4096, alpha = 0.8; 39% at alpha = 0.95), not like the zero-driven n^(-(2alpha-3/2)) first
   predicted, because M_chi(0) = 1/L(1) != 0; the original "gap below 1e-3" is replaced by the rate test. The off-line
   growth law n^(beta + 1 - 2alpha) is not visible at n <= 2^17 (log-periodic oscillation, slow approach), so the test is
   the difference of window-averaged exponents between two alphas.
