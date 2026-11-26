# Hardy-Littlewood-Ramanujan reformulation of GRH: done criteria (written before building)

Claim under investigation (from the Ramanujan x Masullo run): with lambda(k) = 1/L(2k+1, chi), RMT gives
Mellin(M_chi)(s) = Gamma(s)/L(1-2s, chi) for M_chi(x) = Sum mu(n) chi(n)/n e^{-x/n^2}; its poles in the strip are
at s = (1 - rho)/2, so GRH for chi <=> M_chi(x) = O(x^{-1/4+eps}); Hardy's RMT hypothesis on Re z > -1/4 holds
exactly when GRH holds; a trace-formula proof could aim at this growth bound.

Literature found before building: the equivalence is a published theorem (Hardy-Littlewood, Acta Math. 41
(1918) for zeta; Garg-Maji, arXiv 2208.07596, Thm 2.2, for primitive chi and general k, l). The character
analogue of Ramanujan's alpha beta = pi identity is Dixit, Pacific J. Math. 255 (2012), Thms 1.9-1.10.
So nothing below can be new mathematics; the checks test the precise statements and measure what numerics
can and cannot see. Evidence, not proof.

| # | Check | Done when |
|---|-------|-----------|
| 1 | `mellin-strip` | the unconditional identity Int_0^oo x^(s-1) (M_chi(x) - 1/L(1,chi)) dx = Gamma(s)/L(1-2s,chi) on -1 < Re s < 0 holds to 1e-10 at 4 points for zeta and two characters, with the integral computed from the power series (x <= X0) and the Moebius sum beyond, at two cut points X0 (amended: the integral uses the closed-form Mellin transform of the zero expansion beyond X0 instead of the Moebius sum, which is checked against it in #3) |
| 2 | `hardy-hypothesis-edge` | phi(z) = 1/(Gamma(z+1) L(2z+1,chi)) sampled on Re z = -delta, |Im z| <= 40: max |phi| grows at least like (1/4 - delta)^(-1) as delta -> 1/4 (so the hypothesis holds on each closed half-plane Re z >= -delta, delta < 1/4, not uniformly on the open one); Hardy's A estimated <= pi/2 + 0.05 |
| 3 | `moebius-large-x` | for zeta and every primitive chi mod 3, 4, 5, 7, 8, 11, 13: the Moebius sum to N = 10^7 with tails of order J = 2 agrees with the zero expansion to 1e-8 x^(-1/4) (error budget = rigorous Taylor tail + float estimate) for 10^2 <= x <= 10^11; and with the power series to 1e-10 x^(-1/4) at x <= 100 |
| 4 | `reciprocity` | the character analogue of alpha beta = pi (alpha beta = pi/q; even chi: M_chi, odd chi: sqrt(x) Sum mu chi/n^2 e^{-x/n^2}; root number and the trivial-zero term at s = 1/2 for even chi), derived independently by contour shift, holds to 1e-12 for every primitive chi mod 3, 4, 5, 7, 8, 11, 13 at alpha in {0.7, 1, 1.6}, at two zero heights T |
| 5 | `amplitude` | A_chi = Sum_rho |Gamma((1-rho)/2)/(2 L'(rho))| converges (T = 50 vs 80 agree to 1e-12 A); the first zero pair carries > 90% of A (amended after the first full run: true for zeta and q <= 8 but 84-89% for six characters mod 11 and 13, whose zeros are denser; the criterion is now that zeros with |gamma| <= 20 carry > 99% of A, which is the statement the visibility argument needs); sup of x^(1/4)|M - trivial| over log x in [0, 10^5] is <= A and >= 0.9 A (Kronecker-type: sup approaches A) |
| 6 | `sensitivity` | an injected off-line pair (beta = 1/2 +- 0.2) at height gamma is detected by the Moebius-vs-zero-expansion comparison at x <= 10^11 when gamma <= 25 and is invisible (effect < error budget) when gamma >= 60; the predicted detection height from |Gamma((1-rho)/2)| x^(delta/2)/2 > eta matches the measured one within 15%; table of log10 x needed to see an off-line zero at the verified height 3e12 |

Iterate: run -> any NOT CONSISTENT -> fix numerics or the test (log why) -> rerun until all six pass in one pass. Then PR.
