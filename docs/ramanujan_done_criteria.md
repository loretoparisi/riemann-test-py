# Ramanujan x Masullo checks: done criteria (written before building)

Masullo's manuscript (The Music of the Primes, 2026 draft) claims GRH for all Hecke L-functions over
number fields. Its chapter 13 ("Holomorphic families of test functions", "Main theorems on the location of
the zeros") is empty in the draft. The checks below take Ramanujan's Master Theorem (RMT), Ramanujan's
notebook/lost-notebook formulas and his work on highly composite numbers and tau, and turn each into a
numerical test aimed at a specific step of Masullo's programme. They are evidence, not proof.

A check is CONSISTENT only if every item in its row holds, and the same numbers come out of two
independent computations (two precisions, two quadratures, two truncations or two representations).

| # | Check | Masullo step it targets | Done when |
|---|-------|------------------------|-----------|
| 1 | `rmt-mellin` | Mellin transforms on R>0 (ch. 3, 9: Hardy-Sobolev norms are L2 norms of Mellin transforms on Re z = a, b) | RMT gives Int x^(s-1) f(x) dx = Gamma(s) lambda(-s) to rel. err < 1e-10 at >= 6 points of the strip for (1+x)^-a, e^-x-type, zeta (lambda(k) = zeta(-k)) and Dirichlet L (lambda(k) = L(-k, chi) from generalized Bernoulli numbers), with two quadrature precisions agreeing; the Hardy-Sobolev norm computed on the Mellin side equals the x-side norm to 1e-8; Hardy's growth exponent A estimated < pi for each lambda used |
| 2 | `hardy-littlewood-ramanujan` | the main consequence (1.4.5): L'/L(s + 1/2, chi) has no poles in the open strip | for zeta and for every primitive chi mod 3, 4, 5: the power series Sum (-x)^k / (k! L(2k+1, chi)) and the Moebius sum Sum mu(n) chi(n)/n e^(-x/n^2) agree (two representations); they match the zero expansion from RMT (residues at s = (1 - rho)/2 plus trivial terms) to 1e-8 of x^(-1/4); x^(1/4) |HL(x)| stays bounded up to the largest x reached (GRH <=> O(x^(-1/4+eps))); Ramanujan's alpha beta = pi identity holds to 1e-12 with simple zeros only |
| 3 | `hecke-zeros` | GRH for Hecke L-functions over Q (Dirichlet characters) | for every primitive chi mod q in {3, 4, 5, 7, 8, 11, 13} up to height T: the argument-principle count of zeros in [-1/2, 3/2] x [0, T] equals the number of sign changes of the Hardy-type Z_chi(t) on the line, at two grid densities |
| 4 | `hecke-explicit-formula` | the explicit formula (App. B.4) | Weil's explicit formula for each chi with a Gaussian test function: sum over the on-line zeros found in #3 equals the prime side to 1e-8, for two widths; adding one hypothetical off-line zero breaks it by > 1e-4 |
| 5 | `zero-multiplicities` | Expectation 1.7.1 (multiplicity <= [F:Q] for finite-order chi; Grand Simplicity) | for the Dedekind zeta of Q(zeta_q), q = 5, 7, 11, 13 (degree q - 1): every zero up to T is simple (|Z'| bounded away from 0 at each sign change) and no ordinate is shared by two characters (min gap > 1e-6); PSLQ finds no integer relation (coefficients <= 10^3) among the first 8 ordinates of zeta |
| 6 | `euler-products-1-line` | App. B.7 (partial Euler products on the 1-line) | Prod_{p <= x} (1 - chi(p)/p)^-1 -> L(1, chi) with |error| * sqrt(x) / log(x)^2 bounded for x up to 10^7 (GRH rate); Nicolas: N_k/phi(N_k) > e^gamma log log N_k for all primorials with p_k <= 10^7 |
| 7 | `ramanujan-robin` | Ramanujan's "Highly composite numbers" (unpublished part, RH-conditional) | at colossally abundant n up to log n ~ 10^6: Robin margin positive, and (e^gamma log log n - sigma(n)/n) sqrt(log n) stays positive and drifts down towards Robin's RH limit e^gamma(2 sqrt2 - 4 - gamma + log 4 pi) = 1.3932; Ramanujan sums: Sum_{q<=Q} c_q(n)/q -> 0 at the RH rate |
| 8 | `ramanujan-tau` | higher rank (Masullo 14.3, empty in the draft): GL2 | tau(n) to 2000 from Delta = q Prod(1 - q^n)^24: multiplicative, Hecke relation, 691 congruence, Deligne bound |tau(p)| <= 2 p^(11/2), Sato-Tate moments within 3/sqrt(#p); zeros of L(Delta, s) up to T all on Re s = 6 (sign-change count equals the argument-principle count), first zero 9.22237... |

Amended after the quick run (logged in the README): row 7 originally asked the scaled Robin margin to
"drift down" monotonically. It oscillates (like d_N^2 log N in the Nyman-Beurling check), so the
criterion is now: positive everywhere, second-half mean below first-half mean, and second-half minimum
above the RH liminf 1.3932 minus 0.05.

Iterate: full run -> any NOT CONSISTENT -> fix the numerics or the test (and log why) -> full run again,
until all eight are consistent in one pass. Then PR.
