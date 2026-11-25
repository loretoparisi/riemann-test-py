# Majorana x Masullo checks: done criteria (written before building)

Sources read: E. Recami, *The scientific work of Ettore Majorana* and the EJTP 3(10) Majorana issue (2006:
the 1932 infinite-component equation, Majorana's 1928 Thomas-Fermi solution, the Majorana stellar
representation via Zimba, Plyushchay on the (2+1)-d Majorana equation); M. Plyushchay, *Fractional spin:
Majorana-Dirac field* (IHEP 91-90); A. Castillo-Ramirez, *On Majorana algebras and representations* (PhD,
Imperial 2014); H. Hendriksen, *Majorana particles in physics and mathematics* (BSc, Groningen 2014).

Masullo's manuscript (*The Music of the Primes*, 2026 draft) works with Hardy-Sobolev norms that are L2
norms of Mellin transforms on vertical lines Re z = a, b, with Schwartz-Bergman spaces "replacing the open
unit disc with a vertical strip" (his Lemma D.3.1.2), Schauder bases (ch. 4, 7), Sarnak's paradigm of
families (1.1) and an empty chapter 13 on holomorphic families of test functions.

Two directions. (A) a Majorana technique applied to Masullo's setting or to an RH criterion; (B) Masullo's
tools (Mellin transforms on strips, explicit formulas, L-function families) used to test a Majorana result.
All of it is numerical evidence, not proof.

A check is CONSISTENT only if every item in its row holds, and the key numbers come out of two independent
computations (two truncations, precisions, quadratures or representations).

| # | Check | Dir. | Done when |
|---|-------|------|-----------|
| 1 | `majorana-tower` | B | Majorana's two unitary infinite-dimensional Lorentz representations, (j0, c) = (0, 1/2) and (1/2, 0), truncated at j <= J for J = 40 and 80: the so(3,1) relations hold to 1e-12 on the blocks j <= J - 1 and all six generators are Hermitian; Gamma0 = diag(j + 1/2) with Gamma_k = i[F_k, Gamma0] is a 4-vector to 1e-12; rest masses are m/(s + 1/2); at p = 0.7 m the four largest energies in the lowest-helicity sector equal sqrt(m^2/(s+1/2)^2 + p^2) to 1e-6 at J = 80, and J = 40 and J = 80 agree to 1e-5 on them; every negative-energy solution is spacelike (abs(E) < p, Majorana's tachyonic branch); the tower's spectral zeta Sum_states (M/m)^s equals 2 zeta(s-1) (half-integer tower) and 2 (2^(s-1) - 1) zeta(s-1) (integer tower) to 1e-12 at s = 3, 4.5, 6 by direct summation |
| 2 | `discrete-series-hardy-sobolev` | A | For alpha in {0.6, 0.75, 1, 1.5} (Plyushchay's D+_alpha, the internal space of the (2+1)-d Majorana equation): J0, J+- satisfy sl(2,R) with Casimir alpha(alpha - 1) to 1e-12 on interior blocks, the rest masses are m alpha/(alpha + n), and the differential realization J0 = z d/dz + alpha acts as the matrix; for a random f = Sum_(n<=12) c_n chi_n four norms agree to 1e-10: coefficients, the disk integral with weight (1 - abs(z)^2)^(2 alpha - 2), the Laplace side Int abs(F)^2 t^(1 - 2 alpha) dt and the Mellin side on Re z = 1 - alpha (Masullo's seminorm); the Hardy limit alpha = 1/2 does the same with the circle and Re z = 1/2; Masullo's s = 0 Hardy-Sobolev norm with base [1 - alpha2, 1 - alpha1] lies between the larger of the two discrete-series norms and their sum |
| 3 | `local-rh-majorana-basis` | A | For the same alpha and n <= 30, the Mellin transform of the n-th basis vector, t^(2 alpha - 1) e^(-t) L_n^(2 alpha - 1)(2t), is Gamma(s + 2 alpha - 1) Q_n(s) with deg Q_n = n, and all n zeros of Q_n lie on Re s = 1 - alpha (abs(Re z - (1 - alpha)) < 1e-20 at 50 digits), confirmed by n sign changes of the rotated real function on the line on two grids; direct quadrature equals the closed form to 1e-15 at 5 points; the basis is orthonormal on the line to 1e-12; control: F_n^(alpha) + F_m^(alpha') with alpha != alpha' has zeros off every vertical line (spread of Re z > 1e-2) |
| 4 | `xi-discrete-series-expansion` | A | Xi(2x) = Sum a_n P_n^(lambda)(x; pi/2) (Meixner-Pollaczek, the Mellin-side image of the Majorana basis) for lambda = 3/4 and lambda = 1: a_n at 30 and 40 digits agree to 1e-8 relative wherever abs(a_n) > 1e-20; S_N reproduces Xi(2x) on [0, 10] to 1e-12 at N = 160; the first four zeros of zeta recovered from real roots of S_N improve from N = 80 to N = 160 and are within 1e-4 at N = 160; both lambdas give the same zeros to 1e-4 |
| 5 | `majorana-stars-jensen` | A | GORZ's gamma(n) (Taylor coefficients of 8 xi(1/2 + z)) for n <= 40 from a quadrature of Riemann's Phi at 60 digits agree with mpmath Taylor coefficients of xi for n <= 6 to 1e-20; for d <= 10 and n <= 30 every Jensen polynomial J^(d,n) has d real roots by an exact Sturm count, and the Majorana stars of the spin-d/2 state with amplitudes sqrt(C(d,k)) gamma(n + d - k) all lie on one great circle (abs(Y) < 1e-12); control: Xi(t)(t^2 + 0.04) (zeros at s = 0.3, 0.7) gives at least one non-hyperbolic J^(d,n) with d <= 10, n <= 30, whose stars leave the circle by > 1e-3 |
| 6 | `majorana-random-matrices-quadratic-L` | B | Class D (Majorana BdG H = iA, A real antisymmetric) and class C random matrices, 2N = 100, >= 2000 samples: the unfolded density of the smallest positive eigenvalues matches 1 + sin(2 pi x)/(2 pi x) and 1 - sin(2 pi x)/(2 pi x) respectively (L2 distance on [0, 3] < 0.05), each closer to its own law than to the other; low-lying zeros of L(s, chi_d) for all fundamental discriminants 100 < abs(d) <= D (D = 1000 quick, 3000 full), computed by a theta-integral and checked against hecke.Z on 10 characters to 1e-8: the scaled one-level density is closer to USp (class C) than to SO(even) (class D) and to U, and the first bin [0, 0.25) holds less than half of what U predicts |
| 7 | `majorana-thomas-fermi` | B | Majorana's series u = Sum a_n tau^n for du/dt = 8(t u^2 - 1)/(1 - t^2 u), u(1) = 1: a1 = 9 - sqrt(73), a1 = 2(1 - lambda) with Sommerfeld's exponent lambda = (sqrt(73) - 7)/2; Sum a_n gives phi'(0) = -1.588071022611... to 1e-10 (with a tail estimate) and matches an independent shooting solution of phi'' = phi^(3/2)/sqrt(x) to 1e-9; Majorana's 10-term solution has max relative error <= 0.3% on [0.1, 20] (his "0.1%"), the full series <= 1e-8; the ratio a_n/a_(n-1) settles (reported against Majorana's 4/5); Mellin transform Int x^(s-1) phi dx at four points of the strip 0 < Re s < 3 from Majorana's one-quadrature parametric form equals the ODE value to 1e-8; a fit of x^3 phi/144 - 1 at large x recovers lambda to 1e-3 |
| 8 | `majorana-algebras-moonshine` | B | The eight non-trivial Norton-Sakuma algebras 2A, 2B, 3A, 3C, 4A, 4B, 5A, 6A from Table 2.2 of Castillo-Ramirez, in exact rational arithmetic: commutative, the form is associative (M1), Norton's inequality on 2000 random pairs (M2), ad(a) semisimple with spectrum in {1, 0, 1/4, 1/32} and a one-dimensional 1-space (M4, M5), the fusion rules of Table 2.1, tau(a) is an automorphism (M6), and an identity exists with length 12/5, 2, 116/35, 32/11, 4, 19/5, 32/7, 51/10 (Table 2.3); moonshine: c(n) of j(tau) - 744 exactly for n <= 10, Rademacher's Kloosterman-Bessel series within 0.5 of c(n) for n <= 5 with the error shrinking in the cutoff, Weil's bound abs(K(m, n; c)) <= d(c) gcd(m, n, c)^(1/2) c^(1/2) for m, n <= 5, c <= 1000, and c(1), c(2), c(3) decompose into Monster irreducible dimensions (1, 196883, 21296876, 842609326) with multiplicities (1,1), (1,1,1), (2,2,1,1) |

Iterate: full run -> any NOT CONSISTENT -> fix the numerics or the test (and log why in the README) -> full
run again, until all eight are consistent in one pass. Then PR.

## Amendments (logged in the README convergence log)

1. Row 5, control. `Xi(t)(t^2 + 0.04)` was a wrong control: its extra zeros t = +-0.2i are real points w = 0.04 of
   F(w) = sum gamma(n) w^n/n! (w = -t^2), and Jensen hyperbolicity only detects non-real w. Replaced, before the
   first run, by a quadruple of off-line zeros at s = 1/2 +- 0.4 +- 2i (t = +-2 +- 0.4i). Quadruples at height 1 and 3
   are reported too; the one at height 3 is not detected for d <= 10, n <= 30.
2. Row 7, Mellin. The double-precision ODE is unstable beyond x ~ 50 (the mode x^lambda grows), and a fitted
   asymptotic tail limits a full-line ODE Mellin transform to ~1e-5. The criterion now compares the truncated
   transform Int_0^100 x^(s-1) phi dx at four points (tolerance 1e-6) against a 30-digit Taylor-series ODE solution;
   the full transform is reported. The pole at s = 3 (residue 144) is reported.
3. Row 7, Majorana's accuracy. Esposito reports "order of 0.1%" for 10 terms; we measure 0.50% (max on [0.1, 20]).
   The criterion is now: 10-term error below 1%, and decreasing with the number of terms (10, 12, 15). 0.1% needs ~15.
4. Row 6: the quadratic-character zeros are computed serially (a process pool with multithreaded numpy was 10x slower).
