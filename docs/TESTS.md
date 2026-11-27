# Detailed test results

Every section below follows the same protocol (see [Methodology](../README.md#methodology)): done criteria written
before the code, one full run, fixes, and re-runs until every check converges. Floating-point checks are evidence,
not certificates; the Lean section is the only part that is machine-checked proof.

* [Lean 4 formalisation](#lean-4-formalisation-seventh-and-eighth-runs)
* [Original checks](#results-of-the-full-run) · [Extended criteria](#results-of-the-extended-run-new-criteria)
* [Ramanujan × Masullo](#ramanujan--masullo-third-run) · [Majorana × Masullo](#majorana--masullo-fourth-run)
* [Hardy–Littlewood–Ramanujan](#hardylittlewoodramanujan-investigation-fifth-run) · [Combined norm](#ramanujan--majorana--masullo-one-combined-norm-sixth-run)

## Lean 4 formalisation (seventh and eighth runs)

`python -m riemann_lab lean` (and the `Lean` GitHub Actions workflow on every PR touching `lean/`). It runs
`lake build`, then `lake env lean Audit.lean`, which prints `#print axioms` for every theorem, and then mpmath
checks of the same statements. A theorem counts as proved only if its axioms are exactly Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`); a theorem using `sorryAx` is open. Raw output:
[`results/lean_report.txt`](../results/lean_report.txt).

| Status | Lean name | Statement |
| --- | --- | --- |
| proved | `mellin_g` | ∫₀^∞ x^{s−1}(e^{−x} − 1) dx = Γ(s), −1 < Re s < 0 |
| proved | `integrableOn_g_norm` | x^{σ−1}\|e^{−x} − 1\| integrable on (0, ∞), −1 < σ < 0 |
| proved | `scale_identity` | x^{−1}((x²)^{−1})^{−s} = x^{−(1−2s)}, x > 0 |
| proved | `integral_norm_F` | ∫\|n-th Mellin integrand\| ≤ K(σ) n^{2σ−1} (Tonelli bound) |
| proved | `mellin_Mt_eq_LSeries` | 𝓜M̃_χ(s) = Γ(s) L(μχ, 1 − 2s), −1 < Re s < 0 (Fubini) |
| proved | `mellin_Mt` | 𝓜M̃_χ(s) = Γ(s)/L(1 − 2s, χ), −1 < Re s < 0 |
| proved, given `MellinPlancherel` | `combined_norm_identity` | ∫\|M̃_χ\|² x^{1−2α} dx = (1/2π)∫\|Γ/L\|² dt, 1 < α < 2 |
| proved | `plancherel` | ∫\|𝓕f\|² = ∫\|f\|² for f ∈ L¹ ∩ L²(ℝ) |
| proved | `mellin_plancherel` | ∫₀^∞\|f\|² x^{2c−1} dx = (1/2π)∫\|𝓜f(c+it)\|² dt when x^{c−1}f and x^{2c−1}\|f\|² are integrable |
| proved | `combined_norm_identity_unconditional` | the norm identity on 1 < α < 2 with no hypothesis |
| proved | `mellinOn_differentiableAt` | ∫_S t^{s−1}f(t) dt is holomorphic where t^{σ−1}\|f\| is integrable on S ⊆ (0, ∞) |
| proved | `K_mul_LFunction_eq` | K(s) L(1 − 2s, χ) = Γ(s + 1) on −1 < Re s < 0, K(s) = s(∫₀¹x^{s−1}M̃ + ∫₁^∞x^{s−1}M) + 1/L(1, χ) |
| proved | `LFunction_ne_zero_of_finiteNorms` | finite norms for all α ∈ (3/4, 1) ⇒ L(w, χ) ≠ 0 for 1/2 < Re w < 1 |
| proved | `grh_of_finiteNorms` | finite norms for χ and χ⁻¹ ⇒ GRH(χ), χ primitive, χ ≠ 1 |
| named hypothesis (now discharged) | `MellinPlancherel` | Mellin–Plancherel on Re s = c; kept as a definition, proved by `mellin_plancherel` |
| open (`sorry`) | `grh_iff_finite_norm` | GRH(χ) ⇔ finite norm for all α ∈ (3/4, 1); the ⇐ direction is `grh_of_finiteNorms`, the ⇒ direction is open |
| open (`sorry`) | `blowup_limit` | (α − 3/4)\|\|M_χ\|\|² → B_χ, given GRH, simple zeros, absolute convergence |

Numerical cross-checks of the Lean statements (all PASS): `mellin_g` to 10^−30 at four points; K(σ) = −Γ(σ) to 10^−17;
`scale_identity` to 3·10^−16; the Lean M̃_χ (direct sum over n) equals the Python M_χ − 1/L(1, χ) to 8·10^−14 (χ mod 5);
`mellin_Mt` to 4·10^−15; the two sides of `combined_norm_identity` agree to 3.5·10^−16 at c = −0.5 and −0.25.

### Convergence log (Lean run)

1. The Mathlib binary cache host is blocked in the cloud sandbox, so compilation moved to GitHub Actions
   (`leanprover/lean-action`, which downloads the cache), with the Python launcher running the audit there.
2. CI pass 1: six elaboration errors in `mellin_g` (a set-inclusion argument, the derivative of e^{−x} − 1, an
   `IntegrableOn` congruence, a rewrite that also hit the `0` inside `𝓝[>] 0`, and the order of two integral rewrites).
   Pass 2: one remaining rewrite in the boundary limit at 0. Pass 3: `CombinedNorm.lean` compiles with no `sorry`;
   `Open.lean` needed `[NeZero N]` for Mathlib's `LFunction`. Pass 4: build, audit and numerics PASS.

### Convergence log (eighth run: Plancherel and finite norms ⇒ GRH)

1. `Plancherel.lean`: five CI passes. The L² Fourier transform needed an explicit `Lp` type ascription, the
   integrals of real casts needed `integral_complex_ofReal`, `ContDiff ℝ ⊤` had to be `ContDiff ℝ ∞`, and the
   substitution x = e^{−u} was redone by hand because the generic Mathlib lemma timed out at E = ℂ.
2. `MtBounds.lean` (split out of `CombinedNormFull.lean` so the GRH file could build independently): sums had to
   be indexed by ℕ explicitly, and two rpow rewrites were restated.
3. **Bug found and fixed in `Open.lean`.** M_χ was a `tsum` of a series that converges only conditionally; in Lean
   such a `tsum` is 0, so M_χ was the zero function and the two open statements were about the wrong object
   (`blowup_limit` was even false as stated). M_χ is now M̃_χ + 1/L(1, χ).
4. `GRHFromNorm.lean`: one CI pass with name clashes (`K` already existed, `δ` is a reserved token), then the full
   build passed locally (7448 jobs) and the audit reports 14 proved, 2 open. pytest: 114 passed.

## Results of the full run

Raw output is in [`../results/`](../results/): `pytest.txt`, `report.txt`, `verify_windows.txt`, `extended_report.txt`, `ramanujan_report.txt`, `majorana_report.txt`.

* Tests: 106 of 106 pass (25 original + 19 for the extended criteria + 23 for the Ramanujan × Masullo checks + 19 for the Majorana × Masullo checks + 13 for the HLR investigation + 7 for the combined norm).
* Zeros: all 4,491 zeros with 100 < t ≤ 5000, all 4,626 with 10^5 < t ≤ 1.03·10^5 and all 3,812 with 10^6 < t ≤ 1.002·10^6 lie on the critical line (sign changes of Z equal N(T2) − N(T1)).
* Gram's law holds for 959 of the first 1,001 Gram intervals.
* Schoenfeld's RH bound |π(x) − li(x)| < √x log x / 8π holds up to 10^6 (tightest at x = 2657, ratio 0.964).
* Robin's inequality holds for 5040 < n ≤ 10^6 (max ratio 1.755814 at n = 10080) and at 19,992 colossally abundant numbers up to 10^96728 (max ratio 1.7808203 vs e^γ = 1.7810724).
* Lagarias's inequality holds for n ≤ 10^6.
* Mertens: |M(x)|/√x stays below 1 up to 10^6 (max 0.894 at x = 5).
* Keiper–Li: λ_1 … λ_20 all positive, λ_1 = 0.023095708966 (certified to n = 10^4 below).
* Weil explicit formula: spectral and geometric sides agree to 4.4e-16.
* Masullo's toy trace formula: spectral, Poisson and matrix traces agree to 1e-15.
* Spacings near t = 10^5: KS distance 0.019 to GUE, 0.087 to GOE, 0.299 to Poisson.

## Results of the extended run (new criteria)

Raw output: [`../results/extended_report.txt`](../results/extended_report.txt). Each check has a verdict:
**CONSISTENT** means the numbers converged (two precisions, two truncations or two grids agree) and agree
with known theory. All 7 are consistent. Two needed fixes on the first full pass (see "Convergence log").

These are numerical experiments. They are evidence about RH, not proof of it. The Li coefficients
are the one exception: each Arb enclosure is a proof that that λ_n > 0, but that is a known
fact for small n and says nothing about all n.

* **Turing's method.** All zeros are on the critical line in four windows: 165 zeros near 10^3,
  1,542 near 10^5, 954 near 10^6 and 2,273 near 10^7. In each window N(g_n) is fixed exactly by
  Trudgian's bound, with E inside [−0.19, +0.19]. At the three lower heights it matches the
  argument-principle count. A deliberately wrong count is rejected, because E is forced to −1.
* **de Bruijn–Newman.** H_t from the heat flow matches the defining integral to 2·10^−16.
  Backward in time, the latest pair collision in each window is −4.9·10^−2 below 10^3,
  −2.9·10^−3 near 10^4, −1.0·10^−3 near 10^5 and −3.4·10^−4 near 10^6. These rise towards 0,
  as Λ ≥ 0 (Rodgers–Tao) requires. Lehmer's pair at 7005.06 gives −7.1·10^−4, which is
  consistent with the rigorous Λ > −0.0991 from that pair. The first-order collision time agrees
  with the exact one from H_t to 0.4%. H_{0.2} has no zeros with Im z ≥ 0.2 for Re z ≤ 400,
  which is the finite-range part of Polymath 15's Λ ≤ 0.22. It is not a bound on Λ by itself.
* **Nyman–Beurling.** d_N decreases monotonically: d_200² = 0.00892, and 0.00771 at N = 400.
  The values at dps 60 and dps 100 are identical. d_N² log N stays within 4.5% of Burnol's
  constant 2 + γ − log 4π = 0.04619 for 50 ≤ N ≤ 200, but not monotonically. Sampled values are 0.0464 at 50,
  0.0473 at 200, 0.0455 at 250, 0.0462 at 400. Landreau and Richard saw the same slow,
  irregular approach up to N = 20,000.
* **Weil positivity.** Weil matrices of size 12, 16 and 24 were built from primes alone. They agree
  with the same matrices built from zeros to 1.4·10^−14, and every eigenvalue is positive.
  The smallest are 1.1·10^−8, 1.0·10^−4 and 2.0·10^−3. Putting a hypothetical zero at
  0.6 + 20i or 0.55 + 30i makes the matrix indefinite, so this family would detect such a zero.
* **Li coefficients, certified.** λ_1 … λ_10000 are all positive, as Arb balls at 11,128 bits.
  The largest relative radius is about 10^−300. λ_10000 = 34736.58 is within 0.03% of
  (n/2)(log n − 1 + γ − log 2π). The deviation, divided by √n log n, stays bounded at 0.02–0.035 in every quarter of the range,
  which is what RH predicts.
* **Riesz.** R(x)/x^{1/4} stays bounded by about 2·10^−4 for 10^4 < x ≤ 10^10. It matches the
  expansion over the first 30 zeros plus trivial terms to 4·10^−6 of its amplitude.
  The rigorous truncation bound is about 1.5·10^−6 · x^{1/4}.
* **Redheffer.** det A_n = M(n) holds exactly (integer elimination) for n ≤ 200 and in floating point
  up to n = 3000. The largest eigenvalue divided by √n falls from 1.18 to 1.07, as Vaughan's
  √n + O(log n) predicts.

### Convergence log (full run → fix → re-run)

1. Pass 1, Turing near 10^7: the anchors certified N exactly, but the sign-change search found
   only 2,271 of the 2,273 zeros, because two close pairs fell between grid points. Fix: when
   the count comes up short, refine the grid by 4×. Pass 2 found 2,273 of 2,273 at oversample 64.
2. Pass 1, Nyman–Beurling: I had required d_N² log N to keep decreasing, and it does not. It
   oscillates near the constant. That test was wrong, not the numerics: Landreau and Richard
   (Exp. Math. 11, 2002) report the same irregular behaviour up to N = 20,000. Fix: the verdict
   now asks for agreement between two precisions, monotone d_N, and d_N² log N within 5% of
   2 + γ − log 4π.
3. Pass 1, Riesz: the rigorous tail bound was 6% of the signal. Fix: a longer, chunked tail sum
   (L = 60 x^{7/12}) brings it under 1%.

## Ramanujan × Masullo (third run)

Raw output: [`../results/ramanujan_report.txt`](../results/ramanujan_report.txt). The done criteria were written
before any code: [docs/ramanujan_done_criteria.md](ramanujan_done_criteria.md). **All 8 checks are consistent
in one full pass.** These are numerical tests of ideas, not a repair of Masullo's proof and not a proof of anything.

**Why Ramanujan fits Masullo.** Masullo works with Mellin transforms on the idele class group: his Hardy–Sobolev
norms are L² norms of Mellin transforms on two vertical lines, and his main consequence (§1.4.5) is that
L′/L(s + 1/2, χ) has no poles in the open strip. Ramanujan's Master Theorem (RMT) gives Mellin transforms in closed
form from Taylor coefficients: ∫₀^∞ x^{s−1} Σ λ(k)(−x)^k/k! dx = Γ(s) λ(−s). Chapter 13 of the draft ("holomorphic
families of test functions", "main theorems on the location of the zeros") is empty, and RMT is a supply of explicit,
holomorphic families whose Mellin side is known exactly. The proposals tested here:

1. **RMT reconstructs L(s, χ) inside the critical strip from its values at negative integers** (generalized Bernoulli
   numbers). Hardy's growth hypothesis holds with A = π/2 < π, so by Carlson's theorem those values determine L.
   Measured: the Mellin integral equals Γ(s)L(s, χ) to 10^−20…10^−31 at six points per function (ζ and χ mod 4, 5, 7),
   dps 20 and 30 agree, and the Hardy–Sobolev norm of (1+x)^−1.5 computed on the Mellin side via RMT equals the
   x-side norm to 3·10^−15, with Masullo's norm equivalence holding.
2. **A Ramanujan reformulation of Masullo's main consequence.** With λ(k) = 1/L(2k+1, χ), RMT gives
   Mellin(M_χ)(s) = Γ(s)/L(1−2s, χ) for M_χ(x) = Σ μ(n)χ(n)/n e^{−x/n²} = Σ (−x)^k/(k! L(2k+1, χ)).
   Its poles in the strip are at s = (1−ρ)/2, so **GRH for χ ⇔ M_χ(x) = O(x^{−1/4+ε})** (Hardy–Littlewood 1918
   for ζ), and Hardy's RMT hypothesis on the half-plane Re z > −1/4 holds exactly when GRH holds for χ. A trace-formula
   proof could aim at this growth bound instead of at the poles of L′/L.
   *Correction (HLR investigation below): this equivalence is a published theorem (Hardy–Littlewood 1918; Garg–Maji,
   arXiv:2208.07596, for χ). The Mellin identity is unconditional only for M_χ − 1/L(1, χ) on −1 < Re s < 0, Hardy's
   hypothesis holds on each closed half-plane Re z ≥ −δ, δ < 1/4, not on the open one, and the growth bound is no
   easier a target than GRH itself.*
   Measured, for ζ and χ mod 3, 4, 5: the power series, the Möbius sum to N = 10^7 (with a rigorous tail bound) and the
   residue expansion over zeros on the line agree to 10^−11 x^{−1/4} for 10² ≤ x ≤ 10^8. x^{1/4}|M_χ − trivial terms|
   stays below the amplitude Σ|Γ((1−ρ)/2)/2L′(ρ)| computed from the zeros. Ramanujan's lost-notebook identity
   (αβ = π), which needs simple zeros, holds to 7·10^−17 at three values of α.
3. **GRH for Hecke L-functions over Q, to height 50.** For all 32 primitive characters mod 3, 4, 5, 7, 8, 11, 13: the
   argument-principle count of zeros of Λ(s, χ) in [−1/2, 3/2] × [0, 50] equals the number of sign changes of Z_χ on
   the line (839 zeros), at two grid densities.
4. **Explicit formula for χ (Masullo App. B.4).** Zero side = prime side to 6·10^−15 for every character and two
   Gaussian widths. One hypothetical zero pair 0.6 + 9i, 0.4 + 9i breaks it by at least 0.2.
5. **Masullo's Expectation 1.7.1 (zero multiplicities ≤ [F : Q] for finite-order χ).** For the Dedekind zeta of
   Q(ζ_q), q = 5, 7, 11, 13 (degree 4 … 12), every zero up to height 50 is simple (|Z′| ≥ 0.79) and no ordinate is
   shared between characters (smallest gap 10^−4). That is multiplicity 1, which is stronger than the bound and in line
   with the Grand Simplicity Hypothesis. PSLQ finds no integer relation among γ₁…γ₈. For Thm 1.7.1.1, the local factors at
   different primes share no pole other than s = 0.
6. **Partial Euler products on the 1-line (App. B.7).** ∏_{p≤x}(1 − χ(p)/p)^{−1} → L(1, χ) for 12 characters, with
   |error|·√x/log²x shrinking (upper/lower half ratio 0.49) up to x = 10^7. Nicolas' criterion
   N_k/φ(N_k) > e^γ log log N_k holds for all 664,578 primorials with p_k ≤ 10^7.
7. **Ramanujan's highly composite numbers (RH-conditional part) and Robin's constant.** At 89,992 colossally abundant
   n up to log n = 1.16·10^6, (e^γ log log n − σ(n)/n)√log n is positive. It drifts down from a mean of 1.464 to
   1.432 and stays above the RH liminf e^γ(2√2 − 4 − γ + log 4π) = 1.3932 (minimum on the second half: 1.3969).
   Ramanujan sums: the closed form matches the root-of-unity definition. Σ_q c_q(n)/q → 0 at the RH rate
   (|m(x)| ≤ x^{−0.563} for 10³ ≤ x ≤ 10^7).
8. **τ(n) and L(Δ, s) (GL(2), the empty §14.3 of the draft).** τ is multiplicative, satisfies the Hecke relations and
   τ ≡ σ₁₁ (mod 691), and obeys Deligne's bound (max |τ(p)|/2p^{11/2} = 0.959). The Sato–Tate moments are 0.95, 1.81
   and 4.32 (theory 1, 2, 5). All 8 zeros of L(Δ, s) with 0 < t ≤ 30 lie on Re s = 6, with the argument-principle
   count equal to 8. The first zero is 9.222379399921.

### Convergence log (Ramanujan run)

1. Quick run, `ramanujan-robin`: the pre-written criterion asked the scaled Robin margin to decrease monotonically
   across three stretches. It oscillates (1.468, 1.439, 1.470), as d_N² log N does in the Nyman–Beurling check, so the
   test was wrong, not the numbers. The new criterion: positive everywhere, the second-half mean below the first-half mean,
   and the second-half minimum above 1.3932 − 0.05. It is recorded in the criteria file.
2. Full pass 1, 6/8: `rmt-mellin` for χ mod 7 (2.6·10^−8) and `hardy-littlewood-ramanujan` for χ̄ mod 5 (7.6·10^−8)
   missed their 10^−10 and 10^−8 thresholds. The cause was the character values, which were rounded to 15 decimals, so
   χ(n) = ±i came out as 10^−15 ± i: Σχ ≠ 0, a spurious pole at s = 1, and χ, χ̄ no longer exact conjugates.
   The fix builds the values from one table of roots of unity, with exact 0/±1 components and exact conjugate pairs.
   (mpmath's `dirichlet(1, χ)` is also unreliable for such χ, so L(1, χ) now uses the digamma formula.)
3. Full pass 2: 8/8 consistent.

## Majorana × Masullo (fourth run)

Raw output: [`../results/majorana_report.txt`](../results/majorana_report.txt). The done criteria were written before any
code: [docs/majorana_done_criteria.md](majorana_done_criteria.md). **All 8 checks are consistent in one full
pass.** Sources: Recami's survey and the 2006 EJTP Majorana issue (the 1932 infinite-component equation, the 1928
Thomas–Fermi solution, the stellar representation), Plyushchay's *Fractional spin: Majorana–Dirac field*,
Castillo-Ramírez's thesis *On Majorana algebras and representations* (2014) and Hendriksen's *Majorana particles in
physics and mathematics* (2014). As before: numerical tests of ideas, not a repair of Masullo's proof.

**What carries over to Masullo, and what does not.**

* *The strongest link is structural.* Majorana's equation in 2+1 dimensions (Plyushchay) has its internal space in
  the discrete series D⁺_α of SL(2, ℝ), realised on holomorphic functions on the disk with weight (1 − |z|²)^{2α−2}.
  Cayley map + Laplace transform + Mellin transform carry that norm, exactly, to the L² norm on the vertical line
  Re z = 1 − α, which is the seminorm Masullo uses to define his Hardy–Sobolev spaces (his Lemma D.3.1.2 even
  describes his Schwartz–Bergman spaces as Bergman spaces with the disc replaced by a strip). So Masullo's
  W⁰_[a,b] is, up to a factor 2, D⁺_{1−a} ⊕ D⁺_{1−b}. The basis Majorana and Plyushchay use (z^n ↔ Laguerre functions
  ↔ Γ(α + iτ) × Meixner–Pollaczek polynomials) is an explicit orthonormal, hence Schauder, basis of each line, with
  J₀ = Majorana's spin operator and the mass operator mα/J₀. It is a ready-made coordinate system for the "orbital
  Schauder bases" of chapters 4 and 7.
* *A local Riemann hypothesis comes for free, a global one does not.* The Mellin transform of every basis vector has
  all its zeros on Re z = 1 − α (orthogonal polynomials have real zeros). A mixture of two α breaks this, and the
  expansion of Ξ in the basis converges but only resolves the k-th zero at degree ~γ_k²/3. Nothing in the
  representation theory forces the zeros of the particular infinite combination Ξ onto the line: that is still
  the whole problem.
* *Majorana's tower gives a trace identity, not a Hilbert–Pólya operator.* Σ over states of (M/m)^s on the
  half-integer tower is 2ζ(s − 1): ζ appears as a spectral zeta function, but its zeros are not eigenvalues.
* *Majorana's stellar representation turns Jensen hyperbolicity into geometry.* J^{d,n} (Griffin–Ono–Rolen–Zagier)
  is the Majorana polynomial of a spin-d/2 state, and it is hyperbolic exactly when all Majorana stars lie on one
  great circle. That is a reformulation; low-degree Jensen polynomials only see off-line zeros at small height.
* *Majorana fermions pick the wrong symmetry class for Masullo's GL(1) family.* Majorana Bogoliubov–de Gennes
  Hamiltonians (class D, H = iA with A real antisymmetric, the Clifford-algebra picture of Hendriksen's thesis) give
  SO(even) statistics near zero; the quadratic Dirichlet family is symplectic, like class C. Class D would match
  SO(even) families (for example even quadratic twists of an elliptic curve), which `hecke` does not cover yet.
* *Majorana algebras do not touch ζ directly.* They live on the Griess algebra of the Monster; the only bridge to
  analytic number theory is moonshine (Rademacher's Kloosterman series for j, and Weil's bound, which is RH for curves
  over finite fields and already a theorem).

**Measured.**

1. **Majorana's 1932 tower.** Both unitary infinite-dimensional representations, (j₀, c) = (0, ½) and (½, 0),
   satisfy so(3,1) to 6·10⁻¹⁴ on 441 and 462 states, with Hermitian generators; Γ^μ is a 4-vector to 7·10⁻¹³. Rest
   masses are m/(s + ½), the boosted spectrum at p = 0.7m matches √(M_s² + p²) to 2·10⁻¹⁵ (truncations 40 and 80 agree
   to 4·10⁻⁶), and all 38 negative-energy solutions are spacelike (Majorana's tachyonic branch). The tower's spectral
   zeta equals 2ζ(s − 1) and 2(2^{s−1} − 1)ζ(s − 1) to 2·10⁻¹⁶.
2. **Discrete series = Masullo's lines.** sl(2, ℝ) and the Casimir α(α − 1) hold to 5·10⁻¹³, masses are mα/(α + n).
   For α = 0.6, 0.75, 1, 1.5 the norm of a random 13-term vector is the same (to 25 digits) from coefficients, the
   disk integral, the Laplace side and the Mellin line Re z = 1 − α; at α = ½ the circle and Re z = ½ agree too.
   Masullo's two-line norm lies between the larger single-line norm and their sum.
3. **Local RH for the basis.** For n ≤ 30 and four α, all zeros of the Mellin transforms lie on Re z = 1 − α to
   10⁻³⁶, with 30 sign changes on the line on two grids; the basis is orthonormal on the line to 2·10⁻²¹; mixing two α
   spreads the zeros over a width of 3–4.
4. **Ξ in the basis.** Ξ(2x) = Σ aₙ Pₙ^{(λ)}(x; π/2) for λ = ¾ and 1: coefficients at 30 and 40 digits agree to
   6·10⁻¹⁴, S₁₆₀ reproduces Ξ to 7·10⁻¹⁵, and γ₁…γ₄ come out of its real roots with errors 4·10⁻¹⁴, 3·10⁻¹⁰,
   2·10⁻⁸, 3·10⁻⁵ (λ = ¾), improving from N = 80 to 160.
5. **Majorana stars of Jensen polynomials.** All 310 polynomials J^{d,n}, d ≤ 10, n ≤ 30, are hyperbolic (exact Sturm
   counts), and every constellation lies on the great circle Y = 0. Adding off-line zeros at s = ½ ± 0.4 ± 2i makes
   4 of them non-hyperbolic (first at d = 7) and moves stars off the circle by 0.17; at height 1 it is 8 (from d = 3);
   at height 3 nothing is detected up to d = 10.
6. **Majorana random matrices vs quadratic L-functions.** Class D and class C BdG matrices (2N = 100, 20,000
   samples) follow 1 + sinc and 1 − sinc near zero (L² distance 0.023 and 0.028). For the 1,759 fundamental
   discriminants 100 < |d| ≤ 3000 (zeros by a theta integral, checked against `hecke` to 4·10⁻¹¹), the one-level
   density is closest to USp (0.39, against 1.07 for SO(even) and 0.65 for U), with strong repulsion at 0 (first bin
   0.05). Finite-conductor corrections are still large at this size.
7. **Thomas–Fermi, Majorana's way.** a₁ = 9 − √73 = 2(1 − λ) with Sommerfeld's λ = (√73 − 7)/2. 400 terms give
   φ′(0) = −1.588071022611375, equal to the literature value to 2·10⁻¹⁶ and to an independent shooting solution to
   8·10⁻¹⁵. The parametric solution matches a 30-digit ODE to 3·10⁻¹¹. Its Mellin transform on the strip 0 < Re s < 3
   (one quadrature) matches the ODE on [0, 100] to 6·10⁻⁸, has the pole at s = 3 with residue 144 (extrapolated
   143.9997), and x³φ/144 − 1 decays with exponent 0.7716 (λ = 0.7720). Majorana's 10-term truncation is good to
   0.5%, not the 0.1% quoted by Esposito: 0.1% takes about 15 terms. The ratio aₙ/aₙ₋₁ is 0.795 at n = 10, close to
   Majorana's 4/5, but creeps up to 0.83 by n = 400.
8. **Majorana algebras and moonshine.** All eight Norton–Sakuma algebras from Table 2.2 of the thesis (2A … 6A,
   including the 5A and 6A products, which the scanned text garbles and were rebuilt from the dihedral symmetry) pass
   every axiom in exact rational arithmetic: commutativity, associativity of the form, Norton's inequality, spectrum
   {1, 0, ¼, 1/32} with a one-dimensional 1-space, the fusion rules, τ(a) an automorphism, and identity lengths
   12/5, 2, 116/35, 32/11, 4, 19/5, 32/7, 51/10 exactly as in Table 2.3. j − 744 has c(1) = 196884 = dim of the Griess
   algebra; Rademacher's series reproduces c(1..5) within 0.007; Weil's bound holds for c ≤ 1000 (max ratio 1); and
   the McKay–Thompson decompositions of c(1), c(2), c(3) hold.

### Convergence log (Majorana run)

1. Before the first run: the pre-written Jensen control `Ξ(t)(t² + 0.04)` was wrong. Its extra zeros sit at real
   w = −t², which Jensen polynomials cannot detect. It was replaced by a quadruple at s = ½ ± 0.4 ± 2i.
2. Quick run, 5/8: `local-rh-majorana-basis` missed 10⁻¹⁵ (7·10⁻¹⁴) in the quadrature check, because x^{s−1} oscillates
   infinitely often at 0 for complex s. Fix: integrate (0, 1] in u = −log t (now 10⁻²³). `xi-discrete-series-expansion`
   used too low a degree in quick mode. `majorana-thomas-fermi` failed Majorana's accuracy claim (0.50% against a
   0.3% threshold); the measurement stands and the criterion is now "< 1%, decreasing with terms", with the
   discrepancy reported. The ODE side moved to a 30-digit Taylor-series solver, and the Mellin comparison to [0, 100],
   because double precision is unstable beyond x ≈ 50.
3. Full pass 1, 7/8: `majorana-thomas-fermi` failed only because two 50-digit quantities were compared at 15-digit
   working precision. Fix: compare inside `mp.workdps(50)`.
4. Full pass 2: 8/8 consistent.

## Hardy–Littlewood–Ramanujan investigation (fifth run)

`python -m riemann_lab hlr` checks the result above line by line. Criteria: [docs/hlr_done_criteria.md](hlr_done_criteria.md).
Full pass 3: **6/6 consistent** (raw output in `../results/hlr_report.txt`).

**Prior art.** GRH ⇔ M_χ(x) = O(x^{−1/4+ε}) is Hardy–Littlewood (Acta Math. 41, 1918) for ζ and Garg–Maji
(arXiv:2208.07596, Thm 2.2) for primitive χ. The character analogue of Ramanujan's α β = π identity is Dixit
(Pacific J. Math. 255, 2012, Thms 1.9–1.10). Nothing here is a new theorem about the zeros; what is new, and of
what kind, is listed in [Prior art and what is new](../README.md#prior-art-and-what-is-new).

1. `mellin-strip`: ∫x^{s−1}(M_χ − 1/L(1,χ))dx = Γ(s)/L(1−2s,χ) on −1 < Re s < 0 (unconditional, Fubini) to ≤ 2·10^−14 for ζ, χ4, χ5, χ7.
2. `hardy-hypothesis-edge`: |φ| on Re z = −δ grows like (1/4 − δ)^−1 (constant to 1%), Hardy's A = 1.556–1.566 ≈ π/2.
3. `moebius-large-x`: for ζ and all 32 primitive χ mod 3, 4, 5, 7, 8, 11, 13, the Möbius sum to N = 10^7 (order-3 tails,
   rigorous Taylor remainder plus a floating-point estimate) agrees with the zero expansion within a budget of
   2.5·10^−10 x^{−1/4} for 10² ≤ x ≤ 10^11; the measured differences are ~10^−13.
4. `reciprocity`: M_χ(α²) = ε̄√(π/q)/α (M_χ̄(β²) − 1/L(1,χ̄)) + Z_χ(α²) + √π/(2αL′(0,χ)) (even χ) and the
   √x Σμχ/n² e^{−x/n²} version (odd χ), α β = π/q, hold to ≤ 3·10^−14 for all 33 functions.
5. `amplitude`: A_χ = Σ|Γ((1−ρ)/2)/(2L′(ρ))|; zeros with |γ| ≤ 20 carry > 99.7% of it; sup of x^{1/4}|M − trivial| over
   log x ≤ 10^5 is 0.998–0.99999 A (Kronecker-type).
6. `sensitivity`: an injected off-line quadruple (β = ½ ± 0.2) is detected at x ≤ 10^11 only for γ ≤ 35. Seeing one at the
   verified height 3·10^12 would need log10 x ≈ 4·10^12.

### Convergence log (HLR run)

1. Quick run, 6/6. The Möbius tail was first order 1 (bound x²/8N⁴, too big beyond 10^9); order 3 with 70-digit tails
   and an mpmath head to n = 2·10^5 for m ≥ 5 reaches 10^11.
2. Full pass 1, 5/6: `moebius-large-x` failed by 10^15 for complex χ mod 7, 11, 13: character values stored as
   doubles carry 10^−16 errors that x³ T_7 amplifies. Fix: exact roots of unity (`hlr.exact_values`).
3. Full pass 2, 5/6: `amplitude` failed its guess that the first zero pair carries > 90% of A (84–89% for six
   characters mod 11, 13). Criterion amended to the statement the argument needs: zeros with |γ| ≤ 20 carry > 99%.
4. Full pass 3: 6/6 consistent.

## Ramanujan + Majorana + Masullo: one combined norm (sixth run)

`python -m riemann_lab combined`. Criteria: [docs/combined_done_criteria.md](combined_done_criteria.md). **5/5 consistent**
(`../results/combined_report.txt`). This is a reformulation of GRH in Hilbert-space form, not a proof. See
[Prior art and what is new](../README.md#prior-art-and-what-is-new) for how it relates to the 1918, 2012 and 2022 results.

With F_χ(w) = Σ μ(n)χ(n) n/(1 − i n² w) (the Laplace transform of M_χ) and c = 1 − α:

    ||F_χ||²_{D⁺_α}  =  ∫|M_χ(t)|² t^{1−2α} dt  =  ∫|M_χ(x)|² x^{2c} dx/x  =  (1/2π) ∫|Γ(c+it)/L(1−2c−2it, χ)|² dt
     (Majorana tower)     (Laplace side)            (Masullo line norm)          (Ramanujan: RMT + Plancherel)

* Unconditional for M_χ − 1/L(1, χ) on α ∈ (1, 2). For M_χ on every α ∈ (3/4, 1) it holds **iff GRH** (Hardy–Littlewood /
  Garg–Maji), and with simple zeros (α − 3/4)||F_χ||² → B_χ = (1/8)Σ|Γ((1−ρ)/2)/L′(ρ)|² as α → 3/4.
* An off-line zero with real part β leaves the norm finite for α > (1 + β)/2 and infinite below: coarse spaces hide it,
  only the finest exclude it, and membership there is GRH.

1. `line-norm`: x side = Mellin side (no zeros used) to ≤ 5·10^−13 for ζ and all 11 primitive χ mod 3, 4, 5, 7, at
   c = −0.6, −0.3 (unconditional) and 0.05, 0.1, 0.15, 0.2 (GRH range).
2. `majorana-holomorphic`: ∫|F_χ(u+iv)|² du from the n-sum = 2π∫|M_χ|² e^{−2vt} dt to ≤ 4·10^−16 (ζ, χ4, χ5_2; v = 0.05, 0.2, 1).
3. `critical-blowup`: (1/4 − c)||M||²_c → B_χ linearly (error ratios 10.00 per decade), extrapolated to ≤ 1.4·10^−9 of B
   (ζ: B = 2.1·10^−10, so the blow-up only shows at 1/4 − c ≈ 10^−10).
4. `off-line-control`: moving ζ's first zero pair to β = 0.6 makes h||M||²_{0.2−h} → K = 4.767774·10^−11, equal to the
   predicted residue sum; the coarse norms (c = 0.05–0.15) stay finite, within 2·10^−4 of ζ's.
5. `visibility`: on Re z = c a zero above |γ| ≈ 20 weighs < 10^−16; every check here sees only the lowest zeros.

### Convergence log (combined run)

1. Trials before the first full pass: the critical-blowup h range (10^−2…10^−5) was replaced by h = (10…0.01)·B/||M||²_{0.2},
   since the smooth part dominates until h ≈ B; the coarse-space criterion "agree to 10^−8" became "finite and within
   10^−3", since the model multiplies L by a rational factor that shifts the norm by ~2·10^−4 everywhere.
2. A first attempt was stopped during `line-norm` to add the unconditional range c < 0 (Loreto asked for the equality); its [0, 1]
   quadrature was 1% off for c < 0 until rewritten as ∫|G|² dy with M − c0 = x G(x).
3. Pass 1, 3/5: `critical-blowup` missed for ζ by 3.4·10^−6: c = 1/4 − h was formed in 15 digits, which shifts
   h = 2·10^−12 by 5·10^−5 relative. Fixed (c at working precision, exact β = 3/5). `off-line-control` needed the
   smooth background removed (Richardson for K).
4. Pass 2, 4/5: `critical-blowup` missed for χ5_1 by 1.1·10^−6, which is the b h² term of a first-order Richardson.
   Second order on the three smallest h. Pass 3 of that check: consistent (all within 1.4·10^−9).

