# Proving Σ μ(n)χ(n)/n = 1/L(1, χ) in Lean

## Done criteria (written before the work)

1. Lean proves, with no `sorry` and only the three standard axioms, for a nontrivial Dirichlet
   character χ: `Tendsto (fun X => Σ_{n ≤ X} μ(n)χ(n)/n) atTop (𝓝 (1/L(1, χ)))`.
2. Lean proves that the partial sums of the conditionally convergent series
   `Σ μ(n)χ(n)/n · e^{-x/n²}` converge to the Lean `M χ x` for every `x ≥ 0`, so the
   definition `M = M̃ + 1/L(1, χ)` is a theorem about the classical series, not a convention.
3. Full `lake build` and CI pass; the audit lists the new theorems as proved; pytest passes.
4. README, docs/TESTS.md and the paper drop the "definition note / convention" caveat and say
   exactly what is now proved.

## Plan

A. Twisted PNT: `Σ_{n ≤ X} χ(n)Λ(n) = o(X)` from Mathlib's
   `vonMangoldt.tendsto_sum_residueClass_div_atTop` and `Σ_a χ(a) = 0`.
B. Landau: `μ log = −μ * Λ`, twisted by χ, gives `Σ_{n ≤ X} μχ(n) log n = −Σ_{d ≤ X} μχ(d) ψ_χ(X/d)
   = o(X log X)`, and `|Σ μχ(n) log(X/n)| ≤ X`, so `Σ_{n ≤ X} μχ(n) = o(X)`.
C. `S(k) = Σ_{m ≤ k} χ(m)/m` satisfies `|L(1, χ) − S(k)| ≤ 2N/k` (Mathlib's Abel summation and
   `L(1) = ∫₁^∞ A(t) t^{-2} dt` from `LGrowth.lean`). The convolution identity
   `Σ_{n ≤ X} μχ(n)/n · S(X/n) = 1`, split at `X/n = K`, with a discrete Abel bound on the short
   blocks `X/(j+1) < n ≤ X/j`, gives `Σ_{n ≤ X} μχ(n)/n → 1/L(1, χ)`.
D. Partial sums of the series for `M_χ` = partial sums of `M̃_χ` + partial sums of
   `Σ μχ(n)/n`, so they converge to `M̃_χ(x) + 1/L(1, χ) = M χ x`.
