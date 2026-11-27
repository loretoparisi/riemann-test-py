# Step 4: the blow-up limit, given the zero expansion

## Goal

Prove in Lean, with only the standard axioms, the blow-up at the critical exponent
`(α − 3/4)·‖M_χ‖²_α → B_χ = (1/8) Σ_ρ |Γ((1−ρ)/2) / L′(ρ, χ)|²` as `α ↓ 3/4`.
This version takes the expansion of M_χ over the zeros as an explicit named hypothesis.
It does not prove that expansion.

## The named hypothesis `ZeroExpansion χ`

There is a function r such that both of these hold:

1. For every x > 1, M_χ(x) = Σ_ρ c_ρ x^{−(1−ρ)/2} + r(x), where c_ρ = −Γ((1−ρ)/2) / (2 L′(ρ, χ)) and ρ runs over the
   nontrivial zeros.
2. ∫₁^∞ |r(x)|² x^{−1/2} dx < ∞.

This is what the classical explicit formula gives when the zeros are simple and the sum converges absolutely. The
term for ρ is the residue of Γ(s)/L(1 − 2s, χ) at s = (1 − ρ)/2. The remainder collects the trivial zeros, which
contribute O(x^{−1/2}). Proving the hypothesis needs a contour shift to the right past all the zeros, together with
growth bounds for 1/L on a sequence of horizontal lines that avoid the zeros. That part stays open.

## Done criteria

1. `blowup_limit_of_expansion` is proved, with only propext, Classical.choice and Quot.sound. Its hypotheses are:
   - χ ≠ 1;
   - `GRH χ`;
   - `ZeroExpansion χ`;
   - Σ_ρ |Γ((1−ρ)/2)/L′(ρ)| < ∞.

   Its conclusion is the same as the conclusion of `blowup_limit`.
2. The original `blowup_limit` stays listed as open (`sorry`), because it does not assume `ZeroExpansion`. The
   audit and the docs say exactly this.
3. The core mean-value lemma is proved for any countable family with distinct frequencies:
   (α − 3/4) ∫₁^∞ |Σ c_i x^{s_i}|² x^{1−2α} dx → ½ Σ|c_i|² when Re s_i = −1/4.
4. The build, CI, the audit, `python -m riemann_lab lean` and pytest all pass.
5. The README, TESTS.md and the paper state the assumption plainly.
