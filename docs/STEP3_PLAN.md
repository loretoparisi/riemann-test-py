# Step 3: GRH ⇒ finite norms (closing `grh_iff_finite_norm`)

## Done criteria (written before the work)

1. `grh_iff_finite_norm` in Lean has no `sorry`. `#print axioms` lists only `propext`,
   `Classical.choice`, `Quot.sound`.
2. The full `lake build` passes locally and in CI. `Audit.lean` reports every proved theorem with
   standard axioms only, and `blowup_limit` as the single remaining open statement.
3. `riemann_lab/lean_bridge.py` PROVED/OPEN lists match the audit; `pytest` passes.
4. README, `docs/TESTS.md` and the paper state exactly what Lean checks, with the one standing
   convention spelled out: `M_χ = M̃_χ + 1/L(1, χ)` (the value `Σ μ(n)χ(n)/n = 1/L(1, χ)` is the
   definition of the constant, not a Lean theorem).
5. Nothing claims the unconditional `α ∈ (3/4, 1)` case. The equivalence is "GRH(χ) ⟺ finite
   norms", both sides open.

## Proof plan (χ primitive, χ ≠ 1, `c' = 1 - α ∈ (0, 1/4)`)

A. `LGrowth`: partial sums of χ are bounded by `N`; `L(s, χ) = s ∫₁^∞ A(t) t^{-s-1} dt` on
   `Re s > 0` (Mathlib's Abel summation for `Re s > 1` plus the identity theorem), so
   `|L(s, χ)| ≤ N |s| / Re s`. Also `L(conj s, χ⁻¹) = conj L(s, χ)`.
B. `InvLBound`: under GRH, `L` has a holomorphic logarithm on discs in `Re w > 1/2`
   (Mathlib `HasPrimitives`), and Borel–Carathéodory turns the bound in A into
   `|1/L(w, χ)| ≤ C (1 + |Im w|)^A` on `1/2 + δ ≤ Re w ≤ 3`.
C. `GammaDecay`: `|Γ(s)| ≤ Γ(Re s + k) / |Im s|^k` for `Re s > 0`.
D. `GRHToNorm`: `f = M̃_χ − g / L(1, χ)` has Mellin transform
   `H(s) = Γ(s+1) · dslope (1/L(1-2·, χ)) 0 s`, holomorphic on `-1 < Re s < 1/4` under GRH and
   `O(|Im s|^{-2})` there. Mellin inversion on `Re s = -1/2`, a rectangle contour shift to
   `Re s = c'`, and Plancherel give `x^{c'-1/2} f ∈ L²(0, ∞)`. Since `M_χ = f + e^{-x}/L(1, χ)`,
   the weighted norm of `M_χ` is finite.
E. ⇐ already holds from `grh_of_finiteNorms` given finite norms for χ and χ⁻¹; the conjugation
   symmetry in A removes the need for χ⁻¹, so `grh_iff_finite_norm` closes.
