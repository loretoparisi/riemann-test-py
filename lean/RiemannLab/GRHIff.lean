import RiemannLab.GRHToNorm

/-!
# GRH for `χ` is equivalent to finite weighted norms of `M_χ`

Both directions are proved with no `sorry`:

* `finiteNorms_of_GRH` (`GRHToNorm.lean`): GRH ⇒ `∫₀^∞ |M_χ|² x^{1-2α} dx < ∞` for `α ∈ (3/4, 1)`.
* `grh_of_finiteNorms'` (below): the converse. `LFunction_ne_zero_of_finiteNorms` excludes zeros
  with `1/2 < Re ρ < 1`; a zero with `0 < Re ρ < 1/2` would give, by the functional equation, a
  zero of `L(·, χ⁻¹)` at `1 - ρ`, hence by `L(s, χ⁻¹) = conj L(conj s, χ)` a zero of `L(·, χ)` at
  `conj (1 - ρ)`, whose real part lies in `(1/2, 1)`.

The statement is exactly the one formerly left open in `Open.lean`. Both sides of the
equivalence remain open mathematics; this file proves only that they are equivalent.
-/

open Complex MeasureTheory Set DirichletCharacter

noncomputable section

namespace RiemannLab

variable {N : ℕ} [NeZero N]

/-- **Finite norms ⇒ GRH**, from the norms of `χ` alone. -/
theorem grh_of_finiteNorms' (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hfin : FiniteNorms χ) : GRH χ := by
  intro ρ h0 h1 hρ
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hΛ := completedLFunction_eq_zero χ h0 hρ
    have hfe := hprim.completedLFunction_one_sub (1 - ρ)
    rw [sub_sub_cancel, hΛ] at hfe
    have hN : ((N : ℂ) ^ (1 - ρ - 1 / 2)) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]
      exact fun h => (Nat.cast_ne_zero.mpr (NeZero.ne N)) h.1
    have hΛ' : completedLFunction χ⁻¹ (1 - ρ) = 0 := by
      rcases mul_eq_zero.mp hfe.symm with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hN
        · exact absurd h' (rootNumber_ne_zero hprim)
      · exact h
    have hre1 : 1 / 2 < (1 - ρ).re := by rw [sub_re, one_re]; linarith
    have hre2 : (1 - ρ).re < 1 := by rw [sub_re, one_re]; linarith
    have hL' : LFunction χ⁻¹ (1 - ρ) = 0 := by
      have hne0 : (1 - ρ) ≠ 0 := by
        intro h
        rw [h, zero_re] at hre1
        norm_num at hre1
      rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - ρ) (Or.inl hne0), hΛ', zero_div]
    rw [LFunction_inv_conj χ hχ, map_eq_zero] at hL'
    exact LFunction_ne_zero_of_finiteNorms χ hχ hfin (by rwa [conj_re])
      (by rwa [conj_re]) hL'
  · exact LFunction_ne_zero_of_finiteNorms χ hχ hfin hgt h1 hρ

/-- **GRH-equivalent half of the combined equation.** For a primitive nontrivial `χ`, GRH holds
iff the weighted norm of `M_χ` is finite for every `α ∈ (3/4, 1)`. -/
theorem grh_iff_finite_norm (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) :
    GRH χ ↔ ∀ α ∈ Ioo (3 / 4 : ℝ) 1,
      IntegrableOn (fun x : ℝ => ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α)) (Ioi 0) :=
  ⟨fun h => finiteNorms_of_GRH χ hχ h, fun h => grh_of_finiteNorms' χ hprim hχ h⟩

end RiemannLab
