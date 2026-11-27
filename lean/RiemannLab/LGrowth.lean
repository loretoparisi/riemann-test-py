import RiemannLab.GRHFromNorm
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Growth of `L(s, χ)` on `Re s > 0`, and its conjugation symmetry

For a nontrivial Dirichlet character `χ` mod `N`:

* the partial sums `Σ_{1 ≤ k ≤ n} χ(k)` are bounded by `N` (`norm_partialSum_le`);
* `L(s, χ) = s ∫₁^∞ A(t) t^{-s-1} dt` with `A(t) = Σ_{k ≤ t} χ(k)`, for every `Re s > 0`
  (`LFunction_eq_mul_integral`, Mathlib's Abel summation for `Re s > 1` and the identity theorem);
* hence `|L(s, χ)| ≤ N |s| / Re s` (`norm_LFunction_le`);
* `L(conj s, χ⁻¹) = conj L(s, χ)` (`LFunction_inv_conj`).
-/

open Complex MeasureTheory Set Filter Topology DirichletCharacter
open scoped LSeries.notation

noncomputable section

namespace RiemannLab

variable {N : ℕ} [NeZero N]

lemma sum_range_char (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ∑ k ∈ Finset.range N, χ ((n + k : ℕ) : ZMod N) = ∑ a : ZMod N, χ a := by
  induction n with
  | zero =>
    simp only [zero_add]
    refine Finset.sum_nbij' (fun k => (k : ZMod N)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_univ _
    · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro a ha; exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
    · intro a _; exact ZMod.natCast_zmod_val a
    · intro a _; rfl
  | succ n ih =>
    rw [← ih]
    have h1 := Finset.sum_range_succ (fun k => χ ((n + k : ℕ) : ZMod N)) N
    have h2 := Finset.sum_range_succ' (fun k => χ ((n + k : ℕ) : ZMod N)) N
    have h3 : χ ((n + N : ℕ) : ZMod N) = χ ((n + 0 : ℕ) : ZMod N) := by
      congr 1; push_cast; simp
    have h4 : ∀ k, ((n + (k + 1) : ℕ) : ZMod N) = ((n + 1 + k : ℕ) : ZMod N) := fun k => by
      congr 1; ring
    simp only [h4] at h2
    rw [h3] at h1
    linear_combination h1 - h2

/-- Partial sums of a nontrivial character are bounded by its modulus. -/
lemma norm_partialSum_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ N := by
  set Q : ℕ → ℂ := fun m => ∑ k ∈ Finset.range m, χ ((1 + k : ℕ) : ZMod N) with hQ
  have hzero : ∑ a : ZMod N, χ a = 0 := MulChar.sum_eq_zero_of_ne_one hχ
  have hstep : ∀ m, Q (m + N) = Q m := fun m => by
    simp only [hQ, Finset.sum_range_add]
    have := sum_range_char χ (1 + m)
    simp only [show ∀ k, 1 + (m + k) = 1 + m + k from fun k => by ring]
    rw [this, hzero, add_zero]
  have hper : ∀ m j, Q (m + N * j) = Q m := fun m j => by
    induction j with
    | zero => simp
    | succ j ih => rw [show m + N * (j + 1) = m + N * j + N by ring, hstep, ih]
  have hsmall : ∀ m, ‖Q m‖ ≤ m := fun m => by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.range m, ‖χ ((1 + k : ℕ) : ZMod N)‖ ≤ ∑ k ∈ Finset.range m, (1:ℝ) :=
          Finset.sum_le_sum fun k _ => DirichletCharacter.norm_le_one χ _
      _ = m := by simp
  have hIcc : ∑ k ∈ Finset.Icc 1 n, χ k = Q n := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [hQ]
  rw [hIcc, ← Nat.mod_add_div n N, hper]
  exact (hsmall _).trans (by exact_mod_cast (Nat.mod_lt n (Nat.pos_of_ne_zero (NeZero.ne N))).le)

/-- `A(t) = Σ_{1 ≤ k ≤ t} χ(k)`. -/
def A (χ : DirichletCharacter ℂ N) (t : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ k

lemma norm_A_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t : ℝ) : ‖A χ t‖ ≤ N :=
  norm_partialSum_le χ hχ _

omit [NeZero N] in
lemma measurable_A (χ : DirichletCharacter ℂ N) : Measurable (A χ) :=
  (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ k)).comp Nat.measurable_floor

/-- `J(s) = s ∫₁^∞ A(t) t^{-s-1} dt`. -/
def J (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := s * mellinOn (Ioi 1) (A χ) (-s)

lemma integrableOn_A (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {j : ℝ} (hj : j < 0) :
    IntegrableOn (fun t : ℝ => t ^ (j - 1) * ‖A χ t‖) (Ioi 1) := by
  have hint : IntegrableOn (fun t : ℝ => (N : ℝ) * t ^ (j - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  refine hint.mono' ?_ ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_)
  · exact (((continuousOn_id.rpow_const fun x hx => Or.inl
      (ne_of_gt (zero_lt_one.trans (show (1:ℝ) < x from hx)))).aestronglyMeasurable
      measurableSet_Ioi).mul (measurable_A χ).norm.aestronglyMeasurable)
  · have ht0 : (0:ℝ) < t := zero_lt_one.trans ht
    have hp : 0 ≤ t ^ (j - 1) := Real.rpow_nonneg ht0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (norm_nonneg _)), mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_A_le χ hχ t) hp

lemma differentiableAt_J (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (J χ) s := by
  have h : DifferentiableAt ℂ (mellinOn (Ioi 1) (A χ)) (-s) := by
    refine mellinOn_differentiableAt measurableSet_Ioi
      (fun t ht => (zero_lt_one.trans ht : (0:ℝ) < t))
      (measurable_A χ).aestronglyMeasurable (v := s.re / 4) (by linarith) ?_
    intro j hj
    simp only [neg_re] at hj
    exact integrableOn_A χ hχ (by linarith [hj.2])
  exact differentiableAt_id.mul (h.comp s differentiableAt_id.neg)

lemma LFunction_eq_J_of_one_lt_re (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) : LFunction χ s = J χ s := by
  rw [LFunction_eq_LSeries χ hs]
  have hO : (fun n ↦ ∑ k ∈ Finset.Icc 1 n, (↗χ) k) =O[atTop] fun n ↦ (n : ℝ) ^ (0:ℝ) := by
    refine Asymptotics.IsBigO.of_bound (N : ℝ) (Eventually.of_forall fun n => ?_)
    simp only [Real.rpow_zero, norm_one, mul_one]
    exact norm_partialSum_le χ hχ n
  rw [LSeries_eq_mul_integral _ le_rfl (by linarith) (LSeriesSummable_of_one_lt_re χ hs) hO, J,
    mellinOn]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [A, smul_eq_mul]
  rw [mul_comm]
  congr 2
  ring

/-- **Abel summation on `Re s > 0`.** `L(s, χ) = s ∫₁^∞ A(t) t^{-s-1} dt`. -/
theorem LFunction_eq_J (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = J χ s := by
  set U : Set ℂ := {s | 0 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (r := 0)).isPreconnected
  have hf : AnalyticOnNhd ℂ (LFunction χ) U :=
    DifferentiableOn.analyticOnNhd (differentiable_LFunction hχ).differentiableOn hUo
  have hg : AnalyticOnNhd ℂ (J χ) U :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_J χ hχ hz).differentiableWithinAt) hUo
  have h2 : (2 : ℂ) ∈ U := by show (0:ℝ) < (2:ℂ).re; norm_num
  have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by show (1:ℝ) < (2:ℂ).re; norm_num)
  have hfg : LFunction χ =ᶠ[𝓝 (2 : ℂ)] J χ :=
    Filter.eventuallyEq_of_mem hV fun z hz => LFunction_eq_J_of_one_lt_re χ hχ hz
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hUc h2 hfg hs

/-- **Growth of `L(s, χ)`.** For `Re s > 0`, `|L(s, χ)| ≤ N |s| / Re s`. -/
theorem norm_LFunction_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖LFunction χ s‖ ≤ N * ‖s‖ / s.re := by
  rw [LFunction_eq_J χ hχ hs, J, mellinOn, norm_mul]
  have hint : IntegrableOn (fun t : ℝ => (N : ℝ) * t ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have hval : ∫ t in Ioi (1:ℝ), (N : ℝ) * t ^ (-s.re - 1) = N / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    simp only [Real.one_rpow]
    rw [show -s.re - 1 + 1 = -s.re by ring, div_neg, neg_div, neg_neg]
    ring
  have hle : ‖∫ t in Ioi (1:ℝ), (t : ℂ) ^ (-s - 1) • A χ t‖ ≤ N / s.re := by
    rw [← hval]
    refine norm_integral_le_of_norm_le hint ((ae_restrict_mem measurableSet_Ioi).mono
      fun t ht => ?_)
    have ht0 : (0:ℝ) < t := zero_lt_one.trans ht
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht0, mul_comm]
    simp only [sub_re, neg_re, one_re]
    exact mul_le_mul_of_nonneg_right (norm_A_le χ hχ t) (Real.rpow_nonneg ht0.le _)
  calc ‖s‖ * ‖∫ t in Ioi (1:ℝ), (t : ℂ) ^ (-s - 1) • A χ t‖ ≤ ‖s‖ * (N / s.re) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = N * ‖s‖ / s.re := by ring

/-! ### Conjugation symmetry -/

omit [NeZero N] in
lemma LSeries_inv_conj (χ : DirichletCharacter ℂ N) (s : ℂ) :
    LSeries ↗χ⁻¹ s = (starRingEnd ℂ) (LSeries ↗χ ((starRingEnd ℂ) s)) := by
  rw [LSeries, LSeries, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def, LSeries.term_def]
  split_ifs with hn
  · simp
  · rw [map_div₀, ← MulChar.star_apply' χ, RCLike.star_def]
    congr 1
    rw [cpow_conj _ _ (by rw [natCast_arg]; exact Real.pi_ne_zero.symm), conj_natCast,
      Complex.conj_conj]

/-- **Conjugation symmetry.** `L(s, χ⁻¹) = conj L(conj s, χ)`. -/
theorem LFunction_inv_conj (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    LFunction χ⁻¹ s = (starRingEnd ℂ) (LFunction χ ((starRingEnd ℂ) s)) := by
  have hχ' : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
  have hf : AnalyticOnNhd ℂ (LFunction χ⁻¹) univ :=
    DifferentiableOn.analyticOnNhd (differentiable_LFunction hχ').differentiableOn isOpen_univ
  have hgd : Differentiable ℂ ((starRingEnd ℂ) ∘ LFunction χ ∘ (starRingEnd ℂ)) := fun z => by
    have h := ((differentiable_LFunction hχ) ((starRingEnd ℂ) z)).conj_conj
    rwa [Complex.conj_conj] at h
  have hg : AnalyticOnNhd ℂ ((starRingEnd ℂ) ∘ LFunction χ ∘ (starRingEnd ℂ)) univ :=
    DifferentiableOn.analyticOnNhd hgd.differentiableOn isOpen_univ
  have hV : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const continuous_re).mem_nhds (by show (1:ℝ) < (2:ℂ).re; norm_num)
  have hfg : LFunction χ⁻¹ =ᶠ[𝓝 (2 : ℂ)] ((starRingEnd ℂ) ∘ LFunction χ ∘ (starRingEnd ℂ)) := by
    refine Filter.eventuallyEq_of_mem hV fun z hz => ?_
    have hz' : 1 < ((starRingEnd ℂ) z).re := by rwa [conj_re]
    simp only [Function.comp_apply]
    rw [LFunction_eq_LSeries _ hz, LFunction_eq_LSeries _ hz', LSeries_inv_conj]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_univ (mem_univ _) hfg
    (mem_univ s)

end RiemannLab
