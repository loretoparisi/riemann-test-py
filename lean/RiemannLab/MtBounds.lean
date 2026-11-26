import RiemannLab.CombinedNorm

/-!
# Pointwise bounds and Mellin convergence for `M̃_χ`

`combined_norm_identity` in `CombinedNorm.lean` took Mellin–Plancherel as the named hypothesis
`MellinPlancherel`. `Plancherel.lean` proves Mellin–Plancherel for any `f` with `x^{c-1} f` and
`x^{2c-1} |f|²` integrable on `(0, ∞)`. Here we check those two integrability conditions for
`M̃_χ` when `-1 < c < 0`, from the pointwise bound `|M̃_χ(x)| ≤ Z(θ) x^θ` (`0 < θ ≤ 1`), where
`Z(θ) = Σ n^{-1-2θ}`, and conclude `combined_norm_identity_unconditional`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped LSeries.notation

noncomputable section

namespace RiemannLab

variable {N : ℕ}

/-- `|e^{-t} - 1| ≤ t^θ` for `t ≥ 0`, `0 ≤ θ ≤ 1`. -/
lemma norm_g_le_rpow {t θ : ℝ} (ht : 0 ≤ t) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : ‖g t‖ ≤ t ^ θ := by
  rcases le_or_gt t 1 with h | h
  · rcases eq_or_lt_of_le ht with h0 | h0
    · have hg0 : g t = 0 := by rw [← h0]; simp [g]
      rw [hg0, norm_zero]
      exact Real.rpow_nonneg ht _
    · calc ‖g t‖ ≤ t := norm_g_le_self ht
        _ = t ^ (1 : ℝ) := (Real.rpow_one t).symm
        _ ≤ t ^ θ := Real.rpow_le_rpow_of_exponent_ge h0 h hθ1
  · calc ‖g t‖ ≤ 1 := norm_g_le_one ht
      _ ≤ t ^ θ := Real.one_le_rpow h.le hθ0

/-- `Z(θ) = Σ_n n^{-1-2θ}`. -/
def Z (θ : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-1 - 2 * θ)

lemma summable_Z {θ : ℝ} (hθ : 0 < θ) : Summable fun n : ℕ => (n : ℝ) ^ (-1 - 2 * θ) :=
  Real.summable_nat_rpow.mpr (by linarith)

/-- One term: `|μχ(n)/n · g(x/n²)| ≤ x^θ n^{-1-2θ}`. -/
lemma norm_term_le (χ : DirichletCharacter ℂ N) (n : ℕ) {x θ : ℝ} (hx : 0 < x) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) : ‖coef χ n * g (b n * x)‖ ≤ x ^ θ * (n : ℝ) ^ (-1 - 2 * θ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coef]
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg le_rfl _)
  have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hb := b_pos hn
  have hbn : b n ^ θ = (n : ℝ) ^ (-2 * θ) := by
    rw [b, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hn0.le,
      Real.rpow_neg hn0.le]
    norm_num
  rw [norm_mul]
  calc ‖coef χ n‖ * ‖g (b n * x)‖ ≤ (n : ℝ)⁻¹ * (b n * x) ^ θ :=
        mul_le_mul (norm_coef_le χ n) (norm_g_le_rpow (by positivity) hθ0.le hθ1)
          (norm_nonneg _) (by positivity)
    _ = x ^ θ * (n : ℝ) ^ (-1 - 2 * θ) := by
        rw [Real.mul_rpow hb.le hx.le, hbn, ← Real.rpow_neg_one, mul_comm (_ ^ (-2 * θ)),
          ← mul_assoc, ← Real.rpow_add hn0, mul_comm]
        ring_nf

lemma summable_term (χ : DirichletCharacter ℂ N) {x θ : ℝ} (hx : 0 < x) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) : Summable fun n => ‖coef χ n * g (b n * x)‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_term_le χ n hx hθ0 hθ1)
    ((summable_Z hθ0).mul_left _)

/-- **Pointwise bound.** `|M̃_χ(x)| ≤ Z(θ) x^θ` for `x > 0`, `0 < θ ≤ 1`. -/
lemma norm_Mt_le (χ : DirichletCharacter ℂ N) {x θ : ℝ} (hx : 0 < x) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) : ‖Mt χ x‖ ≤ Z θ * x ^ θ := by
  calc ‖Mt χ x‖ ≤ ∑' n, ‖coef χ n * g (b n * x)‖ :=
        norm_tsum_le_tsum_norm (summable_term χ hx hθ0 hθ1)
    _ ≤ ∑' n, x ^ θ * (n : ℝ) ^ (-1 - 2 * θ) :=
        Summable.tsum_le_tsum (fun n => norm_term_le χ n hx hθ0 hθ1)
          (summable_term χ hx hθ0 hθ1) ((summable_Z hθ0).mul_left _)
    _ = Z θ * x ^ θ := by rw [tsum_mul_left, Z, mul_comm]

lemma Z_nonneg (θ : ℝ) : 0 ≤ Z θ := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- `M̃_χ` is continuous on `(0, ∞)` (uniform convergence on `(0, R)`). -/
lemma continuousOn_Mt (χ : DirichletCharacter ℂ N) : ContinuousOn (Mt χ) (Ioi 0) := by
  have hloc : ∀ R : ℝ, ContinuousOn (Mt χ) (Ioo 0 R) := by
    intro R
    unfold Mt
    refine continuousOn_tsum (u := fun n => |R| * (n : ℝ) ^ (-1 - 2 * (1:ℝ))) ?_
      ((summable_Z one_pos).mul_left _) ?_
    · intro n
      exact (continuous_const.mul (continuous_g.comp (continuous_const.mul continuous_id))).continuousOn
    · intro n x hx
      have h := norm_term_le χ n hx.1 one_pos le_rfl
      rw [Real.rpow_one] at h
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      exact hx.2.le.trans (le_abs_self R)
  intro x hx
  exact ((hloc (x + 1)).continuousAt (Ioo_mem_nhds hx (by linarith))).continuousWithinAt

/-- Integrability on `(0, ∞)` from power bounds near `0` and near `∞`. -/
lemma integrableOn_Ioi_of_bounds {F : ℝ → ℝ} (hF : ContinuousOn F (Ioi 0)) {a b C D : ℝ}
    (ha : -1 < a) (hb : b < -1) (h0 : ∀ t ∈ Ioc (0:ℝ) 1, ‖F t‖ ≤ C * t ^ a)
    (h1 : ∀ t ∈ Ioi (1:ℝ), ‖F t‖ ≤ D * t ^ b) : IntegrableOn F (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · have hint : IntegrableOn (fun t : ℝ => C * t ^ a) (Ioc 0 1) :=
      Integrable.const_mul ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' ha)) C
    exact hint.mono' ((hF.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall h0))
  · have hint : IntegrableOn (fun t : ℝ => D * t ^ b) (Ioi 1) :=
      Integrable.const_mul (integrableOn_Ioi_rpow_of_lt hb zero_lt_one) D
    exact hint.mono' ((hF.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall h1))

lemma rpow_mul_bound {t c θ Zc : ℝ} (ht : 0 < t) (hZ : 0 ≤ Zc) {m : ℝ} (hm : m ≤ Zc * t ^ θ) :
    t ^ (c - 1) * m ≤ Zc * t ^ (c - 1 + θ) := by
  calc t ^ (c - 1) * m ≤ t ^ (c - 1) * (Zc * t ^ θ) :=
        mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg ht.le _)
    _ = Zc * t ^ (c - 1 + θ) := by rw [Real.rpow_add ht]; ring

/-- `x^{c-1} M̃_χ` is integrable on `(0, ∞)` for `-1 < c < 0`. -/
lemma mellinConvergent_Mt (χ : DirichletCharacter ℂ N) {c : ℝ} (h1 : -1 < c) (h0 : c < 0) :
    MellinConvergent (Mt χ) (c : ℂ) := by
  unfold MellinConvergent
  rw [mellin_convergent_iff_norm le_rfl measurableSet_Ioi
    ((continuousOn_Mt χ).aestronglyMeasurable measurableSet_Ioi)]
  simp only [ofReal_re]
  have hc : ContinuousOn (fun t : ℝ => t ^ (c - 1) * ‖Mt χ t‖) (Ioi 0) :=
    (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)).mul (continuousOn_Mt χ).norm
  refine integrableOn_Ioi_of_bounds hc (a := c - 1 + 1) (b := c - 1 + (-c / 2))
    (C := Z 1) (D := Z (-c / 2)) (by linarith) (by linarith) ?_ ?_
  · intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (norm_nonneg _))]
    exact rpow_mul_bound ht.1 (Z_nonneg _) (norm_Mt_le χ ht.1 one_pos le_rfl)
  · intro t ht
    have ht0 : (0:ℝ) < t := zero_lt_one.trans ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (norm_nonneg _))]
    exact rpow_mul_bound ht0 (Z_nonneg _) (norm_Mt_le χ ht0 (by linarith) (by linarith))

/-- `x^{2c-1} |M̃_χ|²` is integrable on `(0, ∞)` for `-1 < c < 0`. -/
lemma mellinConvergent_Mt_sq (χ : DirichletCharacter ℂ N) {c : ℝ} (h1 : -1 < c) (h0 : c < 0) :
    MellinConvergent (fun x => ((‖Mt χ x‖ ^ 2 : ℝ) : ℂ)) ((2 * c : ℝ) : ℂ) := by
  have hcont : ContinuousOn (fun x => ((‖Mt χ x‖ ^ 2 : ℝ) : ℂ)) (Ioi 0) :=
    continuous_ofReal.comp_continuousOn ((continuousOn_Mt χ).norm.pow 2)
  unfold MellinConvergent
  rw [mellin_convergent_iff_norm le_rfl measurableSet_Ioi
    (hcont.aestronglyMeasurable measurableSet_Ioi)]
  simp only [ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_norm]
  have hc : ContinuousOn (fun t : ℝ => t ^ (2 * c - 1) * ‖Mt χ t‖ ^ 2) (Ioi 0) :=
    (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)).mul
      ((continuousOn_Mt χ).norm.pow 2)
  have hsq : ∀ {t θ : ℝ}, 0 < t → 0 < θ → θ ≤ 1 → ‖Mt χ t‖ ^ 2 ≤ Z θ ^ 2 * t ^ (2 * θ) := by
    intro t θ ht hθ0 hθ1
    calc ‖Mt χ t‖ ^ 2 ≤ (Z θ * t ^ θ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_Mt_le χ ht hθ0 hθ1) 2
      _ = Z θ ^ 2 * t ^ (2 * θ) := by
          rw [mul_pow, ← Real.rpow_natCast (t ^ θ), ← Real.rpow_mul ht.le]
          ring_nf
  refine integrableOn_Ioi_of_bounds hc (a := 2 * c - 1 + 2 * 1) (b := 2 * c - 1 + 2 * (-c / 2))
    (C := Z 1 ^ 2) (D := Z (-c / 2) ^ 2) (by linarith) (by linarith) ?_ ?_
  · intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (sq_nonneg _))]
    exact rpow_mul_bound (c := 2 * c) ht.1 (sq_nonneg _) (hsq ht.1 one_pos le_rfl)
  · intro t ht
    have ht0 : (0:ℝ) < t := zero_lt_one.trans ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (sq_nonneg _))]
    exact rpow_mul_bound (c := 2 * c) ht0 (sq_nonneg _) (hsq ht0 (by linarith) (by linarith))

end RiemannLab
