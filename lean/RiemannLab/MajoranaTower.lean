import RiemannLab.GRHIff

/-!
# Majorana's infinite-component tower, and regularised norms

**Part 1: the tower.** Majorana's infinite-component equation in 2+1 dimensions (Plyushchay's form)
lives in the lowest-weight representation `D⁺_k` of `sl(2, ℝ)`. On the level basis `e_n` (`n ∈ ℕ`):

    J₀ e_n = (k + n) e_n,   J₊ e_n = a_n e_{n+1},   J₋ e_{n+1} = a_n e_n,   a_n = √((n+1)(n+2k)).

We let these act on *all* sequences `ℕ → ℝ` (coefficients in the level basis) and prove the operator
identities `[J₀, J₊] = J₊`, `[J₀, J₋] = -J₋`, `[J₊, J₋] = -2 J₀` and the Casimir
`J₀² - J₀ - J₊J₋ = k(k-1)` for every `k ≥ 0`, and that Majorana's rest masses `m k/(k+n)` are a strictly
decreasing tower.

**Part 2: regularising the combined norm.** Cutting the norm off at `x ≤ T` (what a finite Majorana
tower does: level `n` lives on `x ≲ 4n`) gives a quantity that is finite for *every* character,
with no hypothesis (`truncNorm_integrable`). So no fixed regularisation of this kind can be equivalent
to GRH. The equivalence survives only in the limit, as a uniform bound
(`grh_iff_truncNorm_bounded`): GRH holds iff the truncated norms are bounded in `T` for every
`α ∈ (3/4, 1)`. That is `grh_iff_finite_norm` again; the regularisation adds nothing to it.
-/

open MeasureTheory Set Filter

noncomputable section

namespace RiemannLab

/-! ## Part 1: the tower `D⁺_k` -/

/-- The ladder coefficient `a_n = √((n+1)(n+2k))`. -/
def towerA (k : ℝ) (n : ℕ) : ℝ := Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2 * k))

lemma towerA_sq {k : ℝ} (hk : 0 ≤ k) (n : ℕ) :
    towerA k n ^ 2 = ((n : ℝ) + 1) * ((n : ℝ) + 2 * k) := by
  unfold towerA
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))]

/-- `J₀`: the compact generator (Majorana's mass operator, up to the factor `m k`). -/
def J0 (k : ℝ) (v : ℕ → ℝ) (n : ℕ) : ℝ := (k + n) * v n

/-- `J₊`: raises the level. -/
def Jp (k : ℝ) (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => towerA k n * v n

/-- `J₋`: lowers the level. -/
def Jm (k : ℝ) (v : ℕ → ℝ) (n : ℕ) : ℝ := towerA k n * v (n + 1)

theorem tower_comm_J0_Jp (k : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    J0 k (Jp k v) n - Jp k (J0 k v) n = Jp k v n := by
  cases n with
  | zero => simp [J0, Jp]
  | succ n =>
    simp only [J0, Jp]
    push_cast
    ring

theorem tower_comm_J0_Jm (k : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    J0 k (Jm k v) n - Jm k (J0 k v) n = -Jm k v n := by
  simp only [J0, Jm]
  push_cast
  ring

theorem tower_comm_Jp_Jm {k : ℝ} (hk : 0 ≤ k) (v : ℕ → ℝ) (n : ℕ) :
    Jp k (Jm k v) n - Jm k (Jp k v) n = -2 * J0 k v n := by
  cases n with
  | zero =>
    simp only [J0, Jp, Jm]
    have h := towerA_sq hk 0
    push_cast at h ⊢
    linear_combination (-(v 0)) * h
  | succ n =>
    simp only [J0, Jp, Jm]
    have h1 := towerA_sq hk n
    have h2 := towerA_sq hk (n + 1)
    push_cast at h1 h2 ⊢
    linear_combination (v (n + 1)) * h1 - (v (n + 1)) * h2

/-- The Casimir of the tower is the constant `k(k-1)`: the tower is irreducible of Bargmann index `k`. -/
theorem tower_casimir {k : ℝ} (hk : 0 ≤ k) (v : ℕ → ℝ) (n : ℕ) :
    J0 k (J0 k v) n - J0 k v n - Jp k (Jm k v) n = k * (k - 1) * v n := by
  cases n with
  | zero =>
    simp only [J0, Jp]
    push_cast
    ring
  | succ n =>
    simp only [J0, Jp, Jm]
    have h1 := towerA_sq hk n
    push_cast at h1 ⊢
    linear_combination (-(v (n + 1))) * h1

/-- Majorana's rest masses `m k/(k + n)` on level `n`. -/
def restMass (m k : ℝ) (n : ℕ) : ℝ := m * k / (k + n)

theorem restMass_strictAnti {m k : ℝ} (hm : 0 < m) (hk : 0 < k) : StrictAnti (restMass m k) := by
  intro a b hab
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have ha : (0 : ℝ) < k + a := by have := (Nat.cast_nonneg a : (0 : ℝ) ≤ a); linarith
  have hb : (0 : ℝ) < k + b := by linarith
  unfold restMass
  rw [div_lt_div_iff₀ hb ha]
  have hmk : 0 < m * k := mul_pos hm hk
  nlinarith

/-! ## Part 2: regularised norms -/

variable {N : ℕ} [NeZero N]

/-- `‖M_χ(x)‖ ≤ Z(1) T + ‖1/L(1, χ)‖` on `(0, T]`. -/
lemma norm_M_le_on_Ioc (χ : DirichletCharacter ℂ N) {T x : ℝ} (hx : x ∈ Ioc 0 T) :
    ‖M χ x‖ ≤ Z 1 * T + ‖1 / DirichletCharacter.LFunction χ 1‖ := by
  have h1 : ‖Mt χ x‖ ≤ Z 1 * x ^ (1 : ℝ) := norm_Mt_le χ hx.1 one_pos le_rfl
  rw [Real.rpow_one] at h1
  have h2 : Z 1 * x ≤ Z 1 * T := mul_le_mul_of_nonneg_left hx.2 (Z_nonneg 1)
  unfold M
  calc ‖Mt χ x + 1 / DirichletCharacter.LFunction χ 1‖
      ≤ ‖Mt χ x‖ + ‖1 / DirichletCharacter.LFunction χ 1‖ := norm_add_le _ _
    _ ≤ Z 1 * T + ‖1 / DirichletCharacter.LFunction χ 1‖ := by linarith

/-- **A fixed cut-off is finite for every character, unconditionally.** For `α < 1` and any `T`,
`∫₀^T |M_χ(x)|² x^{1-2α} dx < ∞`. So no fixed regularisation of this kind decides GRH. -/
theorem truncNorm_integrable (χ : DirichletCharacter ℂ N) {α : ℝ} (hα : α < 1) (T : ℝ) :
    IntegrableOn (fun x : ℝ => ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α)) (Ioc 0 T) := by
  set B := Z 1 * T + ‖1 / DirichletCharacter.LFunction χ 1‖ with hB
  have hint : IntegrableOn (fun x : ℝ => B ^ 2 * x ^ (1 - 2 * α)) (Ioc 0 T) := by
    rcases le_or_gt T 0 with hT | hT
    · rw [Ioc_eq_empty (not_lt.mpr hT)]
      exact integrableOn_empty
    · have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T) (r := 1 - 2 * α)
        (by linarith)).1
      exact this.const_mul _
  have hc : ContinuousOn (fun x : ℝ => ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α)) (Ioi 0) :=
    ((continuousOn_M χ).norm.pow 2).mul
      (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx))
  refine Integrable.mono' hint
    ((hc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx => ?_))
  have hx0 : 0 < x := hx.1
  have hp : 0 ≤ x ^ (1 - 2 * α) := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hp)]
  have hM := norm_M_le_on_Ioc χ hx
  have hM0 := norm_nonneg (M χ x)
  have hsq : ‖M χ x‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hM0 hM 2
  exact mul_le_mul_of_nonneg_right hsq hp

lemma integrand_nonneg (χ : DirichletCharacter ℂ N) (α : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α) :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx _)

/-- **The equivalence survives only in the limit.** For a primitive nontrivial `χ`, GRH holds iff for
every `α ∈ (3/4, 1)` the cut-off norms `∫₀^T |M_χ|² x^{1-2α} dx` are bounded uniformly in `T`. -/
theorem grh_iff_truncNorm_bounded (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) :
    GRH χ ↔ ∀ α ∈ Ioo (3 / 4 : ℝ) 1, ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
      ∫ x in (0 : ℝ)..T, ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α) ≤ C := by
  rw [grh_iff_finite_norm χ hprim hχ]
  constructor
  · intro h α hα
    refine ⟨∫ x in Ioi (0 : ℝ), ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α), fun T hT => ?_⟩
    rw [intervalIntegral.integral_of_le hT]
    refine setIntegral_mono_set (h α hα) ?_ 
      (ae_of_all _ fun x (hx : x ∈ Ioc (0 : ℝ) T) => (Ioc_subset_Ioi_self hx : x ∈ Ioi (0 : ℝ)))
    exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun x hx => integrand_nonneg χ α (le_of_lt hx))
  · intro h α hα
    obtain ⟨C, hC⟩ := h α hα
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded C 0
      (fun T : ℝ => truncNorm_integrable χ hα.2 T) tendsto_id ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    refine le_trans (le_of_eq ?_) (hC T hT)
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx' : x ∈ Icc (0 : ℝ) T := by rw [← uIcc_of_le hT]; exact hx
    simp only [Real.norm_eq_abs]
    exact abs_of_nonneg (integrand_nonneg χ α hx'.1)

end RiemannLab
