import RiemannLab.LGrowth
import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.NumberTheory.AbelSummation

/-!
# `Σ μ(n)χ(n)/n = 1/L(1, χ)` for a nontrivial Dirichlet character

The classical value of the conditionally convergent series, derived from Mathlib's prime number
theorem in arithmetic progressions in three elementary steps:

* `tendsto_psiχ_div`: `Σ_{n ≤ X} χ(n)Λ(n) = o(X)`;
* `tendsto_Mμ_div`: `Σ_{n ≤ X} μ(n)χ(n) = o(X)` (Landau);
* `tendsto_sum_mu_div`: `Σ_{n ≤ X} μ(n)χ(n)/n → 1/L(1, χ)`.
-/

open Complex Filter Topology Finset DirichletCharacter
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt ArithmeticFunction.zeta

noncomputable section

namespace RiemannLab

variable {N : ℕ} [NeZero N]

/-- `ψ_χ(X) = Σ_{n ≤ X} χ(n)Λ(n)`. -/
def psiχ (χ : DirichletCharacter ℂ N) (X : ℕ) : ℂ := ∑ n ∈ Ioc 0 X, χ n * (Λ n : ℂ)

/-! ### Step A: `ψ_χ(X) = o(X)` -/

lemma psiχ_eq (χ : DirichletCharacter ℂ N) (X : ℕ) :
    psiχ χ X = ∑ a : ZMod N, χ a *
      ((∑ n ∈ Icc 0 ⌊(X : ℝ)⌋₊, ArithmeticFunction.vonMangoldt.residueClass a n : ℝ) : ℂ) := by
  rw [Nat.floor_natCast, psiχ]
  have h0 : Icc 0 X = insert 0 (Ioc 0 X) := by
    ext n; simp only [mem_Icc, mem_insert, mem_Ioc]; omega
  simp only [ofReal_sum, mul_sum]
  rw [sum_comm]
  rw [h0, sum_insert (by simp)]
  have hz : ∑ a : ZMod N, χ a * ((ArithmeticFunction.vonMangoldt.residueClass a 0 : ℝ) : ℂ) = 0 :=
    sum_eq_zero fun a _ => by simp
  rw [hz, zero_add]
  refine sum_congr rfl fun n _ => ?_
  rw [sum_eq_single (n : ZMod N)]
  · simp [ArithmeticFunction.vonMangoldt.residueClass]
  · intro a _ ha
    simp [ArithmeticFunction.vonMangoldt.residueClass, Ne.symm ha]
  · simp

/-- **Twisted prime number theorem.** For `χ ≠ 1`, `Σ_{n ≤ X} χ(n)Λ(n) = o(X)`. -/
theorem tendsto_psiχ_div (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Tendsto (fun X : ℕ => psiχ χ X / X) atTop (𝓝 0) := by
  have hzero : ∑ a : ZMod N, χ a = 0 := MulChar.sum_eq_zero_of_ne_one hχ
  have hterm : ∀ a : ZMod N, Tendsto (fun X : ℕ => χ a *
      (((∑ n ∈ Icc 0 ⌊(X : ℝ)⌋₊, ArithmeticFunction.vonMangoldt.residueClass a n : ℝ) / X : ℝ) : ℂ))
      atTop (𝓝 (χ a * (((Nat.totient N : ℝ)⁻¹ : ℝ) : ℂ))) := by
    intro a
    by_cases ha : IsUnit a
    · refine tendsto_const_nhds.mul ?_
      exact (continuous_ofReal.tendsto _).comp
        ((ArithmeticFunction.vonMangoldt.tendsto_sum_residueClass_div_atTop ha).comp
          tendsto_natCast_atTop_atTop)
    · have : χ a = 0 := χ.map_nonunit ha
      simp only [this, zero_mul]
      exact tendsto_const_nhds
  have hsum := tendsto_finsetSum (univ : Finset (ZMod N)) fun a _ => hterm a
  rw [← sum_mul, hzero, zero_mul] at hsum
  refine hsum.congr fun X => ?_
  rw [psiχ_eq, sum_div]
  refine sum_congr rfl fun a _ => ?_
  push_cast
  ring

/-! ### Step B: `Σ_{n ≤ X} μ(n)χ(n) = o(X)` (Landau) -/

/-- `M_μ(X) = Σ_{n ≤ X} χ(n)μ(n)`. -/
def Mμ (χ : DirichletCharacter ℂ N) (X : ℕ) : ℂ := ∑ n ∈ Ioc 0 X, χ n * (μ n : ℂ)

/-- `μ(n) log n = -(μ * Λ)(n)`. -/
lemma pmul_moebius_log :
    ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) ArithmeticFunction.log
      = -((μ : ArithmeticFunction ℝ) * Λ) := by
  have h1 : ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) ArithmeticFunction.log
      * (ζ : ArithmeticFunction ℝ) = -Λ := by
    ext n
    rw [ArithmeticFunction.coe_mul_zeta_apply, neg_apply,
      ← ArithmeticFunction.sum_moebius_mul_log_eq]
    refine sum_congr rfl fun d _ => ?_
    simp [ArithmeticFunction.pmul_apply]
  calc ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) ArithmeticFunction.log
      = ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) ArithmeticFunction.log
          * ((ζ : ArithmeticFunction ℝ) * μ) := by
        rw [ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one]
    _ = -Λ * μ := by rw [← mul_assoc, h1]
    _ = -((μ : ArithmeticFunction ℝ) * Λ) := by ring

omit [NeZero N] in
lemma mu_log_twisted (χ : DirichletCharacter ℂ N) (n : ℕ) :
    χ n * (μ n : ℂ) * (Real.log n : ℂ) = -∑ x ∈ n.divisorsAntidiagonal,
      (χ x.1 * (μ x.1 : ℂ)) * (χ x.2 * (Λ x.2 : ℂ)) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) pmul_moebius_log
  simp only [ArithmeticFunction.pmul_apply, neg_apply,
    ArithmeticFunction.mul_apply, ArithmeticFunction.log_apply,
    ArithmeticFunction.intCoe_apply] at h
  have h' : ((μ n : ℂ) * (Real.log n : ℂ)) = -∑ x ∈ n.divisorsAntidiagonal,
      (μ x.1 : ℂ) * (Λ x.2 : ℂ) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) h
    simp only [ofReal_mul, ofReal_neg, ofReal_sum, ofReal_intCast] at this
    exact this
  rw [mul_assoc, h', mul_neg, mul_sum]
  congr 1
  refine sum_congr rfl fun x hx => ?_
  have hn : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
  rw [← hn, Nat.cast_mul, map_mul]
  ring

omit [NeZero N] in
lemma sum_mu_log (χ : DirichletCharacter ℂ N) (X : ℕ) :
    ∑ n ∈ Ioc 0 X, χ n * (μ n : ℂ) * (Real.log n : ℂ)
      = -∑ d ∈ Ioc 0 X, χ d * (μ d : ℂ) * psiχ χ (X / d) := by
  let f : ArithmeticFunction ℂ := ⟨fun n => χ n * (μ n : ℂ), by simp⟩
  let g : ArithmeticFunction ℂ := ⟨fun n => χ n * (Λ n : ℂ), by simp⟩
  have hfg : ∀ n : ℕ, χ n * (μ n : ℂ) * (Real.log n : ℂ) = -(f * g) n := fun n => by
    rw [mu_log_twisted, ArithmeticFunction.mul_apply]
    rfl
  simp only [hfg, sum_neg_distrib, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  rfl

omit [NeZero N] in
lemma norm_chi_mu_le (χ : DirichletCharacter ℂ N) (n : ℕ) : ‖χ n * (μ n : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have h2 : ‖(μ n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc ‖χ n‖ * ‖(μ n : ℂ)‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

lemma sum_inv_le_log (X : ℕ) : ∑ d ∈ Ioc 0 X, ((d : ℝ))⁻¹ ≤ 1 + Real.log X := by
  have h := harmonic_le_one_add_log X
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have : Ioc 0 X = Icc 1 X := by ext n; simp; omega
  rwa [this]

lemma sum_log_sub_le (X : ℕ) : ∑ n ∈ Ioc 0 X, (Real.log X - Real.log n) ≤ X := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp
  rw [sum_sub_distrib, Real.sum_log_eq_log_factorial, sum_const, Nat.card_Ioc, Nat.sub_zero,
    nsmul_eq_mul]
  have h := Stirling.le_log_factorial_stirling hX.ne'
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  have hpi : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.two_le_pi])
  linarith

/-- **Landau.** For `χ ≠ 1`, `Σ_{n ≤ X} μ(n)χ(n) = o(X)`. -/
theorem tendsto_Mμ_div (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Tendsto (fun X : ℕ => Mμ χ X / X) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set e : ℝ := ε / 4 with he
  have he0 : 0 < e := by positivity
  -- `|ψ_χ(Y)| ≤ e Y + C` for all `Y`
  obtain ⟨Y0, hY0⟩ := (Metric.tendsto_atTop.mp (tendsto_psiχ_div χ hχ)) e he0
  set C : ℝ := ∑ Y ∈ range Y0, ‖psiχ χ Y‖ with hC
  have hC0 : 0 ≤ C := sum_nonneg fun _ _ => norm_nonneg _
  have hpsi : ∀ Y : ℕ, ‖psiχ χ Y‖ ≤ e * Y + C := by
    intro Y
    rcases lt_or_ge Y Y0 with hY | hY
    · have := single_le_sum (f := fun Y => ‖psiχ χ Y‖) (fun _ _ => norm_nonneg _)
        (mem_range.mpr hY)
      have : 0 ≤ e * Y := by positivity
      linarith
    · have h := hY0 Y hY
      rw [dist_zero_right, norm_div, Complex.norm_natCast] at h
      rcases Nat.eq_zero_or_pos Y with rfl | hYp
      · simp [psiχ, hC0]
      · have hYr : (0:ℝ) < Y := by exact_mod_cast hYp
        rw [div_lt_iff₀ hYr] at h
        linarith
  -- eventually `log X ≥ (C + 1)/e` and `log X ≥ 1`
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (max 1 ((C + 1) / e))
  filter_upwards [hlog, eventually_ge_atTop 1] with X hXlog hX1
  simp only [Function.comp_apply] at hXlog
  have hL1 : 1 ≤ Real.log X := (le_max_left _ _).trans hXlog
  have hL2 : (C + 1) / e ≤ Real.log X := (le_max_right _ _).trans hXlog
  have hXr : (1:ℝ) ≤ X := by exact_mod_cast hX1
  have hXpos : (0:ℝ) < X := by linarith
  -- the two pieces
  have hA : ‖∑ n ∈ Ioc 0 X, χ n * (μ n : ℂ) * (Real.log n : ℂ)‖
      ≤ e * X * (1 + Real.log X) + C * X := by
    rw [sum_mu_log, norm_neg]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ d ∈ Ioc 0 X, ‖χ d * (μ d : ℂ) * psiχ χ (X / d)‖
        ≤ ∑ d ∈ Ioc 0 X, (e * X * ((d : ℝ))⁻¹ + C) := by
          refine sum_le_sum fun d hd => ?_
          have hd0 : (0:ℝ) < d := by exact_mod_cast (mem_Ioc.mp hd).1
          rw [norm_mul]
          refine (mul_le_of_le_one_left (norm_nonneg _) (norm_chi_mu_le χ d)).trans ?_
          refine (hpsi (X / d)).trans ?_
          have : ((X / d : ℕ) : ℝ) ≤ X * (d : ℝ)⁻¹ := by
            rw [← div_eq_mul_inv]; exact Nat.cast_div_le
          nlinarith
      _ = e * X * ∑ d ∈ Ioc 0 X, ((d : ℝ))⁻¹ + C * X := by
          rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
          ring
      _ ≤ e * X * (1 + Real.log X) + C * X := by
          gcongr
          exact sum_inv_le_log X
  have hB : ‖∑ n ∈ Ioc 0 X, χ n * (μ n : ℂ) * ((Real.log X - Real.log n : ℝ) : ℂ)‖ ≤ X := by
    refine (norm_sum_le _ _).trans ((sum_le_sum fun n hn => ?_).trans (sum_log_sub_le X))
    have hn0 : (0:ℝ) < n := by exact_mod_cast (mem_Ioc.mp hn).1
    have hnX : (n : ℝ) ≤ X := by exact_mod_cast (mem_Ioc.mp hn).2
    have hle : 0 ≤ Real.log X - Real.log n := sub_nonneg.mpr (Real.log_le_log hn0 hnX)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hle]
    exact mul_le_of_le_one_left hle (norm_chi_mu_le χ n)
  have hsplit : Mμ χ X * (Real.log X : ℂ) = ∑ n ∈ Ioc 0 X, χ n * (μ n : ℂ) * (Real.log n : ℂ)
      + ∑ n ∈ Ioc 0 X, χ n * (μ n : ℂ) * ((Real.log X - Real.log n : ℝ) : ℂ) := by
    rw [Mμ, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    push_cast
    ring
  have hM : ‖Mμ χ X‖ * Real.log X ≤ e * X * (1 + Real.log X) + C * X + X := by
    have h := congrArg norm hsplit
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h
    rw [h]
    exact (norm_add_le _ _).trans (add_le_add hA hB)
  rw [dist_zero_right, norm_div, Complex.norm_natCast, div_lt_iff₀ hXpos]
  have hLpos : 0 < Real.log X := by linarith
  have hCe : C + 1 ≤ e * Real.log X := by rwa [div_le_iff₀ he0, mul_comm] at hL2
  have hX0 : (0:ℝ) ≤ X := hXpos.le
  have h1 : e * X ≤ e * X * Real.log X := by
    have := mul_le_mul_of_nonneg_left hL1 (mul_nonneg he0.le hX0)
    linarith
  have h2 : (C + 1) * X ≤ e * Real.log X * X := mul_le_mul_of_nonneg_right hCe hX0
  have : ‖Mμ χ X‖ * Real.log X ≤ 3 * e * X * Real.log X := by
    nlinarith
  have h3 : ‖Mμ χ X‖ ≤ 3 * e * X := by
    by_contra hcon
    push Not at hcon
    nlinarith
  nlinarith

/-! ### Step C: the tail of `Σ χ(m)/m` -/

/-- `S(k) = Σ_{m ≤ k} χ(m)/m`. -/
def Sχ (χ : DirichletCharacter ℂ N) (k : ℕ) : ℂ := ∑ m ∈ Ioc 0 k, χ m / m

/-- `χ` with the value at `0` set to `0`. -/
def χ0 (χ : DirichletCharacter ℂ N) (m : ℕ) : ℂ := if m = 0 then 0 else χ m

omit [NeZero N] in
lemma A_eq_sum_χ0 (χ : DirichletCharacter ℂ N) (t : ℝ) :
    A χ t = ∑ k ∈ Icc 0 ⌊t⌋₊, χ0 χ k := by
  rw [A]
  have : Icc 0 ⌊t⌋₊ = insert 0 (Icc 1 ⌊t⌋₊) := by
    ext n; simp only [mem_Icc, mem_insert]; omega
  rw [this, sum_insert (by simp), χ0, if_pos rfl, zero_add]
  refine sum_congr rfl fun k hk => ?_
  rw [χ0, if_neg (by have := (mem_Icc.mp hk).1; omega)]

lemma cpow_neg_two {t : ℝ} (_ht : 0 < t) :
    (t : ℂ) ^ ((-1 : ℂ) - 1) = (((t ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [show (-1 : ℂ) - 1 = -((2 : ℕ) : ℂ) by push_cast; ring, cpow_neg, cpow_natCast]
  push_cast
  rfl

lemma integrableOn_A_div_sq (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {a : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (((t ^ 2)⁻¹ : ℝ) : ℂ) * A χ t) (Set.Ioi a) := by
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => (N : ℝ) * t ^ (-2 : ℝ)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ha).const_mul _
  refine hint.mono' ?_ ((MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_)
  · refine MeasureTheory.AEStronglyMeasurable.mul ?_ (measurable_A χ).aestronglyMeasurable
    exact (Complex.continuous_ofReal.measurable.comp
      ((measurable_id.pow_const 2).inv)).aestronglyMeasurable
  · have ht0 : 0 < t := ha.trans ht
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Real.rpow_neg ht0.le, Real.rpow_two, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_A_le χ hχ t) (by positivity)

lemma norm_integral_A_div_sq_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {a : ℝ}
    (ha : 0 < a) :
    ‖∫ t in Set.Ioi a, (((t ^ 2)⁻¹ : ℝ) : ℂ) * A χ t‖ ≤ N / a := by
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => (N : ℝ) * t ^ (-2 : ℝ)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) ha).const_mul _
  have hval : ∫ t in Set.Ioi a, (N : ℝ) * t ^ (-2 : ℝ) = N / a := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) ha]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    field_simp
  rw [← hval]
  refine MeasureTheory.norm_integral_le_of_norm_le hint
    ((MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_)
  have ht0 : 0 < t := ha.trans ht
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.rpow_neg ht0.le, Real.rpow_two, mul_comm]
  exact mul_le_mul_of_nonneg_right (norm_A_le χ hχ t) (by positivity)

/-- `L(1, χ) = ∫₁^∞ A(t) t^{-2} dt`. -/
lemma LFunction_one_eq_integral (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    LFunction χ 1 = ∫ t in Set.Ioi (1:ℝ), (((t ^ 2)⁻¹ : ℝ) : ℂ) * A χ t := by
  rw [LFunction_eq_J χ hχ (by norm_num), J, mellinOn, one_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [smul_eq_mul]
  rw [cpow_neg_two (zero_lt_one.trans ht)]

omit [NeZero N] in
/-- **Abel summation for `S(k)`.** `S(k) = A(k)/k + ∫₁^k A(t) t^{-2} dt`. -/
lemma Sχ_eq (χ : DirichletCharacter ℂ N) (k : ℕ) :
    Sχ χ k = A χ k / k + ∫ t in Set.Ioc (1:ℝ) k, (((t ^ 2)⁻¹ : ℝ) : ℂ) * A χ t := by
  set f : ℝ → ℂ := fun t => ((t⁻¹ : ℝ) : ℂ) with hf
  have hderiv : ∀ t : ℝ, t ≠ 0 → HasDerivAt f (((-(t ^ 2)⁻¹ : ℝ)) : ℂ) t := fun t ht =>
    (hasDerivAt_inv ht).ofReal_comp
  have hd : ∀ t ∈ Set.Icc (1:ℝ) k, DifferentiableAt ℝ f t := fun t ht =>
    (hderiv t (by linarith [ht.1])).differentiableAt
  have hderiv_eq : ∀ t ∈ Set.Icc (1:ℝ) k, deriv f t = (((-(t ^ 2)⁻¹ : ℝ)) : ℂ) := fun t ht =>
    (hderiv t (by linarith [ht.1])).deriv
  have hint : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (1:ℝ) k) := by
    have hc : ContinuousOn (fun t : ℝ => (((-(t ^ 2)⁻¹ : ℝ)) : ℂ)) (Set.Icc (1:ℝ) k) :=
      Complex.continuous_ofReal.comp_continuousOn
        ((continuousOn_id.pow 2).inv₀ fun t ht =>
          pow_ne_zero 2 (by have : (1:ℝ) ≤ t := ht.1; simp only [id]; linarith)).neg
    exact (hc.integrableOn_compact isCompact_Icc).congr_fun
      (fun t ht => (hderiv_eq t ht).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₀' (χ0 χ) (by simp [χ0]) k hd hint
  have hL : ∑ m ∈ Icc 0 k, f m * χ0 χ m = Sχ χ k := by
    rw [Sχ]
    have : Icc 0 k = insert 0 (Ioc 0 k) := by
      ext n; simp only [mem_Icc, mem_insert, mem_Ioc]; omega
    rw [this, sum_insert (by simp), χ0, if_pos rfl, mul_zero, zero_add]
    refine sum_congr rfl fun m hm => ?_
    rw [χ0, if_neg (by have := (mem_Ioc.mp hm).1; omega), hf]
    push_cast
    ring
  rw [hL] at h
  have hAk : A χ k = ∑ m ∈ Icc 0 k, χ0 χ m := by rw [A_eq_sum_χ0, Nat.floor_natCast]
  rw [h]
  have hI : ∫ t in Set.Ioc (1:ℝ) k, deriv f t * ∑ m ∈ Icc 0 ⌊t⌋₊, χ0 χ m
      = -∫ t in Set.Ioc (1:ℝ) k, (((t ^ 2)⁻¹ : ℝ) : ℂ) * A χ t := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [hderiv_eq t ⟨ht.1.le, ht.2⟩, ← A_eq_sum_χ0]
    push_cast
    ring
  rw [hI, ← hAk, hf]
  push_cast
  ring

/-- **Tail bound.** `|L(1, χ) − S(k)| ≤ 2N/k` for `k ≥ 1`. -/
theorem norm_LFunction_one_sub_Sχ_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {k : ℕ}
    (hk : 1 ≤ k) : ‖LFunction χ 1 - Sχ χ k‖ ≤ 2 * N / k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hsplit : LFunction χ 1 = (∫ t in Set.Ioc (1:ℝ) k, (((t ^ 2)⁻¹ : ℝ) : ℂ) * A χ t)
      + ∫ t in Set.Ioi (k:ℝ), (((t ^ 2)⁻¹ : ℝ) : ℂ) * A χ t := by
    rw [LFunction_one_eq_integral χ hχ, ← Set.Ioc_union_Ioi_eq_Ioi hk1,
      MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        ((integrableOn_A_div_sq χ hχ zero_lt_one).mono_set Set.Ioc_subset_Ioi_self)
        (integrableOn_A_div_sq χ hχ hk0)]
  rw [hsplit, Sχ_eq]
  have h1 := norm_integral_A_div_sq_le χ hχ hk0
  have h2 : ‖A χ k / k‖ ≤ N / k := by
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (norm_A_le χ hχ k) hk0.le
  calc ‖(∫ t in Set.Ioc (1:ℝ) k, (((t ^ 2)⁻¹ : ℝ) : ℂ) * A χ t)
        + (∫ t in Set.Ioi (k:ℝ), (((t ^ 2)⁻¹ : ℝ) : ℂ) * A χ t)
        - (A χ k / k + ∫ t in Set.Ioc (1:ℝ) k, (((t ^ 2)⁻¹ : ℝ) : ℂ) * A χ t)‖
      = ‖(∫ t in Set.Ioi (k:ℝ), (((t ^ 2)⁻¹ : ℝ) : ℂ) * A χ t) - A χ k / k‖ := by ring_nf
    _ ≤ N / k + N / k := (norm_sub_le _ _).trans (add_le_add h1 h2)
    _ = 2 * N / k := by ring

/-! ### Step C: `Σ_{n ≤ X} μ(n)χ(n)/n → 1/L(1, χ)` -/

/-- `s(X) = Σ_{n ≤ X} μ(n)χ(n)/n`. -/
def sμ (χ : DirichletCharacter ℂ N) (X : ℕ) : ℂ := ∑ n ∈ Ioc 0 X, χ n * (μ n : ℂ) / n

omit [NeZero N] in
/-- `Σ_{n ≤ X} μχ(n)/n · S(X/n) = 1` for `X ≥ 1`. -/
lemma sum_mu_div_mul_Sχ (χ : DirichletCharacter ℂ N) {X : ℕ} (hX : 1 ≤ X) :
    ∑ n ∈ Ioc 0 X, χ n * (μ n : ℂ) / n * Sχ χ (X / n) = 1 := by
  let f : ArithmeticFunction ℂ := ⟨fun n => χ n * (μ n : ℂ) / n, by simp⟩
  let g : ArithmeticFunction ℂ := ⟨fun n => χ n / n, by simp⟩
  have hfg : ∀ k : ℕ, (f * g) k = if k = 1 then 1 else 0 := by
    intro k
    rw [ArithmeticFunction.mul_apply]
    have hmu := congrArg (fun F : ArithmeticFunction ℤ => F k)
      ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply] at hmu
    have hterm : ∀ x ∈ k.divisorsAntidiagonal, f x.1 * g x.2
        = χ k / k * ((μ x.1 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 : ℤ) : ℂ) := by
      intro x hx
      have hk := Nat.mem_divisorsAntidiagonal.mp hx
      have h2 : x.2 ≠ 0 := fun h => hk.2 (by rw [← hk.1, h, mul_zero])
      rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg h2]
      show χ x.1 * (μ x.1 : ℂ) / x.1 * (χ x.2 / x.2) = _
      rw [← hk.1, Nat.cast_mul, map_mul]
      push_cast
      field_simp
    rw [sum_congr rfl hterm, ← mul_sum, ← Int.cast_sum, hmu]
    split_ifs with h
    · subst h; simp
    · simp
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum f g X
  simp only [hfg] at h
  rw [sum_ite_eq' (Ioc 0 X) 1, if_pos (mem_Ioc.mpr ⟨one_pos, hX⟩)] at h
  exact h.symm

omit [NeZero N] in
/-- Discrete Abel summation for `Σ μχ(n)/n` on a block `(a, a+d+1]`. -/
lemma sum_Ioc_mu_div_eq (χ : DirichletCharacter ℂ N) (a d : ℕ) :
    ∑ n ∈ Ioc a (a + d + 1), χ n * (μ n : ℂ) / n
      = Mμ χ (a + d + 1) / (a + d + 1 : ℕ) - Mμ χ a / (a + 1 : ℕ)
        + ∑ n ∈ Ico (a + 1) (a + d + 1), Mμ χ n * (1 / n - 1 / (n + 1 : ℕ)) := by
  induction d with
  | zero =>
    simp only [add_zero, Ico_self, sum_empty]
    rw [sum_Ioc_succ_top le_rfl, Ioc_self, sum_empty, zero_add, Mμ, Mμ,
      sum_Ioc_succ_top (Nat.zero_le a)]
    ring
  | succ d ih =>
    have e : a + (d + 1) + 1 = a + d + 1 + 1 := by ring
    have hM : Mμ χ (a + d + 1 + 1) = Mμ χ (a + d + 1)
        + χ (a + d + 1 + 1 : ℕ) * (μ (a + d + 1 + 1) : ℂ) := by
      simp only [Mμ]
      rw [sum_Ioc_succ_top (by omega : 0 ≤ a + d + 1)]
    rw [e, sum_Ioc_succ_top (by omega : a ≤ a + d + 1), ih,
      sum_Ico_succ_top (by omega : a + 1 ≤ a + d + 1), hM]
    have h1 : ((a + d + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : a + d + 1 ≠ 0)
    have h2 : ((a + d + 1 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : a + d + 1 + 1 ≠ 0)
    field_simp
    ring

omit [NeZero N] in
/-- On a block `(a, b]` with `b < 2(a+1)` and `|M_μ(Y)| ≤ δ Y` for `Y ≥ a`,
`|Σ_{a < n ≤ b} μχ(n)/n| ≤ 4δ`. -/
lemma norm_sum_Ioc_mu_div_le (χ : DirichletCharacter ℂ N) {δ : ℝ} (hδ : 0 ≤ δ) {a b : ℕ}
    (hM : ∀ Y : ℕ, a ≤ Y → ‖Mμ χ Y‖ ≤ δ * Y) (hab : a ≤ b) (hb2 : b < 2 * (a + 1)) :
    ‖∑ n ∈ Ioc a b, χ n * (μ n : ℂ) / n‖ ≤ 4 * δ := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · simp; positivity
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
  rw [sum_Ioc_mu_div_eq]
  have hb0 : (0:ℝ) < ((a + d + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < a + d + 1)
  have ha0 : (0:ℝ) < ((a + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < a + 1)
  have t1 : ‖Mμ χ (a + d + 1) / ((a + d + 1 : ℕ) : ℂ)‖ ≤ δ := by
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hb0]
    exact hM _ (by omega)
  have t2 : ‖Mμ χ a / ((a + 1 : ℕ) : ℂ)‖ ≤ δ := by
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ ha0]
    refine (hM a le_rfl).trans ?_
    push_cast
    nlinarith
  have t3 : ‖∑ n ∈ Ico (a + 1) (a + d + 1), Mμ χ n * (1 / n - 1 / (n + 1 : ℕ))‖ ≤ 2 * δ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ Ico (a + 1) (a + d + 1), ‖Mμ χ n * (1 / n - 1 / (n + 1 : ℕ))‖
        ≤ ∑ n ∈ Ico (a + 1) (a + d + 1), δ / ((a + 1 : ℕ) : ℝ) := by
          refine sum_le_sum fun n hn => ?_
          have hn1 : a + 1 ≤ n := (mem_Ico.mp hn).1
          have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
          have hn0' : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
          have hn1' : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
          have hdiff : (1 / (n : ℂ) - 1 / ((n + 1 : ℕ) : ℂ)) = (((n : ℝ) * (n + 1))⁻¹ : ℝ) := by
            push_cast
            field_simp
            ring
          rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          calc ‖Mμ χ n‖ * ((n : ℝ) * (n + 1))⁻¹ ≤ δ * n * ((n : ℝ) * (n + 1))⁻¹ :=
                mul_le_mul_of_nonneg_right (hM n (by omega)) (by positivity)
            _ = δ / (n + 1) := by field_simp
            _ ≤ δ / ((a + 1 : ℕ) : ℝ) := by
                apply div_le_div_of_nonneg_left hδ ha0
                push_cast
                have : ((a : ℝ) + 1) ≤ n := by exact_mod_cast hn1
                linarith
      _ = (d : ℝ) * (δ / ((a + 1 : ℕ) : ℝ)) := by
          rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
          congr 1
          push_cast
          congr 1
          omega
      _ ≤ 2 * δ := by
          have hd : (d : ℝ) ≤ 2 * ((a + 1 : ℕ) : ℝ) := by
            have : d ≤ 2 * (a + 1) := by omega
            exact_mod_cast this
          rw [mul_div_assoc', div_le_iff₀ ha0]
          nlinarith
  calc ‖Mμ χ (a + d + 1) / ((a + d + 1 : ℕ) : ℂ) - Mμ χ a / ((a + 1 : ℕ) : ℂ)
        + ∑ n ∈ Ico (a + 1) (a + d + 1), Mμ χ n * (1 / n - 1 / (n + 1 : ℕ))‖
      ≤ δ + δ + 2 * δ := (norm_add_le _ _).trans
        (add_le_add ((norm_sub_le _ _).trans (add_le_add t1 t2)) t3)
    _ = 4 * δ := by ring

/-- The error term `T(X) = Σ_{n ≤ X} μχ(n)/n · (L(1,χ) − S(X/n))`. -/
def Tμ (χ : DirichletCharacter ℂ N) (X : ℕ) : ℂ :=
  ∑ n ∈ Ioc 0 X, χ n * (μ n : ℂ) / n * (LFunction χ 1 - Sχ χ (X / n))

lemma sμ_mul_L (χ : DirichletCharacter ℂ N) {X : ℕ} (hX : 1 ≤ X) :
    sμ χ X * LFunction χ 1 = 1 + Tμ χ X := by
  rw [sμ, sum_mul, Tμ, ← sum_mu_div_mul_Sχ χ hX, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => by ring

omit [NeZero N] in
lemma norm_mu_div_le (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖χ n * (μ n : ℂ) / n‖ ≤ 1 / n := by
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_chi_mu_le χ n) (Nat.cast_nonneg n)

/-- Terms with `X/n ≥ K` contribute at most `4N/K`. -/
lemma norm_Tμ_head_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {K X : ℕ} (hK : 1 ≤ K)
    (hX : 1 ≤ X) :
    ‖∑ n ∈ Ioc 0 (X / K), χ n * (μ n : ℂ) / n * (LFunction χ 1 - Sχ χ (X / n))‖
      ≤ 4 * N / K := by
  have hX0 : (0:ℝ) < X := by exact_mod_cast hX
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK
  have hterm : ∀ n ∈ Ioc 0 (X / K),
      ‖χ n * (μ n : ℂ) / n * (LFunction χ 1 - Sχ χ (X / n))‖ ≤ 4 * N / X := by
    intro n hn
    obtain ⟨hn0, hnK⟩ := mem_Ioc.mp hn
    have hnX : n ≤ X := hnK.trans (Nat.div_le_self _ _)
    have hm : 1 ≤ X / n := (Nat.le_div_iff_mul_le hn0).mpr (by omega)
    have hlt := Nat.lt_mul_div_succ X hn0
    have h2 : X < 2 * (n * (X / n)) := by
      have : n ≤ n * (X / n) := Nat.le_mul_of_pos_right n hm
      linarith [Nat.mul_succ n (X / n)]
    have h2r : (X : ℝ) < 2 * ((n : ℝ) * ((X / n : ℕ) : ℝ)) := by exact_mod_cast h2
    have hn0r : (0:ℝ) < n := by exact_mod_cast hn0
    have hm0r : (0:ℝ) < ((X / n : ℕ) : ℝ) := by exact_mod_cast hm
    rw [norm_mul]
    calc ‖χ n * (μ n : ℂ) / n‖ * ‖LFunction χ 1 - Sχ χ (X / n)‖
        ≤ (1 / n) * (2 * N / ((X / n : ℕ) : ℝ)) :=
          mul_le_mul (norm_mu_div_le χ n) (norm_LFunction_one_sub_Sχ_le χ hχ hm)
            (norm_nonneg _) (by positivity)
      _ = 2 * N / ((n : ℝ) * ((X / n : ℕ) : ℝ)) := by field_simp
      _ ≤ 4 * N / X := by
          rw [div_le_div_iff₀ (by positivity) hX0]
          have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
          nlinarith
  refine (norm_sum_le _ _).trans ((sum_le_sum hterm).trans ?_)
  rw [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  have hc : ((X / K : ℕ) : ℝ) ≤ (X : ℝ) / K := Nat.cast_div_le
  calc ((X / K : ℕ) : ℝ) * (4 * N / X) ≤ (X : ℝ) / K * (4 * N / X) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 4 * N / K := by field_simp

omit [NeZero N] in
lemma filter_div_eq (X K j : ℕ) (hj : 1 ≤ j) (hjK : j < K) :
    {n ∈ Ioc (X / K) X | X / n = j} = Ioc (X / (j + 1)) (X / j) := by
  ext n
  simp only [mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨hKn, hnX⟩, hj'⟩
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hKn
    refine ⟨(Nat.div_lt_iff_lt_mul (by omega)).mpr ?_, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
    · have := (Nat.div_lt_iff_lt_mul hn0).mp (by omega : X / n < j + 1)
      linarith [mul_comm n (j + 1)]
    · have := (Nat.le_div_iff_mul_le hn0).mp (le_of_eq hj'.symm)
      linarith [mul_comm n j]
  · rintro ⟨h1, h2⟩
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) h1
    have hjn : n * j ≤ X := (Nat.le_div_iff_mul_le (by omega)).mp h2
    have hXn : X < n * (j + 1) := (Nat.div_lt_iff_lt_mul (by omega)).mp h1
    refine ⟨⟨lt_of_le_of_lt (Nat.div_le_div_left (by omega) (by omega)) h1,
      h2.trans (Nat.div_le_self _ _)⟩, le_antisymm ?_ ?_⟩
    · have := (Nat.div_lt_iff_lt_mul hn0).mpr (by linarith [mul_comm n (j + 1)] : X < (j + 1) * n)
      omega
    · exact (Nat.le_div_iff_mul_le hn0).mpr (by linarith [mul_comm n j])

/-- Terms with `X/n < K` contribute at most `8NKδ`, given `|M_μ(Y)| ≤ δY` for `Y ≥ A₀`
and `X ≥ A₀ K`. -/
lemma norm_Tμ_tail_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    {A0 K X : ℕ} (hK1 : 1 ≤ K) (hM : ∀ Y : ℕ, A0 ≤ Y → ‖Mμ χ Y‖ ≤ δ * Y) (hX : A0 * K ≤ X) :
    ‖∑ n ∈ Ioc (X / K) X, χ n * (μ n : ℂ) / n * (LFunction χ 1 - Sχ χ (X / n))‖
      ≤ 8 * N * K * δ := by
  have hmaps : ∀ n ∈ Ioc (X / K) X, X / n ∈ Ico 1 K := by
    intro n hn
    obtain ⟨hKn, hnX⟩ := mem_Ioc.mp hn
    have hK : 0 < K := hK1
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hKn
    refine mem_Ico.mpr ⟨(Nat.le_div_iff_mul_le hn0).mpr (by rw [one_mul]; exact hnX), ?_⟩
    exact (Nat.div_lt_iff_lt_mul hn0).mpr (by
      have := (Nat.div_lt_iff_lt_mul hK).mp hKn; linarith [mul_comm n K])
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hblock : ∀ j ∈ Ico 1 K,
      ‖∑ n ∈ Ioc (X / K) X with X / n = j,
          χ n * (μ n : ℂ) / n * (LFunction χ 1 - Sχ χ (X / n))‖ ≤ 8 * N * δ := by
    intro j hj
    obtain ⟨hj1, hjK⟩ := mem_Ico.mp hj
    rw [sum_congr rfl (fun n hn => by rw [(mem_filter.mp hn).2]), ← sum_mul,
      filter_div_eq X K j hj1 hjK, norm_mul]
    set a := X / (j + 1)
    set b := X / j
    have haA : A0 ≤ a := (Nat.le_div_iff_mul_le (by omega)).mpr
      ((Nat.mul_le_mul_left A0 (by omega : j + 1 ≤ K)).trans hX)
    have hab : a ≤ b := Nat.div_le_div_left (by omega) (by omega)
    have hb2 : b < 2 * (a + 1) := by
      have h1 : b * j ≤ X := Nat.div_mul_le_self X j
      have h2 : X < (j + 1) * (a + 1) := Nat.lt_mul_div_succ X (by omega)
      have h3 : (j + 1) * (a + 1) ≤ (2 * (a + 1)) * j := by nlinarith
      exact Nat.lt_of_mul_lt_mul_right (by omega : b * j < 2 * (a + 1) * j)
    have hB := norm_sum_Ioc_mu_div_le χ hδ (fun Y hY => hM Y (haA.trans hY)) hab hb2
    have hL : ‖LFunction χ 1 - Sχ χ j‖ ≤ 2 * N := by
      refine (norm_LFunction_one_sub_Sχ_le χ hχ hj1).trans ?_
      have hj1r : (1:ℝ) ≤ j := by exact_mod_cast hj1
      exact div_le_self (by positivity) hj1r
    calc _ ≤ 4 * δ * (2 * N) := mul_le_mul hB hL (norm_nonneg _) (by positivity)
      _ = 8 * N * δ := by ring
  refine (norm_sum_le _ _).trans ((sum_le_sum hblock).trans ?_)
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul]
  have : ((K - 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.sub_le K 1
  have h8 : 0 ≤ 8 * (N:ℝ) * δ := by positivity
  nlinarith

/-- `T(X) → 0`. -/
lemma tendsto_Tμ (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Tendsto (Tμ χ) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hN : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈8 * N / ε⌉₊ + 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by omega
  have hK0 : (0:ℝ) < K := by exact_mod_cast hK1
  have hKε : 8 * N / ε < K := by
    rw [hK]; push_cast; linarith [Nat.le_ceil (8 * (N:ℝ) / ε)]
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = ε / (32 * N * K) := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; positivity
  obtain ⟨A0, hA0⟩ := (Metric.tendsto_atTop.mp (tendsto_Mμ_div χ hχ)) d hd0
  have hM : ∀ Y : ℕ, A0 ≤ Y → ‖Mμ χ Y‖ ≤ d * Y := by
    intro Y hY
    rcases Nat.eq_zero_or_pos Y with rfl | hY0
    · simp [Mμ]
    have := hA0 Y hY
    rw [dist_zero_right, norm_div, Complex.norm_natCast] at this
    have hY0r : (0:ℝ) < Y := by exact_mod_cast hY0
    rw [div_lt_iff₀ hY0r] at this
    linarith
  refine ⟨A0 * K + 1, fun X hX => ?_⟩
  rw [dist_zero_right, Tμ, ← sum_Ioc_consecutive _ (Nat.zero_le (X / K)) (Nat.div_le_self X K)]
  have h1 := norm_Tμ_head_le χ hχ hK1 (by omega : 1 ≤ X)
  have h2 := norm_Tμ_tail_le χ hχ hd0.le hK1 hM (by omega : A0 * K ≤ X)
  have e1 : 4 * N / K < ε / 2 := by
    rw [div_lt_iff₀ hK0]
    rw [div_lt_iff₀ hε] at hKε
    linarith
  have e2 : 8 * N * K * d = ε / 4 := by rw [hd]; field_simp; ring
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ 4 * N / K + 8 * N * K * d := add_le_add h1 h2
    _ < ε := by linarith

/-- **Main theorem of Step C.** For a non-principal character `χ`,
`Σ_{n ≤ X} μ(n)χ(n)/n → 1/L(1, χ)`. -/
theorem tendsto_sum_mu_div (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Tendsto (fun X : ℕ => ∑ n ∈ Ioc 0 X, χ n * (μ n : ℂ) / n) atTop
      (𝓝 (1 / LFunction χ 1)) := by
  have hL : LFunction χ 1 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simp)
  have hlim : Tendsto (fun X => (1 + Tμ χ X) / LFunction χ 1) atTop
      (𝓝 ((1 + 0) / LFunction χ 1)) :=
    (tendsto_const_nhds.add (tendsto_Tμ χ hχ)).div_const _
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [← sμ_mul_L χ hX, mul_div_cancel_right₀ _ hL, sμ]

end RiemannLab
