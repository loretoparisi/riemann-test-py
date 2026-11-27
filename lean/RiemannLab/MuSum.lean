import RiemannLab.LGrowth
import Mathlib.NumberTheory.LSeries.WeakPNT
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Sum

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

end RiemannLab
