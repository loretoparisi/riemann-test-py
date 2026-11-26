import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The combined norm identity: the parts Lean checks

This file formalises the unconditional half of the combined equation of `riemann_lab.combined`
(PR #5). For a Dirichlet character `χ` and `1 < α < 2`, write `c = 1 - α ∈ (-1, 0)`. The
Python side computes the same number four ways:

  ‖F_χ‖²_{D⁺_α} = ∫₀^∞ |M̃_χ(x)|² x^{1-2α} dx = (1/2π) ∫_ℝ |Γ(c+it) / L(1-2c-2it, χ)|² dt,

where `M̃_χ(x) = Σ μ(n) χ(n)/n · (e^{-x/n²} - 1)` is the Ramanujan–Hardy–Littlewood function with
its constant term removed.

What is proved here, with no `sorry` and no new axiom:

* `mellin_g`: the shifted Euler integral `∫₀^∞ x^{s-1} (e^{-x} - 1) dx = Γ(s)` on `-1 < Re s < 0`
  (integration by parts on top of Mathlib's `Γ`).
* `mellin_Mt`: the Mellin transform of `M̃_χ` on the strip `-1 < Re s < 0` equals
  `Γ(s) / L(1 - 2s, χ)` (Fubini–Tonelli, with Mathlib's Dirichlet L-series and
  `LSeries.mul_mu_eq_one`). This is the analytic heart of the identity.
* `combined_norm_identity`: the weighted `L²` norm of `M̃_χ` equals the line integral of
  `|Γ/L|²`, **assuming** the Mellin–Plancherel identity on the line `Re s = c`, which enters as
  the explicit hypothesis `MellinPlancherel`. Plancherel is a classical theorem, but this
  Mathlib version only has it for `L²`-classes and Schwartz functions, not for the integral of
  an `L¹ ∩ L²` function, so it is a named hypothesis here and not proved.

Nothing in this file says anything about zeros of `L(s, χ)` in the critical strip: on
`-1 < c < 0` the L-series converges absolutely, which is exactly why this half is
unconditional. The GRH-equivalent half and the blow-up limit are stated in
`RiemannLab/Open.lean`, with `sorry`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped LSeries.notation ArithmeticFunction.Moebius

noncomputable section

namespace RiemannLab

/-! ### The kernel `g(t) = e^{-t} - 1` -/

/-- The subtracted heat kernel `g(t) = e^{-t} - 1`, complex valued. -/
def g (t : ℝ) : ℂ := ((Real.exp (-t) - 1 : ℝ) : ℂ)

lemma continuous_g : Continuous g := by
  unfold g; fun_prop

lemma norm_g {t : ℝ} (ht : 0 ≤ t) : ‖g t‖ = 1 - Real.exp (-t) := by
  have h : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [g, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  ring

lemma norm_g_le_one {t : ℝ} (ht : 0 ≤ t) : ‖g t‖ ≤ 1 := by
  rw [norm_g ht]; linarith [Real.exp_pos (-t)]

lemma norm_g_le_self {t : ℝ} (ht : 0 ≤ t) : ‖g t‖ ≤ t := by
  rw [norm_g ht]; linarith [Real.add_one_le_exp (-t)]

/-- `t^{σ-1} |e^{-t} - 1|` is integrable on `(0, ∞)` for `-1 < σ < 0`. -/
lemma integrableOn_g_norm {σ : ℝ} (h1 : -1 < σ) (h0 : σ < 0) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖g t‖) (Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ (σ - 1) * ‖g t‖) (Ioi 0) :=
    (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)).mul
      (continuous_g.norm.continuousOn)
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · -- near 0: bounded by t^σ
    have hint : IntegrableOn (fun t : ℝ => t ^ σ) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' h1)
    refine hint.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (norm_nonneg _))]
    calc t ^ (σ - 1) * ‖g t‖ ≤ t ^ (σ - 1) * t :=
          mul_le_mul_of_nonneg_left (norm_g_le_self ht0.le) (Real.rpow_nonneg ht0.le _)
      _ = t ^ σ := by
          rw [← Real.rpow_add_one ht0.ne']; ring_nf
  · -- near ∞: bounded by t^{σ-1}
    have hint : IntegrableOn (fun t : ℝ => t ^ (σ - 1)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hint.mono' ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0:ℝ) < t := zero_lt_one.trans ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (norm_nonneg _))]
    calc t ^ (σ - 1) * ‖g t‖ ≤ t ^ (σ - 1) * 1 :=
          mul_le_mul_of_nonneg_left (norm_g_le_one ht0.le) (Real.rpow_nonneg ht0.le _)
      _ = t ^ (σ - 1) := mul_one _

lemma mellinConvergent_g {s : ℂ} (h1 : -1 < s.re) (h0 : s.re < 0) : MellinConvergent g s := by
  unfold MellinConvergent
  rw [mellin_convergent_iff_norm le_rfl measurableSet_Ioi
    continuous_g.aestronglyMeasurable]
  exact integrableOn_g_norm h1 h0

/-- **Shifted Euler integral.** `∫₀^∞ x^{s-1} (e^{-x} - 1) dx = Γ(s)` for `-1 < Re s < 0`. -/
theorem mellin_g {s : ℂ} (h1 : -1 < s.re) (h0 : s.re < 0) : mellin g s = Gamma s := by
  have hs : s ≠ 0 := fun h => by simp [h] at h0
  have hr : s - 1 ≠ -1 := fun h => hs (by linear_combination h)
  -- integration by parts with u = g, v = x^s / s
  set u' : ℝ → ℂ := fun t => -((Real.exp (-t) : ℝ) : ℂ)
  set v : ℝ → ℂ := fun y => (y : ℂ) ^ (s - 1 + 1) / (s - 1 + 1)
  set v' : ℝ → ℂ := fun y => (y : ℂ) ^ (s - 1)
  have hu : ∀ x ∈ Ioi (0:ℝ), HasDerivAt g (u' x) x := by
    intro x _
    have h := (((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).sub_const 1).ofReal_comp
    exact h.congr_deriv (by simp [u'])
  have hv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt v (v' x) x := fun x hx =>
    hasDerivAt_ofReal_cpow_const' (ne_of_gt hx) hr
  have hss : s - 1 + 1 = s := by ring
  -- integrability of u * v'
  have huv' : IntegrableOn (g * v') (Ioi 0) := by
    have := mellinConvergent_g h1 h0
    unfold MellinConvergent at this
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [v', smul_eq_mul, mul_comm]
  -- integrability of u' * v
  have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
    have hG := (GammaIntegral_convergent (s := s + 1) (by simp; linarith)).const_mul (-1 / s)
    refine IntegrableOn.congr_fun (f := fun x : ℝ => -1 / s * (((Real.exp (-x) : ℝ) : ℂ) *
      (x : ℂ) ^ (s + 1 - 1))) hG (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, u', v, hss, show s + 1 - 1 = s by ring]
    field_simp
  -- boundary term at 0
  have h_zero : Tendsto (g * v) (𝓝[>] 0) (𝓝 0) := by
    have hlim : Tendsto (fun t : ℝ => t ^ (s.re + 1) / ‖s‖) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ => t ^ (s.re + 1) / ‖s‖) 0 :=
        (Real.continuousAt_rpow_const 0 _ (Or.inr (by linarith))).div_const _
      have h00 : (fun t : ℝ => t ^ (s.re + 1) / ‖s‖) 0 = 0 := by
        simp [Real.zero_rpow (by linarith : s.re + 1 ≠ 0)]
      have ht := hc.tendsto
      rw [h00] at ht
      exact ht.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [Pi.mul_apply, v, hss, norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos ht]
    calc ‖g t‖ * (t ^ s.re / ‖s‖) ≤ t * (t ^ s.re / ‖s‖) :=
          mul_le_mul_of_nonneg_right (norm_g_le_self ht.le)
            (div_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _))
      _ = t ^ (s.re + 1) / ‖s‖ := by
          rw [Real.rpow_add_one ht.ne']; ring
  -- boundary term at ∞
  have h_infty : Tendsto (g * v) atTop (𝓝 0) := by
    have hlim : Tendsto (fun t : ℝ => t ^ s.re / ‖s‖) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := -s.re) (by linarith)).div_const ‖s‖
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Pi.mul_apply, v, hss, norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos ht]
    calc ‖g t‖ * (t ^ s.re / ‖s‖) ≤ 1 * (t ^ s.re / ‖s‖) :=
          mul_le_mul_of_nonneg_right (norm_g_le_one ht.le)
            (div_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _))
      _ = t ^ s.re / ‖s‖ := one_mul _
  have hparts := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h_zero h_infty
  -- assemble
  have hG : ∫ t in Ioi (0:ℝ), u' t * v t = -(Gamma (s + 1) / s) := by
    rw [Gamma_eq_integral (by simp; linarith), GammaIntegral, ← integral_div, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [u', v, hss, show s + 1 - 1 = s by ring]
    ring
  rw [mellin]
  calc ∫ t in Ioi (0:ℝ), (t : ℂ) ^ (s - 1) • g t
      = ∫ t in Ioi (0:ℝ), g t * v' t := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        simp [v', smul_eq_mul, mul_comm]
    _ = Gamma s := by
        rw [hparts, hG, Gamma_add_one s hs]
        field_simp
        ring

/-! ### Scaling by `n²` -/

/-- `b n = 1 / n²` (and `b 0 = 0`). -/
def b (n : ℕ) : ℝ := ((n : ℝ) ^ 2)⁻¹

lemma b_pos {n : ℕ} (hn : n ≠ 0) : 0 < b n := by
  unfold b; positivity

/-- For `x > 0`: `x^{-1} · ((x²)⁻¹)^{-s} = x^{-(1-2s)}`, as complex powers. -/
lemma scale_identity {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (((x ^ 2)⁻¹ : ℝ) : ℂ) ^ (-s) / (x : ℂ) = 1 / (x : ℂ) ^ (1 - 2 * s) := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hb : (((x ^ 2)⁻¹ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  rw [cpow_def_of_ne_zero hb, cpow_def_of_ne_zero hx', ← ofReal_log (by positivity),
    ← ofReal_log hx.le, Real.log_inv, Real.log_pow]
  have hxe : (x : ℂ) = Complex.exp (Real.log x) := by
    rw [← ofReal_exp, Real.exp_log hx]
  rw [hxe, ← Complex.exp_sub, one_div, ← Complex.exp_neg]
  congr 1
  push_cast
  ring

/-- Mellin transform of one term `t ↦ g(t / n²)`. -/
lemma mellin_g_scaled {n : ℕ} (hn : n ≠ 0) {s : ℂ} (h1 : -1 < s.re) (h0 : s.re < 0) :
    mellin (fun t => g (b n * t)) s = ((b n : ℝ) : ℂ) ^ (-s) * Gamma s := by
  rw [mellin_comp_mul_left _ _ (b_pos hn), mellin_g h1 h0, smul_eq_mul]

lemma mellinConvergent_g_scaled {n : ℕ} (hn : n ≠ 0) {s : ℂ} (h1 : -1 < s.re) (h0 : s.re < 0) :
    MellinConvergent (fun t => g (b n * t)) s :=
  (MellinConvergent.comp_mul_left (b_pos hn)).mpr (mellinConvergent_g h1 h0)

/-- `K(σ) = ∫₀^∞ t^{σ-1} |e^{-t} - 1| dt`. -/
def K (σ : ℝ) : ℝ := ∫ t in Ioi (0:ℝ), t ^ (σ - 1) * ‖g t‖

/-- The norm integral of one term: `∫ t^{σ-1} |g(t/n²)| dt = (1/n²)^{-σ} K(σ)`. -/
lemma integral_norm_scaled {n : ℕ} (hn : n ≠ 0) (σ : ℝ) :
    ∫ t in Ioi (0:ℝ), t ^ (σ - 1) * ‖g (b n * t)‖ = b n ^ (-σ) * K σ := by
  have hb := b_pos hn
  have h : ∀ t ∈ Ioi (0:ℝ), t ^ (σ - 1) * ‖g (b n * t)‖
      = b n ^ (1 - σ) * ((b n * t) ^ (σ - 1) * ‖g (b n * t)‖) := by
    intro t ht
    rw [Real.mul_rpow hb.le (le_of_lt ht), ← mul_assoc, ← mul_assoc,
      ← Real.rpow_add hb]
    simp
  rw [setIntegral_congr_fun measurableSet_Ioi h, integral_const_mul,
    integral_comp_mul_left_Ioi (fun u => u ^ (σ - 1) * ‖g u‖) 0 hb, mul_zero, smul_eq_mul,
    K, ← mul_assoc]
  congr 1
  rw [← Real.rpow_neg_one, ← Real.rpow_add hb]
  ring_nf

/-! ### The subtracted Ramanujan–Hardy–Littlewood function -/

variable {N : ℕ}

/-- Coefficients `μ(n) χ(n) / n`. -/
def coef (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ := (↗χ * ↗μ) n / n

lemma norm_coef_le (χ : DirichletCharacter ℂ N) (n : ℕ) : ‖coef χ n‖ ≤ (n : ℝ)⁻¹ := by
  unfold coef
  rw [norm_div, Pi.mul_apply, norm_mul, Complex.norm_natCast, div_eq_mul_inv]
  have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hμ : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc ‖χ n‖ * ‖((μ n : ℤ) : ℂ)‖ * (n : ℝ)⁻¹ ≤ 1 * 1 * (n : ℝ)⁻¹ := by
        gcongr
    _ = (n : ℝ)⁻¹ := by ring

/-- `M̃_χ(x) = Σ_n μ(n) χ(n)/n · (e^{-x/n²} - 1)`. -/
def Mt (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ := ∑' n : ℕ, coef χ n * g (b n * x)

/-- The `n`-th term of the Mellin integrand. -/
def F (χ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) • (coef χ n * g (b n * t))

lemma F_zero (χ : DirichletCharacter ℂ N) (s : ℂ) : F χ s 0 = 0 := by
  funext t; simp [F, coef]

lemma F_eq (χ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) (t : ℝ) :
    F χ s n t = coef χ n * ((t : ℂ) ^ (s - 1) • g (b n * t)) := by
  simp only [F, smul_eq_mul]; ring

lemma integrable_F (χ : DirichletCharacter ℂ N) {s : ℂ} (h1 : -1 < s.re) (h0 : s.re < 0)
    (n : ℕ) : Integrable (F χ s n) (volume.restrict (Ioi 0)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [F_zero]; exact integrable_zero _ _ _
  · have := (mellinConvergent_g_scaled hn h1 h0).const_mul (coef χ n)
    refine this.congr ?_
    exact Eventually.of_forall fun t => (F_eq χ s n t).symm

lemma integral_F (χ : DirichletCharacter ℂ N) {s : ℂ} (h1 : -1 < s.re) (h0 : s.re < 0) (n : ℕ) :
    ∫ t in Ioi (0:ℝ), F χ s n t = Gamma s * LSeries.term (↗χ * ↗μ) (1 - 2 * s) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [F_zero]
  · simp_rw [F_eq]
    rw [integral_const_mul]
    have := mellin_g_scaled hn h1 h0
    rw [mellin] at this
    rw [this, LSeries.term_of_ne_zero hn, coef]
    have hx : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hsc := scale_identity hx s
    simp only [b] at hsc ⊢
    push_cast at hsc ⊢
    calc (↗χ * ↗μ) n / (n : ℂ) * ((((n : ℂ) ^ 2)⁻¹) ^ (-s) * Gamma s)
        = Gamma s * ((↗χ * ↗μ) n * ((((n : ℂ) ^ 2)⁻¹) ^ (-s) / (n : ℂ))) := by ring
      _ = Gamma s * ((↗χ * ↗μ) n / (n : ℂ) ^ (1 - 2 * s)) := by
        rw [hsc]; ring

lemma integral_norm_F (χ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) :
    ∫ t in Ioi (0:ℝ), ‖F χ s n t‖ ≤ K s.re * (n : ℝ) ^ (2 * s.re - 1) := by
  have hK : 0 ≤ K s.re :=
    setIntegral_nonneg measurableSet_Ioi fun t (ht : 0 < t) =>
      mul_nonneg (Real.rpow_nonneg ht.le _) (norm_nonneg _)
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [F_zero, Pi.zero_apply, norm_zero, integral_zero]
    exact mul_nonneg hK (Real.rpow_nonneg le_rfl _)
  have hx : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h : ∀ t ∈ Ioi (0:ℝ), ‖F χ s n t‖ = ‖coef χ n‖ * (t ^ (s.re - 1) * ‖g (b n * t)‖) := by
    intro t ht
    rw [F, norm_smul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht]
    simp only [sub_re, one_re]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h, integral_const_mul, integral_norm_scaled hn]
  have hb : b n ^ (-s.re) = (n : ℝ) ^ (2 * s.re) := by
    rw [b, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
      ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  rw [hb]
  calc ‖coef χ n‖ * ((n : ℝ) ^ (2 * s.re) * K s.re)
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) ^ (2 * s.re) * K s.re) :=
        mul_le_mul_of_nonneg_right (norm_coef_le χ n)
          (mul_nonneg (Real.rpow_nonneg hx.le _) hK)
    _ = K s.re * (n : ℝ) ^ (2 * s.re - 1) := by
        rw [Real.rpow_sub_one hx.ne']; field_simp

theorem mellin_Mt_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (h1 : -1 < s.re)
    (h0 : s.re < 0) : mellin (Mt χ) s = Gamma s * LSeries (↗χ * ↗μ) (1 - 2 * s) := by
  have hsum : Summable fun n => ∫ t in Ioi (0:ℝ), ‖F χ s n t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
      (integral_norm_F χ s) ?_
    exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  have key := integral_tsum_of_summable_integral_norm (integrable_F χ h1 h0) hsum
  rw [mellin, LSeries, ← tsum_mul_left]
  simp_rw [← integral_F χ h1 h0]
  rw [key]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  simp only [Mt, F, smul_eq_mul]
  rw [tsum_mul_left]

/-- **Mellin transform of `M̃_χ` on the unconditional strip.** For `-1 < Re s < 0`,
`∫₀^∞ x^{s-1} M̃_χ(x) dx = Γ(s) / L(1 - 2s, χ)`. -/
theorem mellin_Mt (χ : DirichletCharacter ℂ N) {s : ℂ} (h1 : -1 < s.re) (h0 : s.re < 0) :
    mellin (Mt χ) s = Gamma s / LSeries ↗χ (1 - 2 * s) := by
  have hre : 1 < (1 - 2 * s).re := by simp; linarith
  have hinv := DirichletCharacter.LSeries.mul_mu_eq_one χ hre
  rw [mellin_Mt_eq_LSeries χ h1 h0, div_eq_mul_inv]
  congr 1
  exact (eq_inv_of_mul_eq_one_right hinv)

/-! ### The combined norm identity -/

/-- **Named hypothesis (not proved here): Mellin–Plancherel on the line `Re s = c`.**
`∫₀^∞ |f(x)|² x^{2c-1} dx = (1/2π) ∫_ℝ |𝓜f(c + it)|² dt`. It is Fourier–Plancherel after
`x = e^{-u}` (Mathlib has that substitution as `mellin_eq_fourier`), but the integral form of
Plancherel for `L¹ ∩ L²` functions is not in this Mathlib version. -/
def MellinPlancherel (f : ℝ → ℂ) (c : ℝ) : Prop :=
  ∫ x in Ioi (0:ℝ), ‖f x‖ ^ 2 * x ^ (2 * c - 1)
    = (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖mellin f (c + t * I)‖ ^ 2

/-- **Combined norm identity (unconditional range `1 < α < 2`).** Given Mellin–Plancherel on
`Re s = 1 - α`, the Ramanujan side equals the Masullo/L-function side:
`∫₀^∞ |M̃_χ(x)|² x^{1-2α} dx = (1/2π) ∫_ℝ |Γ(s_t) / L(1 - 2 s_t, χ)|² dt`, `s_t = 1 - α + it`. -/
theorem combined_norm_identity (χ : DirichletCharacter ℂ N) {α : ℝ} (h1 : 1 < α) (h2 : α < 2)
    (hP : MellinPlancherel (Mt χ) (1 - α)) :
    ∫ x in Ioi (0:ℝ), ‖Mt χ x‖ ^ 2 * x ^ (1 - 2 * α)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ,
          ‖Gamma ((1 - α : ℝ) + t * I) / LSeries ↗χ (1 - 2 * ((1 - α : ℝ) + t * I))‖ ^ 2 := by
  unfold MellinPlancherel at hP
  rw [show (1 - 2 * α) = 2 * (1 - α) - 1 by ring, hP]
  congr 2
  funext t
  rw [mellin_Mt χ (by simp; linarith) (by simp; linarith)]

end RiemannLab
