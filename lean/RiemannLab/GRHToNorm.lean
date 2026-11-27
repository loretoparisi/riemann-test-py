import RiemannLab.InvLBound
import RiemannLab.Plancherel
import Mathlib.Analysis.MellinInversion

/-!
# GRH implies finite weighted norms of `M_χ`

The "GRH ⇒ finite norms" half of the GRH-equivalent part of the combined equation, proved here
with no `sorry`. Fix `α ∈ (3/4, 1)` and put `c' = 1 - α ∈ (0, 1/4)`.

1. `f = M̃_χ − C_χ g` (with `g(x) = e^{-x} − 1`, `C_χ = 1/L(1, χ)`) has Mellin transform
   `H(s) = Γ(s+1) · dslope φ 0 s`, `φ(s) = 1/L(1-2s, χ)`, on `-1 < Re s < 0`.
2. Under GRH, `H` is holomorphic on `-1 < Re s < 1/4`, and on the closed strip
   `-1/2 ≤ Re s ≤ c'` it is `O((1 + Im² s)⁻¹)`: the polynomial bound for `1/L`
   (`norm_inv_LFunction_le`) is beaten by the decay `|Γ(s)| |Im s|^k ≤ Γ(Re s + k)`.
3. Mellin inversion on `Re s = -1/2` and a rectangle contour shift give
   `f(x) = (1/2π) ∫ x^{-(c' + iy)} H(c' + iy) dy` for every `x > 0`.
4. So `x^{c'} f(x)` is a Fourier transform of an `L¹ ∩ L²` function, and Plancherel gives
   `∫₀^∞ |f(x)|² x^{2c'-1} dx < ∞`. Since `M_χ = f + C_χ e^{-x}` and `2c' - 1 = 1 - 2α`,
   the weighted norm of `M_χ` is finite.
-/

open Complex MeasureTheory Set Filter Topology DirichletCharacter Metric
open scoped LSeries.notation FourierTransform

noncomputable section

namespace RiemannLab

/-! ### Decay of `Γ` on vertical lines -/

lemma norm_Gamma_le_real {s : ℂ} (hs : 0 < s.re) : ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Gamma_eq_integral hs, Real.Gamma_eq_integral hs, GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0:ℝ) < x := hx
  simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    norm_cpow_eq_rpow_re_of_pos hx0, sub_re, one_re]

/-- `|Γ(s)| |Im s|^k ≤ Γ(Re s + k)` for `Re s > 0`. -/
lemma norm_Gamma_mul_pow_le (k : ℕ) :
    ∀ s : ℂ, 0 < s.re → ‖Gamma s‖ * |s.im| ^ k ≤ Real.Gamma (s.re + k) := by
  induction k with
  | zero => intro s hs; simpa using norm_Gamma_le_real hs
  | succ k ih =>
    intro s hs
    have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; exact lt_irrefl _ hs
    have h1 := ih (s + 1) (by rw [add_re, one_re]; linarith)
    rw [Gamma_add_one s hs0, add_re, one_re, add_im, one_im, add_zero] at h1
    have him : |s.im| ≤ ‖s‖ := abs_im_le_norm s
    calc ‖Gamma s‖ * |s.im| ^ (k + 1) = ‖Gamma s‖ * |s.im| * |s.im| ^ k := by ring
      _ ≤ ‖Gamma s‖ * ‖s‖ * |s.im| ^ k := by gcongr
      _ = ‖s * Gamma s‖ * |s.im| ^ k := by rw [norm_mul, mul_comm ‖s‖]
      _ ≤ Real.Gamma (s.re + 1 + k) := h1
      _ = Real.Gamma (s.re + ↑(k + 1)) := by push_cast; ring_nf

/-! ### Shifting a vertical line integral -/

lemma continuous_vertical {Φ : ℂ → ℂ} {a b σ : ℝ}
    (hΦ : DifferentiableOn ℂ Φ {s : ℂ | a ≤ s.re ∧ s.re ≤ b}) (hσ : σ ∈ Icc a b) :
    Continuous fun y : ℝ => Φ (σ + y * I) := by
  refine hΦ.continuousOn.comp_continuous (by fun_prop) fun y => ?_
  simpa using hσ

lemma integrable_vertical {Φ : ℂ → ℂ} {a b σ E : ℝ}
    (hΦ : DifferentiableOn ℂ Φ {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Φ s‖ ≤ E * (1 + s.im ^ 2)⁻¹) (hσ : σ ∈ Icc a b) :
    Integrable fun y : ℝ => Φ (σ + y * I) := by
  refine (integrable_inv_one_add_sq.const_mul E).mono'
    (continuous_vertical hΦ hσ).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have := hbd (σ + y * I) (by simpa using hσ.1) (by simpa using hσ.2)
  simpa using this

/-- **Contour shift.** If `Φ` is holomorphic on the closed strip `a ≤ Re s ≤ b` and
`|Φ(s)| ≤ E (1 + Im² s)⁻¹` there, the integrals of `Φ` over the two vertical edges agree. -/
theorem integral_vertical_eq {Φ : ℂ → ℂ} {a b E : ℝ} (hab : a ≤ b)
    (hΦ : DifferentiableOn ℂ Φ {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hbd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Φ s‖ ≤ E * (1 + s.im ^ 2)⁻¹) :
    ∫ y : ℝ, Φ (a + y * I) = ∫ y : ℝ, Φ (b + y * I) := by
  have hia := integrable_vertical hΦ hbd ⟨le_rfl, hab⟩
  have hib := integrable_vertical hΦ hbd ⟨hab, le_rfl⟩
  set e : ℝ → ℂ := fun T => (∫ x : ℝ in a..b, Φ (x + (-T) * I))
    - (∫ x : ℝ in a..b, Φ (x + T * I)) + I • (∫ y : ℝ in (-T)..T, Φ (b + y * I))
    - I • (∫ y : ℝ in (-T)..T, Φ (a + y * I)) with he
  have he0 : ∀ T : ℝ, e T = 0 := by
    intro T
    have h := integral_boundary_rect_eq_zero_of_differentiableOn Φ (a + (-T) * I) (b + T * I)
      (hΦ.mono fun s hs => by
        have h1 : s.re ∈ uIcc a b := by simpa using hs.1
        rw [uIcc_of_le hab] at h1
        exact ⟨h1.1, h1.2⟩)
    simpa [he] using h
  have hdecay : Tendsto (fun T : ℝ => E * (1 + T ^ 2)⁻¹ * |b - a|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => (1 + T ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero))
    have := (h1.const_mul E).mul_const |b - a|
    rwa [mul_zero, zero_mul] at this
  have hH : ∀ u : ℝ, ∀ T : ℝ, (u = T ∨ u = -T) →
      ‖∫ x : ℝ in a..b, Φ (x + u * I)‖ ≤ E * (1 + T ^ 2)⁻¹ * |b - a| := by
    intro u T hu
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [uIoc_of_le hab] at hx
    have := hbd (x + u * I) (by simpa using hx.1.le) (by simpa using hx.2)
    have hu2 : u ^ 2 = T ^ 2 := by rcases hu with rfl | rfl <;> ring
    simpa [hu2] using this
  have htop : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, Φ (x + T * I)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun T => hH T T (Or.inl rfl)) hdecay
  have hbot : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, Φ (x + (-T) * I)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun T => hH (-T) T (Or.inr rfl)) hdecay
  have hva := intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have hvb := intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto e atTop (𝓝 (0 - 0 + I • (∫ y : ℝ, Φ (b + y * I))
      - I • (∫ y : ℝ, Φ (a + y * I)))) :=
    ((hbot.sub htop).add (hvb.const_smul I)).sub (hva.const_smul I)
  have h0 : Tendsto e atTop (𝓝 0) := by
    rw [show e = fun _ => 0 from funext he0]
    exact tendsto_const_nhds
  have := tendsto_nhds_unique hlim h0
  simp only [sub_zero, zero_add, smul_eq_mul] at this
  have hI : I ≠ 0 := I_ne_zero
  have := mul_left_cancel₀ hI (sub_eq_zero.mp this)
  exact this.symm

/-! ### Plancherel in the reverse direction -/

lemma cpow_eq_fourier_kernel {x : ℝ} (hx : 0 < x) (c y : ℝ) :
    (x : ℂ) ^ (-((c : ℂ) + y * I)) = ((x ^ (-c) : ℝ) : ℂ) *
      Complex.exp (↑(-2 * Real.pi * y * (Real.log x / (2 * Real.pi))) * I) := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [cpow_def_of_ne_zero hx', ofReal_cpow hx.le, cpow_def_of_ne_zero hx', ← Complex.exp_add,
    ← ofReal_log hx.le]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- If `f(x) = (1/2π) ∫ x^{-(c+iy)} h(y) dy` on `x > 0` with `h ∈ L¹ ∩ L²`, then
`∫₀^∞ |f(x)|² x^{2c-1} dx < ∞`. -/
theorem integrableOn_weighted_of_mellinInv {h : ℝ → ℂ} (hi : Integrable h) (h2 : MemLp h 2)
    {c : ℝ} {f : ℝ → ℂ}
    (hf : ∀ x : ℝ, 0 < x → f x = (1 / (2 * Real.pi)) • ∫ y : ℝ, (x : ℂ) ^ (-((c : ℂ) + y * I)) • h y) :
    IntegrableOn (fun x : ℝ => ‖f x‖ ^ 2 * x ^ (2 * c - 1)) (Ioi 0) := by
  have hF2 : MemLp (𝓕 h) 2 := (Lp.memLp _).ae_eq (fourier_toLp_ae hi h2)
  have hG : Integrable fun u : ℝ => ‖𝓕 h (u / (2 * Real.pi))‖ ^ 2 :=
    ((memLp_two_iff_integrable_sq_norm hF2.aestronglyMeasurable).1 hF2).comp_div
      (by positivity)
  set k : ℝ := (1 / (2 * Real.pi)) ^ 2 with hk
  have hfx : ∀ x : ℝ, 0 < x → ‖f x‖ ^ 2 * x ^ (2 * c - 1)
      = k * ‖𝓕 h (Real.log x / (2 * Real.pi))‖ ^ 2 * x⁻¹ := by
    intro x hx
    rw [hf x hx, Real.fourier_real_eq_integral_exp_smul]
    have hint : ∫ y : ℝ, (x : ℂ) ^ (-((c : ℂ) + y * I)) • h y
        = ((x ^ (-c) : ℝ) : ℂ) * ∫ v : ℝ, Complex.exp
          (↑(-2 * Real.pi * v * (Real.log x / (2 * Real.pi))) * I) • h v := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [smul_eq_mul]
      rw [cpow_eq_fourier_kernel hx c y]
      ring
    rw [hint, norm_smul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hx.le _),
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (2 * Real.pi)), hk]
    have hxc : (x ^ (-c)) ^ 2 * x ^ (2 * c - 1) = x⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx, ← Real.rpow_neg_one]
      congr 1
      push_cast
      ring
    calc (1 / (2 * Real.pi) * (x ^ (-c) * ‖∫ v : ℝ, Complex.exp
          (↑(-2 * Real.pi * v * (Real.log x / (2 * Real.pi))) * I) • h v‖)) ^ 2 * x ^ (2 * c - 1)
        = (1 / (2 * Real.pi)) ^ 2 * ‖∫ v : ℝ, Complex.exp
          (↑(-2 * Real.pi * v * (Real.log x / (2 * Real.pi))) * I) • h v‖ ^ 2
          * ((x ^ (-c)) ^ 2 * x ^ (2 * c - 1)) := by ring
      _ = _ := by rw [hxc]
  have himage : Real.exp '' univ = Ioi 0 := by rw [Set.image_univ, Real.range_exp]
  have hsub : IntegrableOn (fun x : ℝ => k * ‖𝓕 h (Real.log x / (2 * Real.pi))‖ ^ 2 * x⁻¹)
      (Ioi 0) := by
    rw [← himage, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
      integrableOn_univ]
    refine (hG.const_mul k).congr (Eventually.of_forall fun u => ?_)
    simp only [smul_eq_mul, Real.log_exp, abs_of_pos (Real.exp_pos u)]
    field_simp
  refine hsub.congr_fun (fun x hx => (hfx x hx).symm) measurableSet_Ioi

end RiemannLab
