import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.MellinInversion

/-!
# Plancherel for integrable square-integrable functions, and Mellin–Plancherel

Mathlib (v4.36) has Plancherel for the Fourier transform on the Hilbert space `L²` (as an abstract
isometry `Lp.fourierTransformₗᵢ`) and for Schwartz functions. This file derives the integral form

  `∫ |𝓕 f|² = ∫ |f|²`   for `f ∈ L¹(ℝ) ∩ L²(ℝ)`,

by identifying the `L²` Fourier transform of `f` with its Fourier integral (they agree as tempered
distributions by the multiplication formula, hence almost everywhere), and then the Mellin form

  `∫₀^∞ |f(x)|² x^{2c-1} dx = (1/2π) ∫_ℝ |𝓜f(c + it)|² dt`

through the substitution `x = e^{-u}` (Mathlib's `mellin_eq_fourier`).
-/

open MeasureTheory Complex Set Filter
open scoped FourierTransform

noncomputable section

namespace RiemannLab

/-- `‖F‖² = ∫ |F|²` in `L²(ℝ)`. -/
lemma L2_norm_sq_eq (F : Lp ℂ 2 (volume : Measure ℝ)) : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) F, L2.inner_def]
  have h : (fun a => (inner ℂ (F a) (F a) : ℂ)) = fun a => ((‖F a‖ ^ 2 : ℝ) : ℂ) := by
    funext a
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [h, integral_ofReal]
  simp

/-- For `f ∈ L¹ ∩ L²`, the `L²` Fourier transform of `f` is a.e. its Fourier integral. -/
lemma fourier_toLp_ae {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    (𝓕 (hf2.toLp f) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ) Real.continuous_fourierChar
      continuous_inner hf1
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num))
    hcont.locallyIntegrable ?_
  intro g hg hgs
  have hgc : HasCompactSupport (fun x => (g x : ℂ)) := hgs.comp_left Complex.ofReal_zero
  have hgd : ContDiff ℝ ⊤ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  let φ : SchwartzMap ℝ ℂ := hgc.toSchwartzMap hgd
  have hφ : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  calc ∫ x, g x • (𝓕 (hf2.toLp f) : ℝ → ℂ) x
      = Lp.toTemperedDistribution (𝓕 (hf2.toLp f)) φ := by
        rw [Lp.toTemperedDistribution_apply]
        congr 1
        funext x
        rw [hφ, Complex.real_smul, smul_eq_mul]
    _ = 𝓕 (Lp.toTemperedDistribution (hf2.toLp f)) φ := by
        rw [Lp.fourier_toTemperedDistribution_eq]
    _ = ∫ x, 𝓕 φ x • (hf2.toLp f : ℝ → ℂ) x := by
        rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
    _ = ∫ x, 𝓕 (φ : ℝ → ℂ) x • f x := by
        refine integral_congr_ae ?_
        filter_upwards [hf2.coeFn_toLp] with x hx
        rw [hx, SchwartzMap.fourier_coe]
    _ = ∫ ξ, φ ξ • 𝓕 f ξ := by
        have := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
          Real.continuous_fourierChar continuous_inner φ.integrable hf1
        simpa using this
    _ = ∫ ξ, g ξ • 𝓕 f ξ := by
        congr 1
        funext ξ
        rw [hφ, Complex.real_smul, smul_eq_mul]

/-- **Plancherel, integral form.** For `f ∈ L¹(ℝ) ∩ L²(ℝ)`, `∫ |𝓕 f|² = ∫ |f|²`. -/
theorem plancherel {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := fourier_toLp_ae hf1 hf2
  calc ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ ξ, ‖(𝓕 (hf2.toLp f) : ℝ → ℂ) ξ‖ ^ 2 :=
        integral_congr_ae (h.mono fun x hx => by simp only [hx])
    _ = ‖𝓕 (hf2.toLp f)‖ ^ 2 := (L2_norm_sq_eq _).symm
    _ = ‖hf2.toLp f‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ x, ‖(hf2.toLp f : ℝ → ℂ) x‖ ^ 2 := L2_norm_sq_eq _
    _ = ∫ x, ‖f x‖ ^ 2 := integral_congr_ae (hf2.coeFn_toLp.mono fun x hx => by simp only [hx])

/-! ### The substitution `x = e^{-u}` (as in Mathlib's `MellinInversion`) -/

private theorem rexp_neg_deriv_aux :
    ∀ x ∈ univ, HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (Real.exp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem rexp_neg_image_aux : Real.exp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

private theorem rexp_neg_injOn_aux : univ.InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

private theorem rexp_cexp_aux (x : ℝ) (s : ℂ) (f : ℂ) :
    Real.exp (-x) • cexp (-↑x) ^ (s - 1) • f = cexp (-s * ↑x) • f := by
  change (Real.exp (-x) : ℂ) • _ = _ • f
  rw [← smul_assoc, smul_eq_mul]
  push_cast
  conv in cexp _ * _ => lhs; rw [← cpow_one (cexp _)]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _), cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  ring_nf

/-- A Mellin-convergent function becomes integrable on `ℝ` after `x = e^{-u}`. -/
theorem integrable_of_mellinConvergent {f : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f σ) :
    Integrable (fun u : ℝ => Real.exp (-σ * u) • f (Real.exp (-u))) := by
  rw [MellinConvergent, ← rexp_neg_image_aux, integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ rexp_neg_deriv_aux rexp_neg_injOn_aux] at hf
  replace hf : Integrable fun (x : ℝ) ↦ cexp (-↑σ * ↑x) • f (Real.exp (-x)) := by
    simpa [rexp_cexp_aux] using hf
  norm_cast at hf

/-- **Mellin–Plancherel on the line `Re s = c`.** If `x^{c-1} f` and `x^{2c-1} |f|²` are integrable
on `(0, ∞)`, then `∫₀^∞ |f(x)|² x^{2c-1} dx = (1/2π) ∫_ℝ |𝓜f(c + it)|² dt`. -/
theorem mellin_plancherel {f : ℝ → ℂ} {c : ℝ} (hf1 : MellinConvergent f c)
    (hf2 : MellinConvergent (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) ((2 * c : ℝ) : ℂ)) :
    ∫ x in Ioi (0:ℝ), ‖f x‖ ^ 2 * x ^ (2 * c - 1)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖mellin f (c + t * I)‖ ^ 2 := by
  set g : ℝ → ℂ := fun u => Real.exp (-c * u) • f (Real.exp (-u)) with hg_def
  have hg1 : Integrable g := integrable_of_mellinConvergent hf1
  have hg2' := integrable_of_mellinConvergent hf2
  have hnorm : ∀ u, ‖g u‖ ^ 2 = Real.exp (-(2 * c) * u) * ‖f (Real.exp (-u))‖ ^ 2 := by
    intro u
    have he : Real.exp (-c * u) ^ 2 = Real.exp (-(2 * c) * u) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [hg_def, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), he]
  have hg2 : MemLp g 2 := by
    rw [memLp_two_iff_integrable_sq_norm hg1.aestronglyMeasurable]
    refine hg2'.norm.congr (Eventually.of_forall fun u => ?_)
    simp only
    rw [hnorm u, norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg (sq_nonneg _)]
  -- left side: the Mellin transform of |f|² at the real point 2c
  have e1 : mellin (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) ((2 * c : ℝ) : ℂ)
      = ((∫ x in Ioi (0:ℝ), ‖f x‖ ^ 2 * x ^ (2 * c - 1) : ℝ) : ℂ) := by
    rw [mellin, ← integral_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [smul_eq_mul]
    rw [show ((2 * c : ℝ) : ℂ) - 1 = ((2 * c - 1 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (le_of_lt hx), ← ofReal_mul, mul_comm]
  have e2 : mellin (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) ((2 * c : ℝ) : ℂ)
      = ((∫ u, ‖g u‖ ^ 2 : ℝ) : ℂ) := by
    rw [mellin_eq_fourier, Real.fourier_real_eq, ← integral_ofReal]
    congr 1
    funext u
    simp only [ofReal_re, ofReal_im, zero_div, mul_zero, neg_zero, AddChar.map_zero_eq_one,
      one_smul]
    rw [hnorm u, Complex.real_smul, ofReal_mul]
  have hL : ∫ x in Ioi (0:ℝ), ‖f x‖ ^ 2 * x ^ (2 * c - 1) = ∫ u, ‖g u‖ ^ 2 :=
    ofReal_injective (e1.symm.trans e2)
  -- right side: the Fourier transform of g on the line, rescaled
  have hR : ∫ t : ℝ, ‖mellin f (c + t * I)‖ ^ 2 = 2 * Real.pi * ∫ ξ, ‖𝓕 g ξ‖ ^ 2 := by
    have hpt : ∀ t : ℝ, mellin f (c + t * I) = 𝓕 g (t / (2 * Real.pi)) := by
      intro t
      rw [mellin_eq_fourier]
      congr 1
      · congr 1
        funext u
        simp [hg_def]
      · simp
    simp_rw [hpt]
    rw [Measure.integral_comp_div (fun ξ => ‖𝓕 g ξ‖ ^ 2) (2 * Real.pi), smul_eq_mul,
      abs_of_pos (by positivity)]
  rw [hL, hR, plancherel hg1 hg2, ← mul_assoc, one_div,
    inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_mul]

end RiemannLab
