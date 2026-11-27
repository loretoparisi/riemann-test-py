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
open scoped FourierTransform ContDiff

noncomputable section

namespace RiemannLab

/-- `‖F‖² = ∫ |F|²` in `L²(ℝ)`. -/
lemma L2_norm_sq_eq (F : Lp ℂ 2 (volume : Measure ℝ)) : ‖F‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) F, L2.inner_def, ← integral_re (L2.integrable_inner F F)]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (F a)

/-- For `f ∈ L¹ ∩ L²`, the `L²` Fourier transform of `f` is a.e. its Fourier integral. -/
lemma fourier_toLp_ae {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ) Real.continuous_fourierChar
      continuous_inner hf1
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ))).locallyIntegrable (by norm_num))
    hcont.locallyIntegrable ?_
  intro g hg hgs
  have hgc : HasCompactSupport (fun x => (g x : ℂ)) := hgs.comp_left Complex.ofReal_zero
  have hgd : ContDiff ℝ ∞ (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  let φ : SchwartzMap ℝ ℂ := hgc.toSchwartzMap hgd
  have hφ : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  calc ∫ x, g x • ((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
      = Lp.toTemperedDistribution (𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) φ := by
        rw [Lp.toTemperedDistribution_apply]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        show g x • _ = φ x • _
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
        have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume)
          (ν := volume) (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner
          φ.integrable hf1
        rw [flip_innerₗ] at h
        exact h
    _ = ∫ ξ, g ξ • 𝓕 f ξ := by
        congr 1

/-- **Plancherel, integral form.** For `f ∈ L¹(ℝ) ∩ L²(ℝ)`, `∫ |𝓕 f|² = ∫ |f|²`. -/
theorem plancherel {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f 2) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := fourier_toLp_ae hf1 hf2
  calc ∫ ξ, ‖𝓕 f ξ‖ ^ 2
        = ∫ ξ, ‖((𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2 :=
        integral_congr_ae (h.mono fun x hx => by simp only [hx])
    _ = ‖(𝓕 (hf2.toLp f) : Lp ℂ 2 (volume : Measure ℝ))‖ ^ 2 := (L2_norm_sq_eq _).symm
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

/-- A Mellin-convergent function becomes integrable on `ℝ` after `x = e^{-u}`. -/
theorem integrable_of_mellinConvergent {f : ℝ → ℂ} {σ : ℝ} (hf : MellinConvergent f σ) :
    Integrable (fun u : ℝ => Real.exp (-σ * u) • f (Real.exp (-u))) := by
  rw [MellinConvergent, ← rexp_neg_image_aux, integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ rexp_neg_deriv_aux rexp_neg_injOn_aux, integrableOn_univ] at hf
  refine hf.congr (Eventually.of_forall fun x => ?_)
  have hpos := Real.exp_pos (-x)
  have h1 : ((Real.exp (-x) : ℝ) : ℂ) ^ ((σ : ℂ) - 1) = ((Real.exp (-x) ^ (σ - 1) : ℝ) : ℂ) := by
    rw [ofReal_cpow hpos.le, ofReal_sub, ofReal_one]
  have h2 : Real.exp (-x) * Real.exp (-x) ^ (σ - 1) = Real.exp (-σ * x) := by
    rw [Real.rpow_def_of_pos hpos, Real.log_exp, ← Real.exp_add]
    congr 1
    ring
  simp only [Function.comp_apply, abs_neg, abs_of_pos hpos]
  rw [h1, smul_eq_mul, Complex.real_smul, Complex.real_smul, ← mul_assoc, ← ofReal_mul, h2]

set_option maxHeartbeats 800000 in
/-- **Mellin–Plancherel on the line `Re s = c`.** If `x^{c-1} f` and `x^{2c-1} |f|²` are integrable
on `(0, ∞)`, then `∫₀^∞ |f(x)|² x^{2c-1} dx = (1/2π) ∫_ℝ |𝓜f(c + it)|² dt`. -/
theorem mellin_plancherel {f : ℝ → ℂ} {c : ℝ} (hf1 : MellinConvergent f c)
    (hf2 : MellinConvergent (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) ((2 * c : ℝ) : ℂ)) :
    ∫ x in Ioi (0:ℝ), ‖f x‖ ^ 2 * x ^ (2 * c - 1)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖mellin f (c + t * I)‖ ^ 2 := by
  have hg1 : Integrable (fun u : ℝ => Real.exp (-c * u) • f (Real.exp (-u))) :=
    integrable_of_mellinConvergent hf1
  have hg2' := integrable_of_mellinConvergent hf2
  have hnorm : ∀ u : ℝ, ‖Real.exp (-c * u) • f (Real.exp (-u))‖ ^ 2
      = Real.exp (-(2 * c) * u) * ‖f (Real.exp (-u))‖ ^ 2 := by
    intro u
    have he : Real.exp (-c * u) ^ 2 = Real.exp (-(2 * c) * u) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), he]
  have hg2 : MemLp (fun u : ℝ => Real.exp (-c * u) • f (Real.exp (-u))) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hg1.aestronglyMeasurable]
    refine hg2'.norm.congr (Eventually.of_forall fun u => ?_)
    show ‖Real.exp (-(2 * c) * u) • ((‖f (Real.exp (-u))‖ ^ 2 : ℝ) : ℂ)‖
      = ‖Real.exp (-c * u) • f (Real.exp (-u))‖ ^ 2
    rw [hnorm u, norm_smul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg (sq_nonneg _)]
  -- left side: the Mellin transform of |f|² at the real point 2c, computed two ways
  have e1 : mellin (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) ((2 * c : ℝ) : ℂ)
      = ((∫ x in Ioi (0:ℝ), ‖f x‖ ^ 2 * x ^ (2 * c - 1) : ℝ) : ℂ) := by
    rw [mellin, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [smul_eq_mul]
    rw [show ((2 * c : ℝ) : ℂ) - 1 = ((2 * c - 1 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (le_of_lt hx), ofReal_mul]
    ring
  have e2 : mellin (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) ((2 * c : ℝ) : ℂ)
      = ((∫ u : ℝ, ‖Real.exp (-c * u) • f (Real.exp (-u))‖ ^ 2 : ℝ) : ℂ) := by
    rw [mellin_eq_fourier, Real.fourier_real_eq, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [ofReal_re, ofReal_im, zero_div, mul_zero, neg_zero, AddChar.map_zero_eq_one,
      one_smul]
    rw [hnorm u, Complex.real_smul, ofReal_mul]
  have hL : ∫ x in Ioi (0:ℝ), ‖f x‖ ^ 2 * x ^ (2 * c - 1)
      = ∫ u : ℝ, ‖Real.exp (-c * u) • f (Real.exp (-u))‖ ^ 2 :=
    ofReal_injective (e1.symm.trans e2)
  -- right side: on the line, the Mellin transform is the Fourier transform of g, rescaled
  set G : ℝ → ℝ := fun ξ => ‖𝓕 (fun u : ℝ => Real.exp (-c * u) • f (Real.exp (-u))) ξ‖ ^ 2
    with hG
  have hpt : ∀ t : ℝ, ‖mellin f (c + t * I)‖ ^ 2 = G (t / (2 * Real.pi)) := by
    intro t
    have hre : ((c : ℂ) + t * I).re = c := by simp
    have him : ((c : ℂ) + t * I).im = t := by simp
    rw [mellin_eq_fourier, hre, him]
  have hR : ∫ t : ℝ, ‖mellin f (c + t * I)‖ ^ 2 = 2 * Real.pi * ∫ ξ, G ξ := by
    rw [integral_congr_ae (Eventually.of_forall hpt), Measure.integral_comp_div G (2 * Real.pi),
      smul_eq_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  rw [hL, hR]
  simp only [hG]
  rw [plancherel hg1 hg2, ← mul_assoc, one_div,
    inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_mul]

end RiemannLab
