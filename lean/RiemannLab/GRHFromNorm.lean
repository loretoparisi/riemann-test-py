import RiemannLab.MtBounds
import RiemannLab.Open
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Finite weighted norms of `M_χ` imply GRH for `χ`

This is the "finite norms ⇒ GRH" half of the GRH-equivalent part of the combined equation
(Hardy–Littlewood 1918 for `ζ`, Garg–Maji 2022 for `χ`), proved here with no `sorry`.

Write `C_χ = 1/L(1, χ)` and `M_χ = M̃_χ + C_χ` (see `Open.lean` for why `M_χ` is defined this way).
Assume `∫₀^∞ |M_χ(x)|² x^{1-2α} dx < ∞` for every `α ∈ (3/4, 1)`.

1. On `(1, ∞)`, `x^{σ-1} |M_χ| ≤ |M_χ|² x^{1-2α} + x^{2σ-3+2α}`, so `x^{σ-1} M_χ` is integrable
   on `(1, ∞)` for every `σ < 1/4` (`integrableOn_M_Ioi`). On `(0, 1]`, `|M̃_χ(x)| ≤ Z(1) x`, so
   `x^{σ-1} M̃_χ` is integrable there for `σ > -1` (`integrableOn_Mt_Ioc`).
2. Both pieces are holomorphic in `s` on those half planes (`mellinOn_differentiableAt`, a
   dominated-differentiation argument), so
   `K(s) = s (∫₀¹ x^{s-1} M̃_χ + ∫₁^∞ x^{s-1} M_χ) + C_χ` is holomorphic on `-1 < Re s < 1/4`.
3. For `-1 < Re s < 0`, `K(s) = s 𝓜M̃_χ(s)` and `𝓜M̃_χ(s) = Γ(s)/L(1-2s, χ)` (`mellin_Mt`), so
   `K(s) L(1-2s, χ) = Γ(s+1)` there (`K_mul_LFunction_eq`).
4. The identity theorem extends this to the whole strip `-1 < Re s < 1/4`. Since `Γ(s+1) ≠ 0`
   there, `L(w, χ) ≠ 0` for `1/2 < Re w < 1` (`LFunction_ne_zero_of_finiteNorms`).
5. The functional equation moves zeros with `0 < Re ρ < 1/2` to zeros of `L(·, χ⁻¹)` with real part
   in `(1/2, 1)`, so finite norms for `χ` and for `χ⁻¹` give GRH for `χ` (`grh_of_finiteNorms`).
-/

open Complex MeasureTheory Set Filter Topology DirichletCharacter
open scoped LSeries.notation

noncomputable section

namespace RiemannLab

/-! ### Mellin integrals over a subset of `(0, ∞)` and their holomorphy -/

/-- `|log t| ≤ (t^δ + t^{-δ})/δ` for `t > 0`, `δ > 0`. -/
lemma abs_log_le {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) :
    |Real.log t| ≤ (t ^ δ + t ^ (-δ)) / δ := by
  have h1 := Real.log_le_rpow_div ht.le hδ
  have h2 := Real.neg_rpow_div_le_log ht.le hδ
  have h3 : 0 ≤ t ^ δ / δ := div_nonneg (Real.rpow_nonneg ht.le _) hδ.le
  have h4 : 0 ≤ t ^ (-δ) / δ := div_nonneg (Real.rpow_nonneg ht.le _) hδ.le
  rw [add_div, abs_le]
  constructor <;> linarith [neg_div δ (t ^ (-δ))]

/-- `∫_S t^{s-1} f(t) dt` over a set `S ⊆ (0, ∞)`. -/
def mellinOn (S : Set ℝ) (f : ℝ → ℂ) (s : ℂ) : ℂ := ∫ t in S, (t : ℂ) ^ (s - 1) • f t

/-- **Holomorphy of a Mellin integral.** If `t^{j-1} |f(t)|` is integrable on `S ⊆ (0, ∞)` for
every real `j ∈ [Re s - 2v, Re s + 2v]`, then `s ↦ ∫_S t^{s-1} f(t) dt` is complex
differentiable at `s`. (Mathlib's `mellin_differentiableAt_of_isBigO_rpow` needs `O(x^a)` bounds;
this version only needs integrability, by dominated differentiation.) -/
theorem mellinOn_differentiableAt {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0)
    {f : ℝ → ℂ} (hfm : AEStronglyMeasurable f (volume.restrict S)) {s : ℂ} {v : ℝ} (hv : 0 < v)
    (hint : ∀ j ∈ Icc (s.re - 2 * v) (s.re + 2 * v),
      IntegrableOn (fun t : ℝ => t ^ (j - 1) * ‖f t‖) S) :
    DifferentiableAt ℂ (mellinOn S f) s := by
  set F : ℂ → ℝ → ℂ := fun z t => (t : ℂ) ^ (z - 1) • f t with hF
  set F' : ℂ → ℝ → ℂ := fun z t => ((t : ℂ) ^ (z - 1) * (Real.log t : ℂ)) • f t with hF'
  let bound : ℝ → ℝ := fun t =>
    (t ^ (s.re + v - 1) + t ^ (s.re - v - 1)) * ((t ^ v + t ^ (-v)) / v) * ‖f t‖
  have hcpow : ∀ z : ℂ, ContinuousOn (fun t : ℝ => (t : ℂ) ^ (z - 1)) S := fun z t ht =>
    (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt (hS0 ht)))).continuousWithinAt
  have h1 : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) (volume.restrict S) :=
    Eventually.of_forall fun z => ((hcpow z).aestronglyMeasurable hS).smul hfm
  have h2 : Integrable (F s) (volume.restrict S) := by
    refine Integrable.mono' (hint s.re ⟨by linarith, by linarith⟩) h1.self_of_nhds ?_
    refine (ae_restrict_mem hS).mono fun t ht => le_of_eq ?_
    have ht0 : (0:ℝ) < t := hS0 ht
    simp only [hF, norm_smul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re]
  have h3 : AEStronglyMeasurable (F' s) (volume.restrict S) := by
    refine (((hcpow s).mul ?_).aestronglyMeasurable hS).smul hfm
    exact continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun t ht => ne_of_gt (hS0 ht))
  have hre : ∀ z ∈ Metric.ball s v, |z.re - s.re| < v := fun z hz => by
    have := Complex.abs_re_le_norm (z - s)
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [← sub_re]
    linarith
  have hpow : ∀ z ∈ Metric.ball s v, ∀ t : ℝ, 0 < t →
      t ^ (z.re - 1) ≤ t ^ (s.re + v - 1) + t ^ (s.re - v - 1) := by
    intro z hz t ht
    have h := abs_lt.mp (hre z hz)
    rcases le_or_gt 1 t with h1 | h1
    · exact le_add_of_le_of_nonneg (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))
        (Real.rpow_nonneg ht.le _)
    · exact le_add_of_nonneg_of_le (Real.rpow_nonneg ht.le _)
        (Real.rpow_le_rpow_of_exponent_ge ht h1.le (by linarith))
  have h4 : ∀ᵐ t ∂(volume.restrict S), ∀ z ∈ Metric.ball s v, ‖F' z t‖ ≤ bound t := by
    refine (ae_restrict_mem hS).mono fun t ht z hz => ?_
    have ht0 : 0 < t := hS0 ht
    have hA := hpow z hz t ht0
    have hB := abs_log_le ht0 hv
    have hA0 : 0 ≤ t ^ (s.re + v - 1) + t ^ (s.re - v - 1) :=
      add_nonneg (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg ht0.le _)
    simp only [hF', bound, norm_smul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, sub_re, one_re,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (mul_le_mul hA hB (abs_nonneg _) hA0) (norm_nonneg _)
  have h5 : Integrable bound (volume.restrict S) := by
    have hsum : IntegrableOn (fun t : ℝ => (1 / v) * (t ^ (s.re + 2 * v - 1) * ‖f t‖
        + t ^ (s.re - 1) * ‖f t‖ + t ^ (s.re - 1) * ‖f t‖ + t ^ (s.re - 2 * v - 1) * ‖f t‖)) S :=
      ((((hint (s.re + 2 * v) ⟨by linarith, le_rfl⟩).add
        (hint s.re ⟨by linarith, by linarith⟩)).add
        (hint s.re ⟨by linarith, by linarith⟩)).add
        (hint (s.re - 2 * v) ⟨le_rfl, by linarith⟩)).const_mul _
    refine Integrable.congr hsum ((ae_restrict_mem hS).mono fun t ht => ?_)
    have ht0 : 0 < t := hS0 ht
    have e1 : t ^ (s.re + v - 1) * t ^ v = t ^ (s.re + 2 * v - 1) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    have e2 : t ^ (s.re + v - 1) * t ^ (-v) = t ^ (s.re - 1) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    have e3 : t ^ (s.re - v - 1) * t ^ v = t ^ (s.re - 1) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    have e4 : t ^ (s.re - v - 1) * t ^ (-v) = t ^ (s.re - 2 * v - 1) := by
      rw [← Real.rpow_add ht0]; congr 1; ring
    simp only [bound]
    linear_combination (-(‖f t‖ / v)) * e1 + (-(‖f t‖ / v)) * e2 + (-(‖f t‖ / v)) * e3
      + (-(‖f t‖ / v)) * e4
  have h6 : ∀ᵐ t ∂(volume.restrict S), ∀ y ∈ Metric.ball s v,
      HasDerivAt (fun z : ℂ => F z t) (F' y t) y := by
    refine (ae_restrict_mem hS).mono fun t ht y _ => ?_
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (hS0 ht))
    have u1 : HasDerivAt (fun z : ℂ => (t : ℂ) ^ (z - 1))
        ((t : ℂ) ^ (y - 1) * (Real.log t : ℂ)) y := by
      convert ((hasDerivAt_id' y).sub_const 1).const_cpow (Or.inl ht') using 1
      rw [ofReal_log (le_of_lt (hS0 ht))]
      ring
    exact u1.smul_const (f t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds _ hv)
    h1 h2 h3 h4 h5 h6).2.differentiableAt

/-! ### Integrability of the two pieces -/

lemma continuousOn_M {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ContinuousOn (M χ) (Ioi 0) := by
  unfold M
  exact (continuousOn_Mt χ).add continuousOn_const

/-- `x^{σ-1} M̃_χ` is integrable on `(0, 1]` for `σ > -1`. -/
lemma integrableOn_Mt_Ioc {N : ℕ} (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : -1 < σ) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖Mt χ t‖) (Ioc 0 1) := by
  have hint : IntegrableOn (fun t : ℝ => Z 1 * t ^ (σ - 1 + 1)) (Ioc 0 1) :=
    Integrable.const_mul ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))) _
  have hc : ContinuousOn (fun t : ℝ => t ^ (σ - 1) * ‖Mt χ t‖) (Ioi 0) :=
    (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx)).mul (continuousOn_Mt χ).norm
  refine Integrable.mono' hint
    ((hc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (norm_nonneg _))]
  exact rpow_mul_bound ht.1 (Z_nonneg _) (norm_Mt_le χ ht.1 one_pos le_rfl)

/-- `t^{p+q} m ≤ m² t^{2p} + t^{2q}`. -/
lemma amgm_rpow {t m p q : ℝ} (ht : 0 < t) (hm : 0 ≤ m) :
    t ^ (p + q) * m ≤ m ^ 2 * t ^ (2 * p) + t ^ (2 * q) := by
  have e1 : t ^ (p + q) = t ^ p * t ^ q := Real.rpow_add ht p q
  have e2 : t ^ (2 * p) = t ^ p * t ^ p := by rw [two_mul, Real.rpow_add ht]
  have e3 : t ^ (2 * q) = t ^ q * t ^ q := by rw [two_mul, Real.rpow_add ht]
  rw [e1, e2, e3]
  have hp := Real.rpow_nonneg ht.le p
  have hq := Real.rpow_nonneg ht.le q
  nlinarith [sq_nonneg (m * t ^ p - t ^ q), mul_nonneg (mul_nonneg hm hp) hq]

/-- The hypothesis: `∫₀^∞ |M_χ(x)|² x^{1-2α} dx < ∞` for every `α ∈ (3/4, 1)`. -/
def FiniteNorms {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ α ∈ Ioo (3 / 4 : ℝ) 1,
    IntegrableOn (fun x : ℝ => ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α)) (Ioi 0)

/-- Finite norms give integrability of `x^{σ-1} M_χ` on `(1, ∞)` for every `σ < 1/4`. -/
lemma integrableOn_M_Ioi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hfin : FiniteNorms χ)
    {σ : ℝ} (hσ : σ < 1 / 4) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖M χ t‖) (Ioi 1) := by
  set mm := min 1 (1 - σ) with hmm
  have hm1 : mm ≤ 1 := min_le_left _ _
  have hm2 : mm ≤ 1 - σ := min_le_right _ _
  have hm3 : 3 / 4 < mm := lt_min (by norm_num) (by linarith)
  set α := (3 / 4 + mm) / 2 with hα
  have hα1 : 3 / 4 < α := by linarith
  have hα2 : α < 1 := by linarith
  have hα3 : σ + α < 1 := by linarith
  have hA := (hfin α ⟨hα1, hα2⟩).mono_set (Ioi_subset_Ioi zero_le_one)
  have hB : IntegrableOn (fun t : ℝ => t ^ (2 * (σ - 1 - (1 - 2 * α) / 2))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hc : ContinuousOn (fun t : ℝ => t ^ (σ - 1) * ‖M χ t‖) (Ioi 1) :=
    (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (zero_lt_one.trans hx))).mul
      ((continuousOn_M χ).norm.mono (Ioi_subset_Ioi zero_le_one))
  refine Integrable.mono' (hA.add hB) (hc.aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  have ht0 : (0:ℝ) < t := zero_lt_one.trans ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (norm_nonneg _))]
  have h := amgm_rpow (m := ‖M χ t‖) (p := (1 - 2 * α) / 2) (q := σ - 1 - (1 - 2 * α) / 2) ht0
    (norm_nonneg _)
  rw [show (1 - 2 * α) / 2 + (σ - 1 - (1 - 2 * α) / 2) = σ - 1 by ring,
    show 2 * ((1 - 2 * α) / 2) = 1 - 2 * α by ring] at h
  simpa only [Pi.add_apply] using h

/-! ### The continuation `K` and the identity `K(s) L(1-2s, χ) = Γ(s+1)` -/

variable {N : ℕ} [NeZero N]

/-- `C_χ = 1/L(1, χ)`. -/
def Cχ (χ : DirichletCharacter ℂ N) : ℂ := 1 / LFunction χ 1

/-- `I₀(s) = ∫₀¹ x^{s-1} M̃_χ(x) dx`, holomorphic on `Re s > -1`. -/
def I0 (χ : DirichletCharacter ℂ N) : ℂ → ℂ := mellinOn (Ioc 0 1) (Mt χ)

/-- `I₁(s) = ∫₁^∞ x^{s-1} M_χ(x) dx`, holomorphic on `Re s < 1/4` under `FiniteNorms χ`. -/
def I1 (χ : DirichletCharacter ℂ N) : ℂ → ℂ := mellinOn (Ioi 1) (M χ)

/-- `K(s) = s (I₀(s) + I₁(s)) + C_χ`. -/
def K (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := s * (I0 χ s + I1 χ s) + Cχ χ

lemma differentiableAt_I0 (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ (I0 χ) s := by
  unfold I0
  refine mellinOn_differentiableAt measurableSet_Ioc (fun t ht => ht.1)
    (((continuousOn_Mt χ).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
    (v := (s.re + 1) / 4) (by linarith) ?_
  intro j hj
  exact integrableOn_Mt_Ioc χ (by linarith [hj.1])

lemma differentiableAt_I1 (χ : DirichletCharacter ℂ N) (hfin : FiniteNorms χ) {s : ℂ}
    (hs : s.re < 1 / 4) : DifferentiableAt ℂ (I1 χ) s := by
  unfold I1
  refine mellinOn_differentiableAt measurableSet_Ioi
    (fun t ht => (zero_lt_one.trans ht : (0:ℝ) < t))
    (((continuousOn_M χ).mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi)
    (v := (1 / 4 - s.re) / 4) (by linarith) ?_
  intro j hj
  exact integrableOn_M_Ioi χ hfin (by linarith [hj.2])

lemma differentiableAt_K (χ : DirichletCharacter ℂ N) (hfin : FiniteNorms χ) {s : ℂ}
    (h1 : -1 < s.re) (h2 : s.re < 1 / 4) : DifferentiableAt ℂ (K χ) s := by
  have h := ((differentiableAt_id (x := s)).mul ((differentiableAt_I0 χ h1).add
    (differentiableAt_I1 χ hfin h2))).add_const (Cχ χ)
  exact h

/-- For `-1 < Re s < 0`: `𝓜M̃_χ(s) = I₀(s) + I₁(s) + C_χ / s`. -/
lemma mellin_Mt_split (χ : DirichletCharacter ℂ N) (hfin : FiniteNorms χ) {s : ℂ}
    (h1 : -1 < s.re) (h0 : s.re < 0) :
    mellin (Mt χ) s = I0 χ s + I1 χ s + Cχ χ / s := by
  have hmeas : AEStronglyMeasurable (Mt χ) (volume.restrict (Ioi 0)) :=
    (continuousOn_Mt χ).aestronglyMeasurable measurableSet_Ioi
  have hmeasM : AEStronglyMeasurable (M χ) (volume.restrict (Ioi 0)) :=
    (continuousOn_M χ).aestronglyMeasurable measurableSet_Ioi
  have hconv : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • Mt χ t) (Ioi 0) := by
    have h := mellinConvergent_Mt χ h1 h0
    unfold MellinConvergent at h
    rw [mellin_convergent_iff_norm le_rfl measurableSet_Ioi hmeas] at h ⊢
    simpa only [ofReal_re] using h
  have hint1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • M χ t) (Ioi 1) :=
    (mellin_convergent_iff_norm (Ioi_subset_Ioi zero_le_one) measurableSet_Ioi hmeasM).mpr
      (integrableOn_M_Ioi χ hfin (by linarith))
  have hint2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hMt : ∀ t, Mt χ t = M χ t - Cχ χ := fun t => by simp [M, Cχ]
  have hsplit : ∫ t in Ioi (1:ℝ), (t : ℂ) ^ (s - 1) • Mt χ t
      = (∫ t in Ioi (1:ℝ), (t : ℂ) ^ (s - 1) • M χ t) + Cχ χ / s := by
    calc ∫ t in Ioi (1:ℝ), (t : ℂ) ^ (s - 1) • Mt χ t
        = ∫ t in Ioi (1:ℝ), ((t : ℂ) ^ (s - 1) • M χ t - Cχ χ * (t : ℂ) ^ (s - 1)) := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
          simp only [hMt, smul_eq_mul]
          ring
      _ = (∫ t in Ioi (1:ℝ), (t : ℂ) ^ (s - 1) • M χ t)
            - Cχ χ * ∫ t in Ioi (1:ℝ), (t : ℂ) ^ (s - 1) := by
          rw [integral_sub hint1 (hint2.const_mul (Cχ χ)), integral_const_mul]
      _ = (∫ t in Ioi (1:ℝ), (t : ℂ) ^ (s - 1) • M χ t) + Cχ χ / s := by
          rw [integral_Ioi_cpow_of_lt (a := s - 1) (by simp; linarith) zero_lt_one]
          simp only [ofReal_one, one_cpow, sub_add_cancel]
          ring
  simp only [I0, I1, mellinOn]
  rw [mellin, ← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hconv.mono_set Ioc_subset_Ioi_self) (hconv.mono_set (Ioi_subset_Ioi zero_le_one)),
    hsplit, add_assoc]

/-- For `-1 < Re s < 0`: `K(s) L(1-2s, χ) = Γ(s+1)`. -/
lemma K_mul_LFunction_eq (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hfin : FiniteNorms χ)
    {s : ℂ} (h1 : -1 < s.re) (h0 : s.re < 0) :
    K χ s * LFunction χ (1 - 2 * s) = Gamma (s + 1) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, zero_re] at h0
    exact lt_irrefl _ h0
  have hre : 1 < (1 - 2 * s).re := by simp; linarith
  have hL : LFunction χ (1 - 2 * s) = LSeries ↗χ (1 - 2 * s) := LFunction_eq_LSeries χ hre
  have hL0 : LFunction χ (1 - 2 * s) ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hre.le
  have hK : K χ s = s * mellin (Mt χ) s := by
    rw [mellin_Mt_split χ hfin h1 h0, K, mul_add s (I0 χ s + I1 χ s), mul_div_cancel₀ _ hs0]
  rw [hK, mellin_Mt χ h1 h0, ← hL, Gamma_add_one s hs0, mul_assoc, div_mul_cancel₀ _ hL0]

/-- **No zeros in `1/2 < Re w < 1`** if the weighted norms of `M_χ` are finite. -/
theorem LFunction_ne_zero_of_finiteNorms (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hfin : FiniteNorms χ) {w : ℂ} (hw1 : 1 / 2 < w.re) (hw2 : w.re < 1) :
    LFunction χ w ≠ 0 := by
  set U : Set ℂ := {s | -1 < s.re} ∩ {s | s.re < 1 / 4} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt (r := -1)).inter (convex_halfSpace_re_lt (r := 1 / 4))).isPreconnected
  have hGamma : ∀ s ∈ U, DifferentiableAt ℂ (fun s : ℂ => Gamma (s + 1)) s := by
    intro s hs
    refine (differentiableAt_Gamma (s + 1) fun m h => ?_).comp s (differentiableAt_id.add_const 1)
    have := congrArg re h
    simp only [add_re, one_re, neg_re, natCast_re] at this
    linarith [hs.1, (Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hLd : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ
  have hf : AnalyticOnNhd ℂ (fun s : ℂ => K χ s * LFunction χ (1 - 2 * s)) U := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUo
    refine ((differentiableAt_K χ hfin hs.1 hs.2).mul ?_).differentiableWithinAt
    exact hLd.differentiableAt.comp s
      ((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id))
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => Gamma (s + 1)) U :=
    DifferentiableOn.analyticOnNhd (fun s hs => (hGamma s hs).differentiableWithinAt) hUo
  set V : Set ℂ := {s | -1 < s.re} ∩ {s | s.re < 0} with hV
  have hVo : IsOpen V :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hz0V : (-1 / 2 : ℂ) ∈ V := by
    constructor
    · show (-1 : ℝ) < (-1 / 2 : ℂ).re
      norm_num
    · show (-1 / 2 : ℂ).re < 0
      norm_num
  have hz0U : (-1 / 2 : ℂ) ∈ U := ⟨hz0V.1, lt_trans hz0V.2 (by norm_num)⟩
  have hfg : (fun s : ℂ => K χ s * LFunction χ (1 - 2 * s)) =ᶠ[𝓝 (-1 / 2 : ℂ)]
      (fun s : ℂ => Gamma (s + 1)) :=
    Filter.eventuallyEq_of_mem (hVo.mem_nhds hz0V)
      (fun s hs => K_mul_LFunction_eq χ hχ hfin hs.1 hs.2)
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hz0U hfg
  set s : ℂ := (1 - w) / 2 with hs
  have hsre : s.re = (1 - w.re) / 2 := by
    rw [hs, div_ofNat_re, sub_re, one_re]
  have hsU : s ∈ U := ⟨by show -1 < s.re; rw [hsre]; linarith,
    by show s.re < 1 / 4; rw [hsre]; linarith⟩
  have h := heq hsU
  have hw : 1 - 2 * s = w := by rw [hs]; ring
  simp only [hw] at h
  intro hL
  rw [hL, mul_zero] at h
  exact Gamma_ne_zero_of_re_pos (by rw [add_re, one_re, hsre]; linarith) h.symm

/-! ### GRH from finite norms for `χ` and `χ⁻¹` -/

lemma gammaFactor_ne_zero_of_re_pos (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [ho.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)

lemma completedLFunction_eq_zero (χ : DirichletCharacter ℂ N) {ρ : ℂ} (h0 : 0 < ρ.re)
    (hρ : LFunction χ ρ = 0) : completedLFunction χ ρ = 0 := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h, zero_re] at h0
    exact lt_irrefl _ h0
  rw [LFunction_eq_completed_div_gammaFactor χ ρ (Or.inl hρ0), div_eq_zero_iff] at hρ
  rcases hρ with h | h
  · exact h
  · exact absurd h (gammaFactor_ne_zero_of_re_pos χ h0)

/-- **Finite norms ⇒ GRH.** For a primitive nontrivial `χ`, if the weighted norms
`∫₀^∞ |M(x)|² x^{1-2α} dx` are finite for every `α ∈ (3/4, 1)`, both for `χ` and for `χ⁻¹`
(they are equal: `M_{χ̄} = conj M_χ`; that identity is not formalized here), then GRH holds
for `χ`. -/
theorem grh_of_finiteNorms (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hfin : FiniteNorms χ) (hfin' : FiniteNorms χ⁻¹) : GRH χ := by
  intro ρ h0 h1 hρ
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `0 < Re ρ < 1/2`: the functional equation gives a zero of `L(·, χ⁻¹)` at `1 - ρ`.
    have hΛ := completedLFunction_eq_zero χ h0 hρ
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
    exact LFunction_ne_zero_of_finiteNorms χ⁻¹ (inv_ne_one.mpr hχ) hfin' hre1 hre2 hL'
  · exact LFunction_ne_zero_of_finiteNorms χ hχ hfin hgt h1 hρ

end RiemannLab
