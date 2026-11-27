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

/-! ### The Mellin transform of `f = M̃_χ − C_χ g` -/

variable {N : ℕ} [NeZero N]

/-- `φ(s) = 1/L(1 - 2s, χ)`. -/
def phi (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := (LFunction χ (1 - 2 * s))⁻¹

/-- `H(s) = Γ(s+1) (φ(s) - φ(0)) / s`, written with `dslope` so that it is holomorphic at `0`. -/
def H (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := Gamma (s + 1) * dslope (phi χ) 0 s

/-- `f = M̃_χ − C_χ g`. -/
def fM (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ := Mt χ x - Cχ χ * g x

lemma phi_zero (χ : DirichletCharacter ℂ N) : phi χ 0 = Cχ χ := by
  simp [phi, Cχ]

lemma differentiableAt_phi (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hGRH : GRH χ) {s : ℂ}
    (hs : s.re < 1 / 4) : DifferentiableAt ℂ (phi χ) s := by
  have hre : 1 / 2 < (1 - 2 * s).re := by simp; linarith
  refine DifferentiableAt.inv ?_ (LFunction_ne_zero_of_GRH χ hχ hGRH hre)
  exact (differentiable_LFunction hχ).differentiableAt.comp s
    ((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id))

/-- The strip `-1 < Re s < 1/4`. -/
def stripU : Set ℂ := {s | -1 < s.re} ∩ {s | s.re < 1 / 4}

lemma isOpen_stripU : IsOpen stripU :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)

lemma differentiableOn_H (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hGRH : GRH χ) :
    DifferentiableOn ℂ (H χ) stripU := by
  have h0 : (0:ℂ) ∈ stripU := ⟨by simp, by simp⟩
  have hphi : DifferentiableOn ℂ (phi χ) stripU := fun s hs =>
    (differentiableAt_phi χ hχ hGRH hs.2).differentiableWithinAt
  have hd := (differentiableOn_dslope (isOpen_stripU.mem_nhds h0)).mpr hphi
  refine DifferentiableOn.mul (fun s hs => ?_) hd
  refine ((differentiableAt_Gamma (s + 1) fun m h => ?_).comp s
    (differentiableAt_id.add_const 1)).differentiableWithinAt
  have h1 : -1 < s.re := hs.1
  have := congrArg re h
  simp only [add_re, one_re, neg_re, natCast_re] at this
  linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]

omit [NeZero N] in
lemma mellinConvergent_Mt' (χ : DirichletCharacter ℂ N) {s : ℂ} (h1 : -1 < s.re)
    (h0 : s.re < 0) : MellinConvergent (Mt χ) s := by
  have hmeas : AEStronglyMeasurable (Mt χ) (volume.restrict (Ioi 0)) :=
    (continuousOn_Mt χ).aestronglyMeasurable measurableSet_Ioi
  have h := mellinConvergent_Mt χ h1 h0
  unfold MellinConvergent at h ⊢
  rw [mellin_convergent_iff_norm le_rfl measurableSet_Ioi hmeas] at h ⊢
  simpa only [ofReal_re] using h

lemma mellinConvergent_fM (χ : DirichletCharacter ℂ N) {s : ℂ} (h1 : -1 < s.re)
    (h0 : s.re < 0) : MellinConvergent (fM χ) s := by
  have h := (mellinConvergent_Mt' χ h1 h0).sub ((mellinConvergent_g h1 h0).const_smul (Cχ χ))
  unfold MellinConvergent at h ⊢
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [fM, smul_eq_mul, Pi.sub_apply]
  ring

/-- **Mellin transform of `f`.** `𝓜f(s) = H(s)` for `-1 < Re s < 0`. -/
lemma mellin_fM (χ : DirichletCharacter ℂ N) {s : ℂ} (h1 : -1 < s.re) (h0 : s.re < 0) :
    mellin (fM χ) s = H χ s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at h0; exact lt_irrefl _ h0
  have hre : 1 < (1 - 2 * s).re := by simp; linarith
  have hsplit : mellin (fM χ) s = mellin (Mt χ) s - Cχ χ * mellin g s := by
    have hA := mellinConvergent_Mt' χ h1 h0
    have hB := (mellinConvergent_g h1 h0).const_smul (Cχ χ)
    unfold MellinConvergent at hA hB
    have e : ∫ t in Ioi (0:ℝ), (t : ℂ) ^ (s - 1) • fM χ t
        = ∫ t in Ioi (0:ℝ), ((t : ℂ) ^ (s - 1) • Mt χ t
          - (t : ℂ) ^ (s - 1) • (fun t => Cχ χ • g t) t) :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ => by
        simp only [fM, smul_eq_mul]; ring
    rw [mellin, mellin, mellin, e, integral_sub hA hB, ← integral_const_mul]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul]
    ring
  rw [hsplit, mellin_Mt χ h1 h0, mellin_g h1 h0, H, dslope_of_ne _ hs0, slope_def_field,
    phi_zero, Gamma_add_one s hs0, phi, LFunction_eq_LSeries χ hre, sub_zero]
  field_simp

/-! ### `H` decays like `(1 + Im² s)⁻¹` on the strip `-1/2 ≤ Re s ≤ c'` -/

lemma decay_arith {a G C P K g1 p : ℝ} {m : ℕ} (ha : 1 ≤ a) (hK0 : 0 ≤ K) (hK : K ≤ m)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hg1 : 0 ≤ g1)
    (hΓ : g1 * a ^ (m + 1) ≤ G) (hφ : p ≤ C * (2 * a + 8) ^ K) :
    g1 * ((p + P) / a) ≤ 2 * G * (C * 10 ^ K + P) * (1 + a ^ 2)⁻¹ := by
  have ha0 : 0 < a := by linarith
  set u : ℝ := a ^ m with hu
  have hu1 : 1 ≤ u := one_le_pow₀ ha
  have h1 : (2 * a + 8) ^ K ≤ 10 ^ K * u := by
    calc (2 * a + 8) ^ K ≤ (10 * a) ^ K := Real.rpow_le_rpow (by linarith) (by linarith) hK0
      _ = 10 ^ K * a ^ K := Real.mul_rpow (by norm_num) ha0.le
      _ ≤ 10 ^ K * a ^ (m : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ha hK) (by positivity)
      _ = 10 ^ K * u := by rw [Real.rpow_natCast]
  set Q : ℝ := C * 10 ^ K + P with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hpP : p + P ≤ Q * u := by
    have : C * (2 * a + 8) ^ K ≤ C * (10 ^ K * u) := mul_le_mul_of_nonneg_left h1 hC
    nlinarith
  have hgua : g1 * u * a ≤ G := by
    calc g1 * u * a = g1 * a ^ (m + 1) := by rw [hu, pow_succ]; ring
      _ ≤ G := hΓ
  have hden : 0 < 1 + a ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hden, mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ ha0]
  have hpP' : g1 * (p + P) ≤ g1 * (Q * u) := mul_le_mul_of_nonneg_left hpP hg1
  have h2 : 1 + a ^ 2 ≤ 2 * a ^ 2 := by nlinarith
  have hg1Q : 0 ≤ g1 * Q * u := by positivity
  calc g1 * (p + P) * (1 + a ^ 2) ≤ g1 * (Q * u) * (2 * a ^ 2) :=
        mul_le_mul hpP' h2 hden.le (by positivity)
    _ = 2 * Q * a * (g1 * u * a) := by ring
    _ ≤ 2 * Q * a * G := by gcongr
    _ = 2 * G * Q * a := by ring

theorem norm_H_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hGRH : GRH χ) {c' : ℝ}
    (hc'0 : 0 < c') (hc' : c' < 1 / 4) :
    ∃ E : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ c' → ‖H χ s‖ ≤ E * (1 + s.im ^ 2)⁻¹ := by
  obtain ⟨C, K, hC, hK, hbd⟩ := norm_inv_LFunction_le χ hχ hGRH (d := 1 / 2 - 2 * c')
    (by linarith) (by linarith)
  set m : ℕ := ⌈K⌉₊ with hm
  have hKm : K ≤ m := Nat.le_ceil K
  -- a bound for `Γ` on the compact interval of real parts
  obtain ⟨G0, hG0⟩ := (isCompact_Icc (a := 1 / 2 + ((m + 1 : ℕ) : ℝ))
    (b := c' + 1 + ((m + 1 : ℕ) : ℝ))).exists_bound_of_continuousOn (f := Real.Gamma)
    (fun x hx => (Real.differentiableAt_Gamma fun k h => by
      have := hx.1
      have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      rw [h] at this
      have : (0:ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith).continuousAt.continuousWithinAt)
  -- a bound for `H` on the compact part `|Im s| ≤ 1`
  have hKc : IsCompact (Icc (-1 / 2 : ℝ) c' ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hKsub : Icc (-1 / 2 : ℝ) c' ×ℂ Icc (-1 : ℝ) 1 ⊆ stripU := fun s hs => by
    rw [mem_reProdIm] at hs
    exact ⟨show -1 < s.re by linarith [hs.1.1], show s.re < 1 / 4 by linarith [hs.1.2]⟩
  obtain ⟨B0, hB0⟩ := hKc.exists_bound_of_continuousOn
    ((differentiableOn_H χ hχ hGRH).continuousOn.mono hKsub)
  set P : ℝ := ‖phi χ 0‖ with hP
  refine ⟨2 * max B0 0 + 2 * G0 * (C * 10 ^ K + P), fun s hs1 hs2 => ?_⟩
  have hden : 0 < 1 + s.im ^ 2 := by positivity
  have hG0nn : 0 ≤ G0 := (norm_nonneg _).trans (hG0 (1 / 2 + ((m + 1 : ℕ) : ℝ))
    ⟨le_rfl, by linarith⟩)
  have hQ : 0 ≤ 2 * G0 * (C * 10 ^ K + P) := by positivity
  rcases le_or_gt |s.im| 1 with hsmall | hbig
  · have hmem : s ∈ Icc (-1 / 2 : ℝ) c' ×ℂ Icc (-1 : ℝ) 1 := by
      rw [mem_reProdIm]
      exact ⟨⟨hs1, hs2⟩, abs_le.mp hsmall⟩
    have h1 : ‖H χ s‖ ≤ max B0 0 := (hB0 s hmem).trans (le_max_left _ _)
    have h2 : s.im ^ 2 ≤ 1 := by nlinarith [abs_nonneg s.im, sq_abs s.im]
    have h3 : max B0 0 ≤ 2 * max B0 0 * (1 + s.im ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hden]
      nlinarith [le_max_right B0 0]
    calc ‖H χ s‖ ≤ 2 * max B0 0 * (1 + s.im ^ 2)⁻¹ := h1.trans h3
      _ ≤ _ := by
        rw [add_mul]
        exact le_add_of_nonneg_right (mul_nonneg hQ (inv_nonneg.mpr hden.le))
  · have hs0 : s ≠ 0 := fun h => by rw [h, zero_im, abs_zero] at hbig; linarith
    have hΓ : ‖Gamma (s + 1)‖ * |s.im| ^ (m + 1) ≤ G0 := by
      have h := norm_Gamma_mul_pow_le (m + 1) (s + 1) (by rw [add_re, one_re]; linarith)
      rw [add_im, one_im, add_zero, add_re, one_re] at h
      refine h.trans ((le_abs_self _).trans ?_)
      exact hG0 _ ⟨by push_cast; linarith, by push_cast; linarith⟩
    have hre1 : 1 / 2 + (1 / 2 - 2 * c') ≤ (1 - 2 * s).re := by simp; linarith
    have hre2 : (1 - 2 * s).re ≤ 3 := by simp; linarith
    have hφ : ‖phi χ s‖ ≤ C * (2 * |s.im| + 8) ^ K := by
      have h := hbd (1 - 2 * s) hre1 hre2
      have him : |(1 - 2 * s).im| = 2 * |s.im| := by simp [abs_mul]
      rw [him] at h
      exact h
    have hds : ‖dslope (phi χ) 0 s‖ ≤ (‖phi χ s‖ + P) / |s.im| := by
      rw [dslope_of_ne _ hs0, slope_def_field, sub_zero, norm_div]
      exact div_le_div₀ (by positivity) (norm_sub_le _ _) (by linarith) (abs_im_le_norm s)
    have hmain := decay_arith (a := |s.im|) (P := P) (g1 := ‖Gamma (s + 1)‖) hbig.le hK hKm hC
      (norm_nonneg (phi χ 0)) (norm_nonneg (Gamma (s + 1))) hΓ hφ
    rw [sq_abs] at hmain
    calc ‖H χ s‖ = ‖Gamma (s + 1)‖ * ‖dslope (phi χ) 0 s‖ := norm_mul _ _
      _ ≤ ‖Gamma (s + 1)‖ * ((‖phi χ s‖ + P) / |s.im|) :=
          mul_le_mul_of_nonneg_left hds (norm_nonneg _)
      _ ≤ 2 * G0 * (C * 10 ^ K + P) * (1 + s.im ^ 2)⁻¹ := hmain
      _ ≤ _ := by
        rw [add_mul]
        exact le_add_of_nonneg_left (mul_nonneg (by positivity) (inv_nonneg.mpr hden.le))

/-! ### Mellin inversion and the contour shift -/

lemma rpow_le_of_mem {x σ a b : ℝ} (hx : 0 < x) (h1 : a ≤ σ) (h2 : σ ≤ b) :
    x ^ (-σ) ≤ x ^ (-a) + x ^ (-b) := by
  rcases le_or_gt 1 x with hx1 | hx1
  · exact le_add_of_le_of_nonneg (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
      (Real.rpow_nonneg hx.le _)
  · exact le_add_of_nonneg_of_le (Real.rpow_nonneg hx.le _)
      (Real.rpow_le_rpow_of_exponent_ge hx hx1.le (by linarith))

/-- **Shifted Mellin inversion.** Under GRH, for `0 < c' < 1/4` and `x > 0`,
`f(x) = (1/2π) ∫ x^{-(c'+iy)} H(c'+iy) dy`. -/
theorem fM_eq_mellinInv (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hGRH : GRH χ) {c' : ℝ}
    (hc'0 : 0 < c') (hc' : c' < 1 / 4) {x : ℝ} (hx : 0 < x) :
    fM χ x = (1 / (2 * Real.pi)) • ∫ y : ℝ, (x : ℂ) ^ (-((c' : ℂ) + y * I)) • H χ (c' + y * I) := by
  obtain ⟨E, hE⟩ := norm_H_le χ hχ hGRH hc'0 hc'
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -1 / 2 := ⟨_, rfl⟩
  have hE' : ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ‖H χ s‖ ≤ E * (1 + s.im ^ 2)⁻¹ := by
    rw [hc]; exact hE
  clear hE
  have hS : {s : ℂ | c ≤ s.re ∧ s.re ≤ c'} ⊆ stripU := fun s hs =>
    ⟨show -1 < s.re by linarith [hs.1, hc], show s.re < 1 / 4 by linarith [hs.2]⟩
  have hHd : DifferentiableOn ℂ (H χ) {s : ℂ | c ≤ s.re ∧ s.re ≤ c'} :=
    (differentiableOn_H χ hχ hGRH).mono hS
  have hHb : ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ‖H χ s‖ ≤ E * (1 + s.im ^ 2)⁻¹ := hE'
  have hcc : c ≤ c' := by rw [hc]; linarith
  -- Mellin inversion on `Re s = c`
  have hmel : ∀ y : ℝ, mellin (fM χ) (c + y * I) = H χ (c + y * I) := fun y =>
    mellin_fM χ (by simp [hc]; norm_num) (by simp [hc]; norm_num)
  have hvert : VerticalIntegrable (mellin (fM χ)) c := by
    have := integrable_vertical hHd hHb ⟨le_rfl, hcc⟩
    refine this.congr (Eventually.of_forall fun y => ?_)
    exact (hmel y).symm
  have hcont : ContinuousAt (fM χ) x := by
    have h1 : ContinuousAt (Mt χ) x := (continuousOn_Mt χ).continuousAt (Ioi_mem_nhds hx)
    exact h1.sub (continuous_const.mul continuous_g).continuousAt
  have hinv := mellinInv_mellin_eq c (fM χ) hx
    (mellinConvergent_fM χ (by simp [hc]; norm_num) (by simp [hc]; norm_num)) hvert hcont
  rw [← hinv, mellinInv]
  refine congrArg (fun z : ℂ => (1 / (2 * Real.pi)) • z) ?_
  have hcongr : (fun y : ℝ => (x : ℂ) ^ (-((c : ℂ) + y * I)) • mellin (fM χ) (c + y * I))
      = fun y : ℝ => (x : ℂ) ^ (-((c : ℂ) + y * I)) • H χ (c + y * I) := by
    funext y; rw [hmel y]
  rw [hcongr]
  -- the contour shift from `Re s = c` to `Re s = c'`
  set X : ℝ := x ^ (-c) + x ^ (-c') with hX
  have hX0 : 0 ≤ X := by positivity
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  refine integral_vertical_eq (Φ := fun s => (x : ℂ) ^ (-s) • H χ s) (E := X * E) hcc ?_ ?_
  · intro s hs
    exact ((differentiableAt_id.neg.const_cpow (Or.inl hx')).differentiableWithinAt).mul
      (hHd s hs)
  · intro s h1 h2
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hx, neg_re, mul_assoc]
    exact mul_le_mul (rpow_le_of_mem hx h1 h2) (hHb s h1 h2) (norm_nonneg _) hX0

/-! ### GRH ⇒ finite norms -/

/-- **GRH ⇒ finite norms.** If GRH holds for a nontrivial `χ`, then
`∫₀^∞ |M_χ(x)|² x^{1-2α} dx < ∞` for every `α ∈ (3/4, 1)`. -/
theorem finiteNorms_of_GRH (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hGRH : GRH χ) :
    FiniteNorms χ := by
  intro α hα
  set c' : ℝ := 1 - α with hc'
  have hc'0 : 0 < c' := by linarith [hα.2]
  have hc'1 : c' < 1 / 4 := by linarith [hα.1]
  obtain ⟨E, hE⟩ := norm_H_le χ hχ hGRH hc'0 hc'1
  have hS : {s : ℂ | -1 / 2 ≤ s.re ∧ s.re ≤ c'} ⊆ stripU := fun s hs =>
    ⟨show -1 < s.re by linarith [hs.1], show s.re < 1 / 4 by linarith [hs.2]⟩
  have hHd : DifferentiableOn ℂ (H χ) {s : ℂ | -1 / 2 ≤ s.re ∧ s.re ≤ c'} :=
    (differentiableOn_H χ hχ hGRH).mono hS
  have hmem : c' ∈ Icc (-1 / 2 : ℝ) c' := ⟨by linarith, le_rfl⟩
  set h : ℝ → ℂ := fun y => H χ (c' + y * I) with hh
  have hi : Integrable h := integrable_vertical hHd (fun s h1 h2 => hE s h1 h2) hmem
  have hcont : Continuous h := continuous_vertical hHd hmem
  have hbd : ∀ y : ℝ, ‖h y‖ ≤ E * (1 + y ^ 2)⁻¹ := fun y => by
    have := hE (c' + y * I) (by simp; linarith) (by simp)
    simpa [hh] using this
  have h2 : MemLp h 2 := by
    rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
    refine (integrable_inv_one_add_sq.const_mul (E ^ 2)).mono'
      (hcont.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    have hu0 : 0 ≤ (1 + y ^ 2)⁻¹ := by positivity
    have hu1 : (1 + y ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖h y‖ ^ 2 ≤ (E * (1 + y ^ 2)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hbd y) 2
      _ = E ^ 2 * ((1 + y ^ 2)⁻¹ * (1 + y ^ 2)⁻¹) := by ring
      _ ≤ E ^ 2 * (1 * (1 + y ^ 2)⁻¹) := by gcongr
      _ = E ^ 2 * (1 + y ^ 2)⁻¹ := by ring
  have hw := integrableOn_weighted_of_mellinInv hi h2 (c := c') (f := fM χ)
    (fun x hx => fM_eq_mellinInv χ hχ hGRH hc'0 hc'1 hx)
  -- `M_χ = f + C_χ e^{-x}`
  have hexp : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((2 - 2 * α) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by linarith [hα.2])
  have hsum : IntegrableOn (fun x : ℝ => 2 * (‖fM χ x‖ ^ 2 * x ^ (2 * c' - 1))
      + 2 * ‖Cχ χ‖ ^ 2 * (Real.exp (-x) * x ^ ((2 - 2 * α) - 1))) (Ioi 0) :=
    (hw.const_mul 2).add (hexp.const_mul _)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α))
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ((continuousOn_M χ).norm.pow 2).mul
      (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (show (0:ℝ) < x from hx)))
  refine hsum.mono' hmeas ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_)
  have hx0 : (0:ℝ) < x := hx
  have hMx : M χ x = fM χ x + Cχ χ * (Real.exp (-x) : ℂ) := by
    simp only [M, fM, Cχ, g]
    push_cast
    ring
  have hpow : x ^ (2 * c' - 1) = x ^ (1 - 2 * α) := by rw [hc']; congr 1; ring
  have hpow' : x ^ ((2 - 2 * α) - 1) = x ^ (1 - 2 * α) := by congr 1; ring
  have hp0 : 0 ≤ x ^ (1 - 2 * α) := Real.rpow_nonneg hx0.le _
  have he : Real.exp (-x) ^ 2 ≤ Real.exp (-x) := by
    have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (-x)]
  have hsq : ‖M χ x‖ ^ 2 ≤ 2 * ‖fM χ x‖ ^ 2 + 2 * ‖Cχ χ‖ ^ 2 * Real.exp (-x) ^ 2 := by
    rw [hMx]
    have h1 := norm_add_le (fM χ x) (Cχ χ * (Real.exp (-x) : ℂ))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at h1
    have h0 := norm_nonneg (fM χ x + Cχ χ * (Real.exp (-x) : ℂ))
    nlinarith [sq_nonneg (‖fM χ x‖ - ‖Cχ χ‖ * Real.exp (-x)), norm_nonneg (fM χ x),
      norm_nonneg (Cχ χ), Real.exp_pos (-x)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hpow, hpow']
  have hC0 : 0 ≤ ‖Cχ χ‖ ^ 2 := by positivity
  calc ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α)
      ≤ (2 * ‖fM χ x‖ ^ 2 + 2 * ‖Cχ χ‖ ^ 2 * Real.exp (-x) ^ 2) * x ^ (1 - 2 * α) :=
        mul_le_mul_of_nonneg_right hsq hp0
    _ ≤ (2 * ‖fM χ x‖ ^ 2 + 2 * ‖Cχ χ‖ ^ 2 * Real.exp (-x)) * x ^ (1 - 2 * α) := by
        gcongr
    _ = _ := by ring

end RiemannLab
