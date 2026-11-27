import RiemannLab.MuSum

/-!
# Step 4: the blow-up at the critical exponent, given the zero expansion

The mean-value lemma: if `P(x) = Σ c_i x^{s_i}` with `Re s_i = -1/4`, distinct `s_i` and `Σ |c_i| < ∞`, then
`(α - 3/4) ∫₁^∞ |P(x)|² x^{1-2α} dx → ½ Σ |c_i|²` as `α ↓ 3/4`. With the named hypothesis
`ZeroExpansion χ` (the explicit formula `M_χ(x) = Σ_ρ c_ρ x^{-(1-ρ)/2} + r(x)` for `x > 1`, with `r` square
integrable against `x^{-1/2}`) and GRH, this gives the blow-up `(α - 3/4)‖M_χ‖²_α → B_χ`.
-/

open Complex Filter Topology MeasureTheory Set

set_option linter.unusedSectionVars false

namespace RiemannLab

section MeanValue

open scoped Classical

variable {ι : Type*} [Countable ι]

lemma conj_cpow_ofReal {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (starRingEnd ℂ) ((x : ℂ) ^ z) = (x : ℂ) ^ ((starRingEnd ℂ) z) := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne
  rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

/-- The almost periodic sum `P(x) = Σ c_i x^{s_i}`. -/
noncomputable def Psum (c s : ι → ℂ) (x : ℝ) : ℂ := ∑' i, c i * (x : ℂ) ^ s i

/-- The `(i, j)` term of `|P|² x^{1-2α}`. -/
noncomputable def Fterm (c s : ι → ℂ) (α : ℝ) (p : ι × ι) (x : ℝ) : ℂ :=
  c p.1 * (starRingEnd ℂ) (c p.2) * (x : ℂ) ^ (s p.1 + (starRingEnd ℂ) (s p.2) + ((1 - 2 * α : ℝ) : ℂ))

variable {c s : ι → ℂ}

lemma norm_cpow_s {x : ℝ} (hx : 0 < x) (hs : ∀ i, (s i).re = -1 / 4) (i : ι) :
    ‖(x : ℂ) ^ s i‖ = x ^ (-1 / 4 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hs]

lemma summable_Psum_norm (hc : Summable fun i => ‖c i‖) (hs : ∀ i, (s i).re = -1 / 4)
    {x : ℝ} (hx : 0 < x) : Summable fun i => ‖c i * (x : ℂ) ^ s i‖ := by
  simp_rw [norm_mul, norm_cpow_s hx hs]
  exact hc.mul_right _

lemma re_exponent (hs : ∀ i, (s i).re = -1 / 4) (α : ℝ) (p : ι × ι) :
    (s p.1 + (starRingEnd ℂ) (s p.2) + ((1 - 2 * α : ℝ) : ℂ)).re = 1 / 2 - 2 * α := by
  simp only [add_re, conj_re, ofReal_re, hs]
  ring

lemma sq_norm_Psum_eq (hc : Summable fun i => ‖c i‖) (hs : ∀ i, (s i).re = -1 / 4)
    (α : ℝ) {x : ℝ} (hx : 0 < x) :
    (((‖Psum c s x‖ ^ 2 * x ^ (1 - 2 * α) : ℝ)) : ℂ) = ∑' p : ι × ι, Fterm c s α p x := by
  have hS := summable_Psum_norm hc hs hx
  have hS' : Summable fun i => ‖(starRingEnd ℂ) (c i * (x : ℂ) ^ s i)‖ := by
    simpa only [Complex.norm_conj] using hS
  rw [ofReal_mul, ofReal_pow, ← Complex.mul_conj', Complex.ofReal_cpow hx.le, Psum,
    Complex.conj_tsum, tsum_mul_tsum_of_summable_norm hS hS', ← tsum_mul_right]
  refine tsum_congr fun p => ?_
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Fterm, map_mul, conj_cpow_ofReal hx, Complex.cpow_add _ _ hx0, Complex.cpow_add _ _ hx0]
  push_cast
  ring

lemma integrableOn_Fterm (hs : ∀ i, (s i).re = -1 / 4) {α : ℝ} (hα : 3 / 4 < α) (p : ι × ι) :
    IntegrableOn (Fterm c s α p) (Ioi 1) := by
  refine (integrableOn_Ioi_cpow_of_lt ?_ one_pos).const_mul _
  rw [re_exponent hs]; linarith

lemma integral_norm_Fterm (hs : ∀ i, (s i).re = -1 / 4) {α : ℝ} (hα : 3 / 4 < α) (p : ι × ι) :
    ∫ x in Ioi (1:ℝ), ‖Fterm c s α p x‖ = ‖c p.1‖ * ‖c p.2‖ * (1 / (2 * α - 3 / 2)) := by
  have h : ∀ x ∈ Ioi (1:ℝ), ‖Fterm c s α p x‖ = ‖c p.1‖ * ‖c p.2‖ * x ^ (1 / 2 - 2 * α) := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    rw [Fterm, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      re_exponent hs]
  rw [setIntegral_congr_fun measurableSet_Ioi h, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow]
  congr 1
  rw [show (1 / 2 - 2 * α + 1) = -(2 * α - 3 / 2) by ring, div_neg, neg_div, neg_neg]

lemma integral_Fterm (hs : ∀ i, (s i).re = -1 / 4) {α : ℝ} (hα : 3 / 4 < α) (p : ι × ι) :
    ∫ x in Ioi (1:ℝ), Fterm c s α p x = c p.1 * (starRingEnd ℂ) (c p.2) *
      (-1 / (s p.1 + (starRingEnd ℂ) (s p.2) + ((1 - 2 * α : ℝ) : ℂ) + 1)) := by
  simp only [Fterm]
  rw [integral_const_mul, integral_Ioi_cpow_of_lt (by rw [re_exponent hs]; linarith) one_pos,
    ofReal_one, one_cpow]

/-- The `(i, j)` term after integration, times `α - 3/4`. -/
noncomputable def Dterm (s : ι → ℂ) (α : ℝ) (p : ι × ι) : ℂ :=
  ((α - 3 / 4 : ℝ) : ℂ) * (-1 / (s p.1 + (starRingEnd ℂ) (s p.2) + ((1 - 2 * α : ℝ) : ℂ) + 1))

lemma norm_Dterm_le (hs : ∀ i, (s i).re = -1 / 4) {α : ℝ} (hα : 3 / 4 < α) (p : ι × ι) :
    ‖Dterm s α p‖ ≤ 1 / 2 := by
  set E := s p.1 + (starRingEnd ℂ) (s p.2) + ((1 - 2 * α : ℝ) : ℂ) + 1 with hE
  have hre : E.re = 3 / 2 - 2 * α := by
    rw [hE, add_re, re_exponent hs, one_re]; ring
  have hEn : 2 * α - 3 / 2 ≤ ‖E‖ := by
    have := Complex.abs_re_le_norm E
    rw [hre, abs_of_neg (by linarith)] at this
    linarith
  have hpos : 0 < ‖E‖ := lt_of_lt_of_le (by linarith) hEn
  rw [Dterm, ← hE, norm_mul, norm_div, norm_neg, norm_one, Complex.norm_real,
    Real.norm_of_nonneg (by linarith), mul_one_div, div_le_iff₀ hpos]
  linarith

lemma tendsto_Dterm (hs : ∀ i, (s i).re = -1 / 4) (hinj : Function.Injective s) (p : ι × ι) :
    Tendsto (fun α => Dterm s α p) (𝓝[>] (3 / 4))
      (𝓝 (if p.1 = p.2 then (1 / 2 : ℂ) else 0)) := by
  split_ifs with h
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with α hα
    have hα' : (3:ℝ) / 4 < α := hα
    rw [Dterm, h, Complex.add_conj, hs]
    have hne : ((α - 3 / 4 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by linarith : α - 3 / 4 ≠ 0)
    have : (((2 * (-1 / 4) : ℝ) : ℂ) + ((1 - 2 * α : ℝ) : ℂ) + 1) = -2 * ((α - 3 / 4 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this]
    generalize ((α - 3 / 4 : ℝ) : ℂ) = t at hne ⊢
    field_simp
  · obtain ⟨den, hdenDef⟩ : ∃ den : ℝ → ℂ,
        den = fun α => s p.1 + (starRingEnd ℂ) (s p.2) + ((1 - 2 * α : ℝ) : ℂ) + 1 := ⟨_, rfl⟩
    have hne : den (3 / 4) ≠ 0 := by
      intro h0
      rw [hdenDef] at h0
      have him := congrArg Complex.im h0
      simp only [add_im, conj_im, ofReal_im, one_im, zero_im, add_zero] at him
      apply h
      apply hinj
      apply Complex.ext
      · rw [hs, hs]
      · linarith
    have hden : Continuous den := by
      rw [hdenDef]
      exact (continuous_const.add (Complex.continuous_ofReal.comp
        (continuous_const.sub (continuous_const.mul continuous_id)))).add continuous_const
    have hnum : Continuous (fun α : ℝ => ((α - 3 / 4 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)
    have hq : ContinuousAt (fun α : ℝ => (-1 : ℂ) / den α) (3 / 4) :=
      continuousAt_const.div hden.continuousAt hne
    have hcont := (hnum.continuousAt (x := 3 / 4)).mul hq
    have h0 : ((3 / 4 - 3 / 4 : ℝ) : ℂ) * ((-1 : ℂ) / den (3 / 4)) = 0 := by
      rw [sub_self, ofReal_zero, zero_mul]
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (3 / 4)))
    simp only [Pi.mul_apply] at this
    rw [h0] at this
    refine this.congr fun α => ?_
    rw [Dterm, hdenDef]
    rfl

/-- **Mean-value lemma.** If `Σ |c_i| < ∞`, `Re s_i = -1/4` and the `s_i` are distinct, then
`(α - 3/4) ∫₁^∞ |Σ c_i x^{s_i}|² x^{1-2α} dx → ½ Σ |c_i|²` as `α ↓ 3/4`. -/
theorem tendsto_meanValue (hc : Summable fun i => ‖c i‖) (hs : ∀ i, (s i).re = -1 / 4)
    (hinj : Function.Injective s) :
    Tendsto (fun α : ℝ => (α - 3 / 4) * ∫ x in Ioi (1:ℝ), ‖Psum c s x‖ ^ 2 * x ^ (1 - 2 * α))
      (𝓝[>] (3 / 4)) (𝓝 ((1 / 2) * ∑' i, ‖c i‖ ^ 2)) := by
  have hcc : Summable fun p : ι × ι => ‖c p.1‖ * ‖c p.2‖ := by
    have h := summable_mul_of_summable_norm (f := fun i => ‖c i‖) (g := fun i => ‖c i‖)
      (by simpa only [norm_norm] using hc) (by simpa only [norm_norm] using hc)
    exact h
  -- Step 1: the integral as a double series
  have hstep : ∀ α : ℝ, 3 / 4 < α →
      (((α - 3 / 4) * ∫ x in Ioi (1:ℝ), ‖Psum c s x‖ ^ 2 * x ^ (1 - 2 * α) : ℝ) : ℂ)
        = ∑' p : ι × ι, c p.1 * (starRingEnd ℂ) (c p.2) * Dterm s α p := by
    intro α hα
    rw [ofReal_mul, ← integral_complex_ofReal,
      setIntegral_congr_fun measurableSet_Ioi
        (fun x hx => sq_norm_Psum_eq hc hs α (lt_trans one_pos hx)),
      ← integral_tsum_of_summable_integral_norm (integrableOn_Fterm hs hα) ?_]
    · rw [← tsum_mul_left]
      refine tsum_congr fun p => ?_
      rw [integral_Fterm hs hα, Dterm]
      ring
    · simp_rw [integral_norm_Fterm hs hα]
      exact hcc.mul_right _
  -- Step 2: dominated convergence for the double series
  have hlim : Tendsto (fun α => ∑' p : ι × ι, c p.1 * (starRingEnd ℂ) (c p.2) * Dterm s α p)
      (𝓝[>] (3 / 4)) (𝓝 (∑' p : ι × ι, c p.1 * (starRingEnd ℂ) (c p.2) *
        (if p.1 = p.2 then (1 / 2 : ℂ) else 0))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun p => ‖c p.1‖ * ‖c p.2‖ * (1 / 2))
      (hcc.mul_right _) (fun p => (tendsto_Dterm hs hinj p).const_mul _) ?_
    filter_upwards [self_mem_nhdsWithin] with α hα p
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (norm_Dterm_le hs hα p) (by positivity)
  -- Step 3: the diagonal
  have hdiag : ∑' p : ι × ι, c p.1 * (starRingEnd ℂ) (c p.2) * (if p.1 = p.2 then (1 / 2 : ℂ) else 0)
      = (((1 / 2) * ∑' i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    have hsum : Summable fun p : ι × ι =>
        c p.1 * (starRingEnd ℂ) (c p.2) * (if p.1 = p.2 then (1 / 2 : ℂ) else 0) := by
      refine Summable.of_norm_bounded (hcc.mul_right (1 / 2)) fun p => ?_
      rw [norm_mul, norm_mul, Complex.norm_conj]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      split_ifs <;> norm_num
    rw [hsum.tsum_prod]
    have hin : ∀ i, ∑' j, c (i, j).1 * (starRingEnd ℂ) (c (i, j).2) *
        (if (i, j).1 = (i, j).2 then (1 / 2 : ℂ) else 0) = (1 / 2 : ℂ) * ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [tsum_eq_single i (fun j hj => by simp [Ne.symm hj])]
      simp only [if_true]
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [tsum_congr hin, tsum_mul_left, ofReal_mul, Complex.ofReal_tsum]
    push_cast
    ring
  rw [hdiag] at hlim
  have hC : Tendsto (fun α : ℝ =>
      (((α - 3 / 4) * ∫ x in Ioi (1:ℝ), ‖Psum c s x‖ ^ 2 * x ^ (1 - 2 * α) : ℝ) : ℂ))
      (𝓝[>] (3 / 4)) (𝓝 (((1 / 2) * ∑' i, ‖c i‖ ^ 2 : ℝ) : ℂ)) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with α hα
    exact (hstep α hα).symm
  have h := (Complex.continuous_re.tendsto _).comp hC
  rw [Complex.ofReal_re] at h
  exact h.congr fun α => Complex.ofReal_re _

end MeanValue

end RiemannLab
