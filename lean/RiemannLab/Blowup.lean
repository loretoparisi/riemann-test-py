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

variable {ι : Type*}

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
theorem tendsto_meanValue [Countable ι] (hc : Summable fun i => ‖c i‖) (hs : ∀ i, (s i).re = -1 / 4)
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

section General

variable {ι : Type*} {c s : ι → ℂ}

/-- The mean-value lemma for an arbitrary index type: a summable family has countable support. -/
theorem tendsto_meanValue' (hc : Summable fun i => ‖c i‖) (hs : ∀ i, (s i).re = -1 / 4)
    (hinj : Function.Injective s) :
    Tendsto (fun α : ℝ => (α - 3 / 4) * ∫ x in Ioi (1:ℝ), ‖Psum c s x‖ ^ 2 * x ^ (1 - 2 * α))
      (𝓝[>] (3 / 4)) (𝓝 ((1 / 2) * ∑' i, ‖c i‖ ^ 2)) := by
  set S := Function.support c
  have hS : S.Countable := by
    have h := hc.countable_support
    have he : Function.support (fun i => ‖c i‖) = S := by ext; simp [S]
    rwa [he] at h
  have : Countable S := hS.to_subtype
  have hP : ∀ x, Psum c s x = Psum (fun i : S => c i) (fun i : S => s i) x := by
    intro x
    rw [Psum, Psum, tsum_subtype_eq_of_support_subset (f := fun i => c i * (x : ℂ) ^ s i)]
    intro i hi
    exact fun h0 => hi (by simp [h0])
  have hsq : ∑' i, ‖c i‖ ^ 2 = ∑' i : S, ‖c i‖ ^ 2 := by
    rw [tsum_subtype_eq_of_support_subset (f := fun i => ‖c i‖ ^ 2)]
    intro i hi
    exact fun h0 => hi (by simp [h0])
  simp_rw [hP]
  rw [hsq]
  exact tendsto_meanValue (hc.comp_injective Subtype.val_injective) (fun i => hs i) (hinj.comp Subtype.val_injective)

lemma norm_Psum_le (hc : Summable fun i => ‖c i‖) (hs : ∀ i, (s i).re = -1 / 4) {x : ℝ}
    (hx : 0 < x) : ‖Psum c s x‖ ≤ (∑' i, ‖c i‖) * x ^ (-1 / 4 : ℝ) := by
  calc ‖Psum c s x‖ ≤ ∑' i, ‖c i * (x : ℂ) ^ s i‖ :=
        norm_tsum_le_tsum_norm (summable_Psum_norm hc hs hx)
    _ = ∑' i, ‖c i‖ * x ^ (-1 / 4 : ℝ) := by
        simp_rw [norm_mul, norm_cpow_s hx hs]
    _ = _ := tsum_mul_right

lemma continuousOn_Psum (hc : Summable fun i => ‖c i‖) (hs : ∀ i, (s i).re = -1 / 4) :
    ContinuousOn (Psum c s) (Ioi 1) := by
  refine continuousOn_tsum (u := fun i => ‖c i‖) (fun i => ?_) hc (fun i x hx => ?_)
  · refine continuousOn_const.mul fun x hx => ?_
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    refine ContinuousAt.continuousWithinAt ?_
    exact (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hx0)).comp
      Complex.continuous_ofReal.continuousAt
  · have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    rw [norm_mul, norm_cpow_s hx0 hs]
    have : x ^ (-1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hx) (by norm_num)
    calc ‖c i‖ * x ^ (-1 / 4 : ℝ) ≤ ‖c i‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖c i‖ := mul_one _

/-- `|P|² x^{1-2α}` is integrable on `(1, ∞)` for `α > 3/4`. -/
lemma integrableOn_Psum_sq (hc : Summable fun i => ‖c i‖) (hs : ∀ i, (s i).re = -1 / 4)
    {α : ℝ} (hα : 3 / 4 < α) :
    IntegrableOn (fun x => ‖Psum c s x‖ ^ 2 * x ^ (1 - 2 * α)) (Ioi 1) := by
  set S := ∑' i, ‖c i‖
  have hint : IntegrableOn (fun x : ℝ => S ^ 2 * x ^ (1 / 2 - 2 * α)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
  refine hint.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ((continuousOn_Psum hc hs).norm.pow 2).mul ?_
    exact fun x hx => (Real.continuousAt_rpow_const _ _
      (Or.inl (lt_trans one_pos hx).ne')).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    have hw : 0 < x ^ (1 - 2 * α) := Real.rpow_pos_of_pos hx0 _
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 := norm_Psum_le hc hs hx0
    have h2 : ‖Psum c s x‖ ^ 2 ≤ (S * x ^ (-1 / 4 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc ‖Psum c s x‖ ^ 2 * x ^ (1 - 2 * α) ≤ (S * x ^ (-1 / 4 : ℝ)) ^ 2 * x ^ (1 - 2 * α) :=
          mul_le_mul_of_nonneg_right h2 hw.le
      _ = S ^ 2 * x ^ (1 / 2 - 2 * α) := by
          rw [mul_pow, ← Real.rpow_natCast (x ^ _), ← Real.rpow_mul hx0.le, mul_assoc,
            ← Real.rpow_add hx0]
          congr 2
          push_cast
          ring

end General

lemma sq_norm_add_sub_le (a b : ℂ) {t : ℝ} (ht : 0 < t) :
    |‖a + b‖ ^ 2 - ‖a‖ ^ 2| ≤ t * ‖a‖ ^ 2 + (1 + 1 / t) * ‖b‖ ^ 2 := by
  have h1 : |‖a + b‖ - ‖a‖| ≤ ‖b‖ := by
    have := abs_norm_sub_norm_le (a + b) a
    simpa using this
  have hu : 0 ≤ ‖a‖ := norm_nonneg _
  have hv : 0 ≤ ‖b‖ := norm_nonneg _
  have hw : 0 ≤ ‖a + b‖ := norm_nonneg _
  generalize ‖a‖ = u at *
  generalize ‖b‖ = v at *
  generalize ‖a + b‖ = w at *
  have h2 : |w ^ 2 - u ^ 2| ≤ v * (2 * u + v) := by
    rw [show w ^ 2 - u ^ 2 = (w - u) * (w + u) by ring, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ w + u)]
    have hwu : w + u ≤ 2 * u + v := by have := (abs_le.mp h1).2; linarith
    calc |w - u| * (w + u) ≤ v * (w + u) := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ v * (2 * u + v) := mul_le_mul_of_nonneg_left hwu hv
  have h3 : 2 * u * v ≤ t * u ^ 2 + v ^ 2 / t := by
    rw [← sub_nonneg]
    have : t * u ^ 2 + v ^ 2 / t - 2 * u * v = (t * u - v) ^ 2 / t := by field_simp; ring
    rw [this]; positivity
  calc |w ^ 2 - u ^ 2| ≤ v * (2 * u + v) := h2
    _ = 2 * u * v + v ^ 2 := by ring
    _ ≤ t * u ^ 2 + v ^ 2 / t + v ^ 2 := by linarith
    _ = t * u ^ 2 + (1 + 1 / t) * v ^ 2 := by field_simp; ring

lemma tendsto_sub_mul_zero (Q : ℝ) :
    Tendsto (fun α : ℝ => (α - 3 / 4) * Q) (𝓝[>] (3 / 4)) (𝓝 0) := by
  have h : Tendsto (fun α : ℝ => (α - 3 / 4) * Q) (𝓝 (3 / 4)) (𝓝 ((3 / 4 - 3 / 4) * Q)) :=
    (tendsto_id.sub_const (3 / 4)).mul_const Q
  rw [sub_self, zero_mul] at h
  exact tendsto_nhdsWithin_of_tendsto_nhds h

section Blowup

variable {N : ℕ} [NeZero N]

/-- The residue of `Γ(s)/L(1 - 2s, χ)` at `s = (1 - ρ)/2`, for a simple zero `ρ`. -/
noncomputable def resCoef (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℂ :=
  -Gamma ((1 - ρ) / 2) / (2 * deriv (DirichletCharacter.LFunction χ) ρ)

/-- **Named hypothesis: the explicit formula over the zeros.** For `x > 1`,
`M_χ(x) = Σ_ρ c_ρ x^{-(1-ρ)/2} + r(x)` with `c_ρ = -Γ((1-ρ)/2) / (2 L'(ρ, χ))` and a remainder `r` with
`∫₁^∞ |r(x)|² x^{-1/2} dx < ∞`. This is what a contour shift past all the zeros gives when the zeros are simple
and the sum converges (the trivial zeros contribute `O(x^{-1/2})`); it is assumed, not proved. -/
def ZeroExpansion (χ : DirichletCharacter ℂ N) : Prop :=
  ∃ r : ℝ → ℂ, IntegrableOn (fun x : ℝ => ‖r x‖ ^ 2 * x ^ (-(1 / 2) : ℝ)) (Ioi 1) ∧
    ∀ x : ℝ, 1 < x → M χ x =
      (∑' ρ : zeros χ, resCoef χ ρ * (x : ℂ) ^ (-(1 - (ρ : ℂ)) / 2)) + r x

/-- **The blow-up at the critical exponent, given the zero expansion.** Under GRH, the named hypothesis
`ZeroExpansion χ` and `Σ_ρ |Γ((1-ρ)/2)/L'(ρ, χ)| < ∞`,
`(α - 3/4) ∫₀^∞ |M_χ(x)|² x^{1-2α} dx → (1/8) Σ_ρ |Γ((1-ρ)/2) / L'(ρ, χ)|²` as `α ↓ 3/4`. -/
theorem blowup_limit_of_expansion (χ : DirichletCharacter ℂ N) (hGRH : GRH χ)
    (hexp : ZeroExpansion χ)
    (habs : Summable fun ρ : zeros χ =>
      ‖Gamma ((1 - (ρ : ℂ)) / 2) / deriv (DirichletCharacter.LFunction χ) ρ‖) :
    Tendsto (fun α : ℝ => (α - 3 / 4) * normSq χ α) (𝓝[>] (3 / 4))
      (𝓝 ((1 / 8) * ∑' ρ : zeros χ,
        ‖Gamma ((1 - (ρ : ℂ)) / 2) / deriv (DirichletCharacter.LFunction χ) ρ‖ ^ 2)) := by
  obtain ⟨r, hr, hM⟩ := hexp
  set c : zeros χ → ℂ := fun ρ => resCoef χ ρ with hcdef
  set s : zeros χ → ℂ := fun ρ => -(1 - (ρ : ℂ)) / 2 with hsdef
  have hnc : ∀ ρ : zeros χ, ‖c ρ‖
      = ‖Gamma ((1 - (ρ : ℂ)) / 2) / deriv (DirichletCharacter.LFunction χ) ρ‖ / 2 := by
    intro ρ
    simp only [hcdef, resCoef, norm_div, norm_neg, norm_mul, Complex.norm_ofNat]
    ring
  have hc : Summable fun ρ => ‖c ρ‖ := by simp_rw [hnc]; exact habs.div_const 2
  have hs : ∀ ρ, (s ρ).re = -1 / 4 := by
    intro ρ
    have h := hGRH ρ ρ.2.1 ρ.2.2.1 ρ.2.2.2
    simp only [hsdef, neg_div, neg_re, div_ofNat_re, sub_re, one_re, h]
    norm_num
  have hinj : Function.Injective s := by
    intro a b h
    simp only [hsdef] at h
    exact Subtype.ext (by linear_combination 2 * h)
  set P := Psum c s with hPdef
  have hMP : ∀ x : ℝ, 1 < x → M χ x = P x + r x := fun x hx => hM x hx
  have hmean := tendsto_meanValue' hc hs hinj
  set Bc := (1 / 2) * ∑' ρ, ‖c ρ‖ ^ 2 with hBc
  have hB : Bc = (1 / 8) * ∑' ρ : zeros χ,
      ‖Gamma ((1 - (ρ : ℂ)) / 2) / deriv (DirichletCharacter.LFunction χ) ρ‖ ^ 2 := by
    rw [hBc]
    simp_rw [hnc, div_pow]
    rw [tsum_div_const]
    ring
  rw [← hB]
  have hBc0 : 0 ≤ Bc := by rw [hBc]; exact mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  -- continuity and measurability
  have hPc := continuousOn_Psum hc hs
  have hMc : ContinuousOn (M χ) (Ioi 1) := (continuousOn_M χ).mono (Ioi_subset_Ioi zero_le_one)
  have hrc : ContinuousOn r (Ioi 1) := by
    refine (hMc.sub hPc).congr fun x hx => ?_
    simp only [Pi.sub_apply]
    rw [hMP x hx]; ring
  have hwc : ∀ α : ℝ, ContinuousOn (fun x : ℝ => x ^ (1 - 2 * α)) (Ioi 0) := fun α x hx =>
    (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hx))).continuousWithinAt
  -- constants
  set R0 := ∫ x in Ioi (1:ℝ), ‖r x‖ ^ 2 * x ^ (-(1 / 2) : ℝ) with hR0
  have hR00 : 0 ≤ R0 := setIntegral_nonneg measurableSet_Ioi fun x hx =>
    mul_nonneg (by positivity) (Real.rpow_nonneg (lt_trans one_pos hx).le _)
  set C := Z 1 + ‖1 / DirichletCharacter.LFunction χ 1‖ with hC
  have hMb : ∀ x ∈ Ioc (0:ℝ) 1, ‖M χ x‖ ≤ C := by
    intro x hx
    have h := norm_Mt_le χ hx.1 one_pos le_rfl
    rw [Real.rpow_one] at h
    have hZ := Z_nonneg 1
    calc ‖M χ x‖ ≤ ‖Mt χ x‖ + ‖1 / DirichletCharacter.LFunction χ 1‖ := norm_add_le _ _
      _ ≤ Z 1 + ‖1 / DirichletCharacter.LFunction χ 1‖ := by
          gcongr
          calc ‖Mt χ x‖ ≤ Z 1 * x := h
            _ ≤ Z 1 * 1 := mul_le_mul_of_nonneg_left hx.2 hZ
            _ = Z 1 := mul_one _
  have hC0 : 0 ≤ C := by rw [hC]; exact add_nonneg (Z_nonneg 1) (norm_nonneg _)
  have hK : IntegrableOn (fun x : ℝ => x ^ (-(3 / 4) : ℝ)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  set K := ∫ x in Ioc (0:ℝ) 1, x ^ (-(3 / 4) : ℝ) with hKdef
  -- the pieces, for 3/4 < α < 7/8
  obtain ⟨Hf, hHf⟩ : ∃ f : ℝ → ℝ,
      f = fun α => ∫ x in Ioc (0:ℝ) 1, ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α) := ⟨_, rfl⟩
  obtain ⟨Gf, hGf⟩ : ∃ f : ℝ → ℝ,
      f = fun α => ∫ x in Ioi (1:ℝ), ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α) := ⟨_, rfl⟩
  obtain ⟨Af, hAf⟩ : ∃ f : ℝ → ℝ,
      f = fun α => ∫ x in Ioi (1:ℝ), ‖P x‖ ^ 2 * x ^ (1 - 2 * α) := ⟨_, rfl⟩
  have hpieces : ∀ α : ℝ, 3 / 4 < α → α < 7 / 8 →
      ∀ t : ℝ, 0 < t →
      normSq χ α = Hf α + Gf α ∧ 0 ≤ Hf α ∧ Hf α ≤ C ^ 2 * K ∧
        |Gf α - Af α| ≤ t * Af α + (1 + 1 / t) * R0 := by
    intro α hα1 hα2 t ht
    have hw1 : ∀ x : ℝ, 1 < x → x ^ (1 - 2 * α) ≤ x ^ (-(1 / 2) : ℝ) := fun x hx =>
      Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)
    have intR : IntegrableOn (fun x : ℝ => ‖r x‖ ^ 2 * x ^ (1 - 2 * α)) (Ioi 1) := by
      refine hr.mono' ?_ ?_
      · exact ContinuousOn.aestronglyMeasurable
          ((hrc.norm.pow 2).mul ((hwc α).mono (Ioi_subset_Ioi zero_le_one))) measurableSet_Ioi
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
        have hx0 : (0:ℝ) < x := lt_trans one_pos hx
        rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hx0.le _))]
        exact mul_le_mul_of_nonneg_left (hw1 x hx) (by positivity)
    have intP := integrableOn_Psum_sq hc hs hα1
    have hbnd : ∀ x : ℝ, 1 < x → ‖‖M χ x‖ ^ 2 * x ^ (1 - 2 * α) - ‖P x‖ ^ 2 * x ^ (1 - 2 * α)‖
        ≤ t * (‖P x‖ ^ 2 * x ^ (1 - 2 * α)) + (1 + 1 / t) * (‖r x‖ ^ 2 * x ^ (1 - 2 * α)) := by
      intro x hx
      have hw : 0 ≤ x ^ (1 - 2 * α) := Real.rpow_nonneg (lt_trans one_pos hx).le _
      rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, hMP x hx]
      have := sq_norm_add_sub_le (P x) (r x) ht
      nlinarith
    have intM1 : IntegrableOn (fun x : ℝ => ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α)) (Ioi 1) := by
      have hsum := (intP.const_mul (1 + t)).add (intR.const_mul (1 + 1 / t))
      refine hsum.mono' ?_ ?_
      · exact ContinuousOn.aestronglyMeasurable
          ((hMc.norm.pow 2).mul ((hwc α).mono (Ioi_subset_Ioi zero_le_one))) measurableSet_Ioi
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
        have hx0 : (0:ℝ) < x := lt_trans one_pos hx
        have hw : 0 ≤ x ^ (1 - 2 * α) := Real.rpow_nonneg hx0.le _
        have h := hbnd x hx
        rw [Real.norm_eq_abs, abs_le] at h
        rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hw)]
        simp only [Pi.add_apply]
        nlinarith [h.2]
    have intM0 : IntegrableOn (fun x : ℝ => ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α)) (Ioc 0 1) := by
      refine (hK.const_mul (C ^ 2)).mono' ?_ ?_
      · exact ContinuousOn.aestronglyMeasurable
          (((continuousOn_M χ).mono Ioc_subset_Ioi_self).norm.pow 2 |>.mul
            ((hwc α).mono Ioc_subset_Ioi_self)) measurableSet_Ioc
      · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx => ?_)
        have hw : 0 ≤ x ^ (1 - 2 * α) := Real.rpow_nonneg hx.1.le _
        rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hw)]
        have h1 : ‖M χ x‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hMb x hx) 2
        have h2 : x ^ (1 - 2 * α) ≤ x ^ (-(3 / 4) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith)
        exact mul_le_mul h1 h2 hw (by positivity)
    subst hHf hGf hAf
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [normSq, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
        setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi intM0 intM1]
    · exact setIntegral_nonneg measurableSet_Ioc fun x hx =>
        mul_nonneg (by positivity) (Real.rpow_nonneg hx.1.le _)
    · rw [hKdef, ← integral_const_mul]
      refine setIntegral_mono_on intM0 (hK.const_mul _) measurableSet_Ioc fun x hx => ?_
      have hw : 0 ≤ x ^ (1 - 2 * α) := Real.rpow_nonneg hx.1.le _
      have h1 : ‖M χ x‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hMb x hx) 2
      have h2 : x ^ (1 - 2 * α) ≤ x ^ (-(3 / 4) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith)
      exact mul_le_mul h1 h2 hw (by positivity)
    · rw [← integral_sub intM1 intP, ← Real.norm_eq_abs]
      have hRα : ∫ x in Ioi (1:ℝ), ‖r x‖ ^ 2 * x ^ (1 - 2 * α) ≤ R0 := by
        refine setIntegral_mono_on intR hr measurableSet_Ioi fun x hx => ?_
        exact mul_le_mul_of_nonneg_left (hw1 x hx) (by positivity)
      calc ‖∫ x in Ioi (1:ℝ), (‖M χ x‖ ^ 2 * x ^ (1 - 2 * α) - ‖P x‖ ^ 2 * x ^ (1 - 2 * α))‖
          ≤ ∫ x in Ioi (1:ℝ), (t * (‖P x‖ ^ 2 * x ^ (1 - 2 * α))
              + (1 + 1 / t) * (‖r x‖ ^ 2 * x ^ (1 - 2 * α))) := by
            refine norm_integral_le_of_norm_le ((intP.const_mul t).add (intR.const_mul _)) ?_
            exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbnd)
        _ = t * (∫ x in Ioi (1:ℝ), ‖P x‖ ^ 2 * x ^ (1 - 2 * α))
              + (1 + 1 / t) * ∫ x in Ioi (1:ℝ), ‖r x‖ ^ 2 * x ^ (1 - 2 * α) := by
            rw [integral_add (intP.const_mul t) (intR.const_mul _), integral_const_mul,
              integral_const_mul]
        _ ≤ t * (∫ x in Ioi (1:ℝ), ‖P x‖ ^ 2 * x ^ (1 - 2 * α)) + (1 + 1 / t) * R0 := by
            gcongr
  have hev : ∀ᶠ α in 𝓝[>] (3 / 4 : ℝ), 3 / 4 < α ∧ α < 7 / 8 :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (3 / 4 : ℝ) < 7 / 8)) fun α hα => hα
  have hlimA : Tendsto (fun α => (α - 3 / 4) * Af α) (𝓝[>] (3 / 4)) (𝓝 Bc) := by
    rw [hAf]; exact hmean
  have hH : Tendsto (fun α => (α - 3 / 4) * Hf α) (𝓝[>] (3 / 4)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_sub_mul_zero (C ^ 2 * K))
    filter_upwards [hev] with α hα
    obtain ⟨_, h0, h1, _⟩ := hpieces α hα.1 hα.2 1 one_pos
    have hpos : 0 < α - 3 / 4 := by linarith [hα.1]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left h1 hpos.le
  have hU : Tendsto (fun α => (α - 3 / 4) * (Gf α - Af α)) (𝓝[>] (3 / 4)) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hB1 : 0 < Bc + 1 := by linarith
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ε / (2 * (Bc + 1)) := ⟨_, rfl⟩
    have ht0 : 0 < t := by rw [ht]; positivity
    have e1 : ∀ᶠ α in 𝓝[>] (3 / 4 : ℝ), (α - 3 / 4) * Af α < Bc + 1 :=
      hlimA.eventually (gt_mem_nhds (lt_add_one Bc))
    have e2 : ∀ᶠ α in 𝓝[>] (3 / 4 : ℝ), (α - 3 / 4) * ((1 + 1 / t) * R0) < ε / 2 :=
      (tendsto_sub_mul_zero _).eventually (gt_mem_nhds (by positivity))
    filter_upwards [hev, e1, e2] with α hα h1 h2
    obtain ⟨_, _, _, h3⟩ := hpieces α hα.1 hα.2 t ht0
    have hpos : 0 < α - 3 / 4 := by linarith [hα.1]
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
    have h4 := mul_le_mul_of_nonneg_left h3 hpos.le
    have h5 : t * ((α - 3 / 4) * Af α) ≤ t * (Bc + 1) := mul_le_mul_of_nonneg_left h1.le ht0.le
    have h6 : t * (Bc + 1) = ε / 2 := by rw [ht]; field_simp
    have h7 : (α - 3 / 4) * (t * Af α + (1 + 1 / t) * R0)
        = t * ((α - 3 / 4) * Af α) + (α - 3 / 4) * ((1 + 1 / t) * R0) := by ring
    linarith
  have hsum := (hH.add hlimA).add hU
  rw [zero_add, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hev] with α hα
  obtain ⟨h0, _, _, _⟩ := hpieces α hα.1 hα.2 1 one_pos
  rw [h0]
  ring

end Blowup

end RiemannLab
