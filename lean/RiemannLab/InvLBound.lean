import RiemannLab.LGrowth
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.BorelCaratheodory

/-!
# A polynomial bound for `1/L(w, χ)` on `1/2 < Re w ≤ 3` under GRH

Under GRH, `L(·, χ)` has no zeros on `Re w > 1/2`, so it has a holomorphic logarithm `F` on every
disc there (`exists_log_on_ball`, from Mathlib's primitives on discs). On the disc of radius
`R = 7/2 - d/2` around `4 + it`, `Re F = log |L| ≤ log (2N(|t| + 8))` by `norm_LFunction_le`, and
`|F(4 + it)|` is bounded through `|L(4 + it)| ≥ 1/Z` with `Z = Σ n^{-4}`. Borel–Carathéodory
(Mathlib) then bounds `|F|`, hence `|1/L| = exp(-Re F)`, by a power of `|t| + 8` on
`1/2 + d ≤ Re w ≤ 3` (`norm_inv_LFunction_le`).
-/

open Complex MeasureTheory Set Filter Topology DirichletCharacter Metric
open scoped LSeries.notation ArithmeticFunction.Moebius

noncomputable section

namespace RiemannLab

/-- **Holomorphic logarithm on a disc.** A nonvanishing holomorphic function on a disc is `exp F`
for a holomorphic `F` with `F c = log (f c)`. -/
lemma exists_log_on_ball {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hf0 : ∀ z ∈ ball c r, f z ≠ 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball c r) ∧ F c = Complex.log (f c) ∧
      ∀ z ∈ ball c r, exp (F z) = f z := by
  have hc : c ∈ ball c r := mem_ball_self hr
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c r) :=
    (hf.deriv isOpen_ball).div hf hf0
  obtain ⟨G, hG⟩ := hd.isExactOn_ball
  have hfd : ∀ z ∈ ball c r, HasDerivAt f (deriv f z) z := fun z hz =>
    ((hf z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  set φ : ℂ → ℂ := fun z => f z * exp (-G z) with hφ
  have hφd : ∀ z ∈ ball c r, HasDerivAt φ 0 z := by
    intro z hz
    have h := (hfd z hz).mul ((hG z hz).neg.cexp)
    convert h using 1
    field_simp [hf0 z hz]
    ring
  have hφc : EqOn φ (fun _ => φ c) (ball c r) := by
    refine isOpen_ball.eqOn_of_deriv_eq (convex_ball c r).isPreconnected
      (fun z hz => (hφd z hz).differentiableAt.differentiableWithinAt)
      (differentiableOn_const _) (fun z hz => ?_) hc rfl
    simp only [(hφd z hz).deriv, deriv_const]
  refine ⟨fun z => G z - G c + Complex.log (f c), ?_, by simp, fun z hz => ?_⟩
  · exact fun z hz => (((hG z hz).differentiableAt.sub_const _).add_const _).differentiableWithinAt
  · have h := hφc hz
    simp only [hφ] at h
    rw [exp_add, exp_log (hf0 c hc), exp_sub]
    have he : exp (-G z) ≠ 0 := exp_ne_zero _
    rw [exp_neg, exp_neg] at h
    field_simp at h ⊢
    linear_combination -h

variable {N : ℕ} [NeZero N]

/-- Under GRH, `L(z, χ) ≠ 0` for `Re z > 1/2`. -/
lemma LFunction_ne_zero_of_GRH (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hGRH : GRH χ)
    {z : ℂ} (hz : 1 / 2 < z.re) : LFunction χ z ≠ 0 := by
  rcases lt_or_ge z.re 1 with h1 | h1
  · intro h0
    have := hGRH z (by linarith) h1 h0
    linarith
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h1

omit [NeZero N] in
lemma norm_mulMu_le (χ : DirichletCharacter ℂ N) (n : ℕ) : ‖(↗χ * ↗μ) n‖ ≤ 1 := by
  rw [Pi.mul_apply, norm_mul]
  have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hμ : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc ‖χ n‖ * ‖((μ n : ℤ) : ℂ)‖ ≤ 1 * 1 := by gcongr
    _ = 1 := by ring

/-- On `Re w = 4`: `1 ≤ |L(w, χ)| · Z(3/2)`, with `Z(3/2) = Σ n^{-4}`. -/
lemma one_le_norm_LFunction_mul_Z (χ : DirichletCharacter ℂ N) {w : ℂ} (hw : w.re = 4) :
    1 ≤ ‖LFunction χ w‖ * Z (3 / 2) := by
  have hre : 1 < w.re := by rw [hw]; norm_num
  have h1 := LSeries.mul_mu_eq_one χ hre
  have hterm : ∀ n : ℕ, ‖LSeries.term (↗χ * ↗μ) w n‖ ≤ (n : ℝ) ^ (-1 - 2 * (3 / 2 : ℝ)) := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with hn
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · have hn0 : (0:ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      rw [hw, show (-1 - 2 * (3 / 2 : ℝ)) = -4 by norm_num, Real.rpow_neg hn0.le]
      exact (div_le_div_of_nonneg_right (norm_mulMu_le χ n) (by positivity)).trans
        (le_of_eq (one_div _))
  have hsum : Summable fun n => ‖LSeries.term (↗χ * ↗μ) w n‖ :=
    (summable_Z (by norm_num : (0:ℝ) < 3 / 2)).of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  have hle : ‖LSeries (↗χ * ↗μ) w‖ ≤ Z (3 / 2) :=
    (norm_tsum_le_tsum_norm hsum).trans
      (hsum.tsum_le_tsum hterm (summable_Z (by norm_num : (0:ℝ) < 3 / 2)))
  rw [LFunction_eq_LSeries χ hre]
  calc (1:ℝ) = ‖LSeries ↗χ w * LSeries (↗χ * ↗μ) w‖ := by rw [h1, norm_one]
    _ = ‖LSeries ↗χ w‖ * ‖LSeries (↗χ * ↗μ) w‖ := norm_mul _ _
    _ ≤ ‖LSeries ↗χ w‖ * Z (3 / 2) := mul_le_mul_of_nonneg_left hle (norm_nonneg _)

lemma bc_arith {M a z R d : ℝ} (hM : 0 ≤ M) (ha : 0 ≤ a) (_hz0 : 0 ≤ z) (hz : z ≤ 4)
    (hR : R ≤ 4) (hd : 0 < d) (hgap : d / 2 ≤ R - z) :
    2 * M * z / (R - z) + a * (R + z) / (R - z) ≤ 16 / d * (M + a) := by
  have hpos : 0 < R - z := by linarith
  rw [← add_div, div_le_iff₀ hpos]
  have h1 : 8 * (M + a) ≤ 16 / d * (M + a) * (R - z) := by
    calc 8 * (M + a) = 16 / d * (M + a) * (d / 2) := by field_simp; ring
      _ ≤ 16 / d * (M + a) * (R - z) := by gcongr
  nlinarith

/-- **Polynomial bound for `1/L` under GRH.** For `0 < d ≤ 1` there are `C, K ≥ 0` with
`|1/L(w, χ)| ≤ C (|Im w| + 8)^K` whenever `1/2 + d ≤ Re w ≤ 3`. -/
theorem norm_inv_LFunction_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hGRH : GRH χ)
    {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ w : ℂ, 1 / 2 + d ≤ w.re → w.re ≤ 3 →
      ‖(LFunction χ w)⁻¹‖ ≤ C * (|w.im| + 8) ^ K := by
  set Z4 := Z (3 / 2) with hZ4
  set c1 : ℝ := 1 + |Real.log Z4| + Real.pi with hc1
  set K : ℝ := 32 / d with hK
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  refine ⟨Real.exp (16 / d * c1) * (2 * N) ^ K, K, by positivity, by positivity, ?_⟩
  intro w hw1 hw3
  set t := w.im with ht
  set w0 : ℂ := 4 + t * I with hw0
  set R : ℝ := 7 / 2 - d / 2 with hR
  have hRpos : 0 < R := by linarith
  have hw0re : w0.re = 4 := by simp [hw0]
  have hw0im : w0.im = t := by simp [hw0]
  have hw0norm : ‖w0‖ ≤ 4 + |t| := by
    calc ‖w0‖ ≤ ‖(4:ℂ)‖ + ‖(t:ℂ) * I‖ := norm_add_le _ _
      _ = 4 + |t| := by simp
  set B : ℝ := 2 * N * (|t| + 8) with hB
  have hB1 : 1 < B := by
    have : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have hBpos : 0 < B := by linarith
  -- the disc lies in `Re z > 1/2 + d/2`, where `L ≠ 0` and `|L| ≤ B`
  have hball_re : ∀ z ∈ ball w0 R, 1 / 2 + d / 2 < z.re := by
    intro z hz
    have h1 := abs_re_le_norm (z - w0)
    rw [mem_ball, dist_eq_norm] at hz
    rw [sub_re, hw0re] at h1
    linarith [neg_abs_le (z.re - 4)]
  have hball_norm : ∀ z ∈ ball w0 R, ‖z‖ ≤ |t| + 8 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have := norm_le_norm_add_norm_sub' z w0
    linarith
  have hL0 : ∀ z ∈ ball w0 R, LFunction χ z ≠ 0 := fun z hz =>
    LFunction_ne_zero_of_GRH χ hχ hGRH (by linarith [hball_re z hz])
  have hLB : ∀ z ∈ ball w0 R, ‖LFunction χ z‖ ≤ B := by
    intro z hz
    have hre := hball_re z hz
    have hre0 : 0 < z.re := by linarith
    refine (norm_LFunction_le χ hχ hre0).trans ?_
    rw [div_le_iff₀ hre0, hB]
    have := hball_norm z hz
    have hN0 : (0:ℝ) ≤ N := by linarith
    nlinarith
  obtain ⟨F, hFd, hFc, hFexp⟩ := exists_log_on_ball hRpos
    (differentiable_LFunction hχ).differentiableOn hL0
  have hw0mem : w0 ∈ ball w0 R := mem_ball_self hRpos
  have hReF : ∀ z ∈ ball w0 R, (F z).re = Real.log ‖LFunction χ z‖ := by
    intro z hz
    rw [← hFexp z hz, Complex.norm_exp, Real.log_exp]
  have hReF_le : ∀ z ∈ ball w0 R, (F z).re ≤ Real.log B := by
    intro z hz
    rw [hReF z hz]
    exact Real.log_le_log (norm_pos_iff.mpr (hL0 z hz)) (hLB z hz)
  -- `|F(w0)|`
  have hlow := one_le_norm_LFunction_mul_Z χ hw0re
  have hZpos : 0 < Z4 := by
    by_contra h
    push Not at h
    nlinarith [norm_nonneg (LFunction χ w0)]
  have hLw0pos : 0 < ‖LFunction χ w0‖ := norm_pos_iff.mpr (hL0 w0 hw0mem)
  have hlog_w0 : |Real.log ‖LFunction χ w0‖| ≤ Real.log B + |Real.log Z4| := by
    rw [abs_le]
    constructor
    · have h1 : Real.log (1 / Z4) ≤ Real.log ‖LFunction χ w0‖ := by
        refine Real.log_le_log (by positivity) ?_
        rw [div_le_iff₀ hZpos]
        exact hlow
      rw [one_div, Real.log_inv] at h1
      have := Real.log_pos hB1
      linarith [le_abs_self (Real.log Z4)]
    · have := Real.log_le_log hLw0pos (hLB w0 hw0mem)
      linarith [abs_nonneg (Real.log Z4)]
  have hFw0 : ‖F w0‖ ≤ Real.log B + |Real.log Z4| + Real.pi := by
    rw [hFc]
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    rw [log_re, log_im]
    linarith [abs_arg_le_pi (LFunction χ w0)]
  -- Borel–Carathéodory
  set M : ℝ := Real.log B with hM
  have hM0 : 0 < M := Real.log_pos hB1
  set f' : ℂ → ℂ := fun z => F (w0 + z) with hf'
  have hmaps : MapsTo (fun z : ℂ => w0 + z) (ball 0 R) (ball w0 R) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    simpa using hz
  have hf'd : DifferentiableOn ℂ f' (ball 0 R) :=
    hFd.comp ((differentiableOn_const _).add differentiableOn_id) hmaps
  have hf'maps : MapsTo f' (ball 0 R) {z | z.re ≤ M} := fun z hz => hReF_le _ (hmaps hz)
  set z0 : ℂ := w - w0 with hz0
  have hz0eq : z0 = ((w.re - 4 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hz0, hw0, ht]
  have hz0norm : ‖z0‖ = 4 - w.re := by
    rw [hz0eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hz0mem : z0 ∈ ball (0:ℂ) R := by
    rw [mem_ball, dist_zero_right, hz0norm]
    linarith
  have hbc := Complex.borelCaratheodory hM0 hf'd hf'maps hRpos hz0mem
  have hf'z0 : f' z0 = F w := by simp [hf', hz0]
  have hf'0 : f' 0 = F w0 := by simp [hf']
  rw [hf'z0, hf'0] at hbc
  have harith := bc_arith (M := M) (a := ‖F w0‖) (z := ‖z0‖) (R := R) (d := d) hM0.le
    (norm_nonneg _) (norm_nonneg _) (by rw [hz0norm]; linarith) (by linarith) hd
    (by rw [hz0norm]; linarith)
  have hFw : ‖F w‖ ≤ 16 / d * (2 * M + c1) := by
    have : M + ‖F w0‖ ≤ 2 * M + c1 := by rw [hc1]; linarith
    calc ‖F w‖ ≤ 16 / d * (M + ‖F w0‖) := hbc.trans harith
      _ ≤ 16 / d * (2 * M + c1) := by gcongr
  -- back to `1/L`
  have hwmem : w ∈ ball w0 R := by
    have := hmaps hz0mem
    simpa [hz0] using this
  have hinv : ‖(LFunction χ w)⁻¹‖ = Real.exp (-(F w).re) := by
    rw [← hFexp w hwmem, ← Complex.exp_neg, Complex.norm_exp, neg_re]
  rw [hinv]
  have hexp : Real.exp (-(F w).re) ≤ Real.exp (16 / d * c1) * B ^ K := by
    have h1 : -(F w).re ≤ ‖F w‖ := by
      have := abs_re_le_norm (F w)
      linarith [neg_abs_le (F w).re]
    have h2 : Real.exp (16 / d * c1) * B ^ K = Real.exp (16 / d * (2 * M + c1)) := by
      rw [Real.rpow_def_of_pos hBpos, ← Real.exp_add, hK, hM]
      congr 1
      ring
    rw [h2]
    exact Real.exp_le_exp.mpr (h1.trans hFw)
  refine hexp.trans (le_of_eq ?_)
  rw [hB, Real.mul_rpow (by positivity) (by positivity), mul_assoc]

end RiemannLab
