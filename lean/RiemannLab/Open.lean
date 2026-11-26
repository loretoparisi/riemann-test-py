import RiemannLab.CombinedNorm
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# The combined equation: the parts Lean does NOT check

Everything in this file is a **statement only**. Each theorem below ends in `sorry`, so Lean
checks that the statement is well-typed and nothing else. `#print axioms` reports `sorryAx` for
each of them (see `Audit.lean`), and the Python bridge `python -m riemann_lab lean` fails if
any of the theorems in `CombinedNorm.lean` ever starts to depend on `sorryAx`.

* `grh_iff_finite_norm` is the GRH-equivalent half of the combined equation
  (Hardy–Littlewood 1918 for `ζ`, Garg–Maji 2022 for `χ`). Proving it in Lean would include
  proving nothing less than the equivalence, so it stays open.
* `blowup_limit` is the conditional corollary `(α - 3/4) ‖F_χ‖² → B_χ`, stated with all of
  its hypotheses (GRH, simple zeros, absolute convergence of the zero expansion) as explicit
  arguments. It is checked numerically in `riemann_lab.combined_checks.critical_blowup`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped LSeries.notation ArithmeticFunction.Moebius

noncomputable section

namespace RiemannLab

variable {N : ℕ}

/-- The Ramanujan–Hardy–Littlewood function `M_χ(x) = Σ μ(n) χ(n)/n · e^{-x/n²}`. -/
def M (χ : DirichletCharacter ℂ N) (x : ℝ) : ℂ :=
  ∑' n : ℕ, coef χ n * ((Real.exp (-(b n * x)) : ℝ) : ℂ)

/-- GRH for `χ`: every zero of `L(s, χ)` with `0 < Re s < 1` has `Re s = 1/2`. -/
def GRH (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → DirichletCharacter.LFunction χ ρ = 0 → ρ.re = 1 / 2

/-- The nontrivial zeros of `L(s, χ)`. -/
def zeros (χ : DirichletCharacter ℂ N) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ DirichletCharacter.LFunction χ ρ = 0}

/-- The weighted norm on the GRH-sensitive range: `∫₀^∞ |M_χ(x)|² x^{1-2α} dx`. -/
def normSq (χ : DirichletCharacter ℂ N) (α : ℝ) : ℝ :=
  ∫ x in Ioi (0:ℝ), ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α)

/-- **OPEN (sorry).** GRH-equivalent half of the combined equation: for a primitive
nontrivial `χ`, GRH holds iff the weighted norm of `M_χ` is finite for every `α ∈ (3/4, 1)`. -/
theorem grh_iff_finite_norm (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) :
    GRH χ ↔ ∀ α ∈ Ioo (3 / 4 : ℝ) 1,
      IntegrableOn (fun x : ℝ => ‖M χ x‖ ^ 2 * x ^ (1 - 2 * α)) (Ioi 0) := by
  sorry

/-- **OPEN (sorry), conditional.** The blow-up at the critical exponent, with all hypotheses
explicit: GRH, simple zeros, and absolute convergence of the zero expansion. Then
`(α - 3/4) · ‖F_χ‖²_{D⁺_α} → B_χ = (1/8) Σ_ρ |Γ((1-ρ)/2) / L'(ρ, χ)|²` as `α ↓ 3/4`. -/
theorem blowup_limit (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hGRH : GRH χ)
    (hsimple : ∀ ρ ∈ zeros χ, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0)
    (habs : Summable fun ρ : zeros χ =>
      ‖Gamma ((1 - (ρ : ℂ)) / 2) / deriv (DirichletCharacter.LFunction χ) ρ‖) :
    Tendsto (fun α : ℝ => (α - 3 / 4) * normSq χ α) (𝓝[>] (3 / 4))
      (𝓝 ((1 / 8) * ∑' ρ : zeros χ,
        ‖Gamma ((1 - (ρ : ℂ)) / 2) / deriv (DirichletCharacter.LFunction χ) ρ‖ ^ 2)) := by
  sorry

end RiemannLab
