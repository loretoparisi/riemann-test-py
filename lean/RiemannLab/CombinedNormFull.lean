import RiemannLab.MtBounds
import RiemannLab.Plancherel

/-!
# The combined norm identity with no hypothesis (`1 < α < 2`)

`combined_norm_identity` (in `CombinedNorm.lean`) took Mellin–Plancherel as the named hypothesis
`MellinPlancherel`. `Plancherel.lean` proves it for any `f` with `x^{c-1} f` and `x^{2c-1}|f|²`
integrable on `(0, ∞)`, and `MtBounds.lean` checks both conditions for `M̃_χ` when `-1 < c < 0`.
-/

open Complex MeasureTheory Set
open scoped LSeries.notation

noncomputable section

namespace RiemannLab

variable {N : ℕ}

/-- **Combined norm identity, no hypotheses (`1 < α < 2`).**
`∫₀^∞ |M̃_χ(x)|² x^{1-2α} dx = (1/2π) ∫_ℝ |Γ(s_t) / L(1 - 2 s_t, χ)|² dt`, `s_t = 1 - α + it`. -/
theorem combined_norm_identity_unconditional (χ : DirichletCharacter ℂ N) {α : ℝ} (h1 : 1 < α)
    (h2 : α < 2) :
    ∫ x in Ioi (0:ℝ), ‖Mt χ x‖ ^ 2 * x ^ (1 - 2 * α)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ,
          ‖Gamma ((1 - α : ℝ) + t * I) / LSeries ↗χ (1 - 2 * ((1 - α : ℝ) + t * I))‖ ^ 2 :=
  combined_norm_identity χ h1 h2
    (mellin_plancherel (mellinConvergent_Mt χ (by linarith) (by linarith))
      (mellinConvergent_Mt_sq χ (by linarith) (by linarith)))

end RiemannLab
