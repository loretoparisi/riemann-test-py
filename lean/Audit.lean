import RiemannLab

/-! Axiom audit, parsed by `python -m riemann_lab lean`. Proved theorems must depend only on
`propext`, `Classical.choice` and `Quot.sound`; the open ones show `sorryAx`. -/

#print axioms RiemannLab.mellin_g
#print axioms RiemannLab.integrableOn_g_norm
#print axioms RiemannLab.scale_identity
#print axioms RiemannLab.integral_norm_F
#print axioms RiemannLab.mellin_Mt_eq_LSeries
#print axioms RiemannLab.mellin_Mt
#print axioms RiemannLab.combined_norm_identity
#print axioms RiemannLab.grh_iff_finite_norm
#print axioms RiemannLab.blowup_limit
