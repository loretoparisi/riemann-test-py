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
#print axioms RiemannLab.plancherel
#print axioms RiemannLab.mellin_plancherel
#print axioms RiemannLab.combined_norm_identity_unconditional
#print axioms RiemannLab.mellinOn_differentiableAt
#print axioms RiemannLab.K_mul_LFunction_eq
#print axioms RiemannLab.LFunction_ne_zero_of_finiteNorms
#print axioms RiemannLab.grh_of_finiteNorms
#print axioms RiemannLab.norm_LFunction_le
#print axioms RiemannLab.LFunction_inv_conj
#print axioms RiemannLab.norm_inv_LFunction_le
#print axioms RiemannLab.integral_vertical_eq
#print axioms RiemannLab.integrableOn_weighted_of_mellinInv
#print axioms RiemannLab.fM_eq_mellinInv
#print axioms RiemannLab.finiteNorms_of_GRH
#print axioms RiemannLab.grh_of_finiteNorms'
#print axioms RiemannLab.grh_iff_finite_norm
#print axioms RiemannLab.tendsto_psiχ_div
#print axioms RiemannLab.tendsto_Mμ_div
#print axioms RiemannLab.norm_LFunction_one_sub_Sχ_le
#print axioms RiemannLab.tendsto_sum_mu_div
#print axioms RiemannLab.tendsto_M_partial
#print axioms RiemannLab.blowup_limit
