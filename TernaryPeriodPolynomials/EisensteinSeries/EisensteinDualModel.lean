module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.ClassK

@[expose] public section


/-!
# The `Γ(N)` dual class in the rational cocycle model of `E*`

Formalized by Claude Sonnet 5.5.

The comparison map `dualClassK : H²(Γ(N), E^∨) → H²(Γ, E*)` (level descent / corestriction to `K†`, `E* = E ∘ φ`) carries `ȷ̃^* x` to the `φ`-transport of the `K†`-corestriction `classK x`; for
`x` mixed cuspidal at every plane cusp the maximal coordinates of the dual class satisfy the model form of `ar:eq:dualconstantterms` (inner coordinates, `r_P^∨ = T^∨ r_Q^∨`).  The gap to the `dual_constant_terms` (every inner line class of `E*`) is the adelic lift of `S(Γ(N))`.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.EisensteinDualModel

open TernaryPeriodPolynomials.Argument.EisensteinDual

alias dual_principal_subgroup := dualPrincipal
alias dual_class_to_model := dualClassK
alias dual_class_to_model_jpull := dualClassK_jPullC
alias dual_class_to_model_represented := classOf_phiCocycle_dualClassK
alias dual_model_constant_terms_gamma_n := dual_model_of_gammaN
alias dual_model_constant_terms_cusps := dual_model_of_cusps
alias dual_series_model_class := dualFormClassK
alias dual_series_model_class_eq := dualFormClassK_eq
alias transfer_phi_natural := trH2_phiH2
alias bridge_phi_natural := bridge_phiH2

end TernaryPeriodPolynomials.Argument.Statements.EisensteinDualModel
