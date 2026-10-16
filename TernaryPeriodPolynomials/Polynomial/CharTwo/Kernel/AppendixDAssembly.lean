module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.Identity.A
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.Identity.B

@[expose] public section


open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

/-- Assembly of both conjuncts of `normKernel_projector`: the norm/projector identity
(`projector_norm_zero` from Identity A together with `projector_eq_g_add_theta_norm` from
Identity B) for every symmetric `g`, paired with the eight concrete `projector_K_all`
identities. -/
theorem appendix_D_projector_proof :
    (∀ g : Poly2, g.IsSymmetric →
      TernaryPoly.CharTwoNorm.norm (substitutionProjector g) = 0 ∧
      substitutionProjector g = g + thetaOperator (TernaryPoly.CharTwoNorm.norm g)) ∧
    ∀ j : Fin 8, substitutionProjector (projectedSource j) = TernaryPoly.CharTwoNorm.generator j :=
  ⟨fun _g hg => ⟨projector_norm_zero hg, projector_eq_g_add_theta_norm hg⟩, projector_K_all⟩

end TernaryPeriodPolynomials.Argument.CharTwoKernel
