module

public import TernaryPeriodPolynomials.AlternatingSolution.ModFour.Defs
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.AppendixDAssembly

@[expose] public section


/-! Target: the projector identities `mf:eq:projector` and `mf:eq:projected-exps` of
Appendix D. -/

open MvPolynomial

namespace TernaryPeriodPolynomials

open TernaryPeriodPolynomials.Argument

/-- **Appendix D, projector.** For symmetric `g`, `N̄ π g = 0` and `π g = g + Θ N̄ g`; and
`π(a²b), π(ab²), π(b³), π(b²c), π(ac²), π(bc²), π(c³), π(b⁵)` are `K₀, …, K₇`. -/
theorem normKernel_projector :
    (∀ g : Poly2, g.IsSymmetric →
      TernaryPoly.CharTwoNorm.norm (substitutionProjector g) = 0 ∧
      substitutionProjector g = g + thetaOperator (TernaryPoly.CharTwoNorm.norm g)) ∧
    ∀ j : Fin 8, substitutionProjector (projectedSource j) = TernaryPoly.CharTwoNorm.generator j := by
  exact TernaryPeriodPolynomials.Argument.CharTwoKernel.appendix_D_projector_proof

end TernaryPeriodPolynomials
