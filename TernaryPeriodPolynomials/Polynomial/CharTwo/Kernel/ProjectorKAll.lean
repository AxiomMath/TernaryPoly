module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.ProjectorKOneToSix

@[expose] public section





open MvPolynomial TernaryPoly.CharTwoNorm

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

/-- Assembly of the eight concrete identities into the universally-quantified second
conjunct of `normKernel_projector`. -/
theorem projector_K_all :
    ∀ j : Fin 8, substitutionProjector (projectedSource j) = TernaryPoly.CharTwoNorm.generator j := by
  intro j
  fin_cases j
  · exact projector_K0
  · exact projector_K1
  · exact projector_K2
  · exact projector_K3
  · exact projector_K4
  · exact projector_K5
  · exact projector_K6
  · exact projector_K7

end TernaryPeriodPolynomials.Argument.CharTwoKernel
