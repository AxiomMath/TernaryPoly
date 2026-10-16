module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.InnerVanishing
public import TernaryPeriodPolynomials.SymmetricSpace.All.TopBoundaryPolynomial
public import TernaryPeriodPolynomials.Polynomial.PositiveInnerVanishing

@[expose] public section


/-! Direct composition of two existing library results:
`TernaryPoly.OrdinaryBoundaryActualEvaluation.ordinaryReferencePairwise_of_inner_vanishing`
applied to the already-discharged analytic gate
`TernaryPoly.SymmetricSpaceAllTopBoundary.positivePolynomialInnerVanishing`. -/

namespace TernaryPeriodPolynomials.Argument.Classification

theorem support_principle : TernaryPoly.ScalarGates.OrdinaryReferencePairwise :=
  TernaryPoly.OrdinaryBoundaryActualEvaluation.ordinaryReferencePairwise_of_inner_vanishing
    TernaryPoly.SymmetricSpaceAllTopBoundary.positivePolynomialInnerVanishing

end TernaryPeriodPolynomials.Argument.Classification
