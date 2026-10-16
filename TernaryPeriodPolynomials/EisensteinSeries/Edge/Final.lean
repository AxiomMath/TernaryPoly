module

public import TernaryPeriodPolynomials.EisensteinSeries.Edge.HasEisensteinClasses
public import TernaryPeriodPolynomials.EisensteinSeries.Edge.EisensteinRight

@[expose] public section


/-!
# Global Eisenstein classes in degree three, unconditionally

`EdgeEisensteinRight.edgeEisensteinOperator` supplies the right real equivariance of the Eisenstein
value at `s₀` in every degree, which was the only input of `hasEisensteinClasses_three`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein

open TernaryPeriodPolynomials.EisensteinGraph

variable {n : ℕ}

/-- **Global Eisenstein classes in degree three**, with no residual input. -/
theorem hasEisensteinClasses_three_unconditional (hn : n = 3) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (identity : ∀ x ∈ associatePair D, projection x = x) :
    GraphReduction.HasEisensteinClasses D projection :=
  hasEisensteinClasses_three hn D hol projection identity
    (EdgeEisensteinRight.edgeEisensteinOperator D hol)

end TernaryPeriodPolynomials.EdgeEisenstein
