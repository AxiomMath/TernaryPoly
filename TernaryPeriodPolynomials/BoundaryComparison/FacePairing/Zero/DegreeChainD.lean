module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Zero.DegreeChainC

@[expose] public section


/-!
# Degree-zero reconstruction, part D: the binary edge map and its injectivity

Steps 9-10 (`degree = 0` analogues of `goodLineBinaryEdge` and
`goodLineBinaryEdge_injective_of_invariant_H2_zero`).
-/

noncomputable section

open GeneralEisenstein Matrix CategoryTheory
open GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.Spectral.GoodLineLocalOp
open TernaryPeriodPolynomials.Spectral.LocalUniqueness
open TernaryPeriodPolynomials.Spectral.ModularH2

namespace TernaryPeriodPolynomials.Argument.FacePairing


/-- **Step 9.** `degree = 0` analogue of `goodLineBinaryEdge`. -/
def goodLineBinaryEdgeZero :
    (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRep 0)).ker →ₗ[ℂ]
      groupCohomology.H1 (arithmeticBinaryRep 1 0) :=
  goodLineLeviCohomologyIsoZero.hom.hom.comp
    (splitCohomologyEdge goodLineSplitting (goodLineCoefficientRep 0))

/-- **Step 10.** `degree = 0` analogue of `goodLineBinaryEdge_injective_of_invariant_H2_zero`,
specialized to `ModularH2.binaryH2_zero` directly (unconditional for every `ℂ`-representation of
`GL₂(ℤ)`, so no separate `vanishing` hypothesis is needed). -/
theorem goodLineBinaryEdgeZero_injective : Function.Injective goodLineBinaryEdgeZero :=
  (ConcreteCategory.bijective_of_isIso goodLineLeviCohomologyIsoZero.hom).injective.comp
    (splitCohomologyEdge_injective_of_invariant_H2_zero goodLineSplitting (goodLineCoefficientRep 0)
      (fun cohomology => binaryH2_zero _ cohomology))

end TernaryPeriodPolynomials.Argument.FacePairing
