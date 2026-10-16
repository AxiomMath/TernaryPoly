module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Zero.DegreeChainB

@[expose] public section


/-!
# Degree-zero reconstruction, part C: the Levi cohomology isomorphism

Step 8 alone (`degree = 0` analogue of `goodLineLeviCohomologyIso`).
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


/-- **Step 8.** `degree = 0` analogue of `goodLineLeviCohomologyIso`. -/
def goodLineLeviCohomologyIsoZero :
    groupCohomology.H1 (splitRadicalH1Representation goodLineSplitting (goodLineCoefficientRep 0)) ≅
      groupCohomology.H1 (arithmeticBinaryRep 1 0) :=
  (groupCohomology.functor ℂ (GeneralLinearGroup (Fin 2) ℤ) 1).mapIso goodLineRadicalCoordinateIsoZero

end TernaryPeriodPolynomials.Argument.FacePairing
