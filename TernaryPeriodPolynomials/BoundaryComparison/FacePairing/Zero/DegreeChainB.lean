module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairing.Zero.DegreeChain

@[expose] public section


/-!
# Degree-zero reconstruction, part B: the radical/Levi coordinate isomorphism

See `ZeroDegreeChainC.lean`, `ZeroDegreeChainD.lean`, `ZeroDegreeChainE.lean` for the remaining
steps.
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


/-- **Step 7.** `degree = 0` analogue of `goodLineRadicalCoordinateIso`. -/
def goodLineRadicalCoordinateIsoZero :
    splitRadicalH1Representation goodLineSplitting (goodLineCoefficientRep 0) ≅
      arithmeticBinaryRep 1 0 :=
  Rep.mkIso (Representation.Equiv.mk lowerRadicalH1CoordinateZero (by
    intro matrix
    apply LinearMap.ext
    intro cohomology
    change groupCohomology.H1 (lowerRadicalLatticeRep 0) at cohomology
    change lowerRadicalH1CoordinateZero
        (splitRadicalH1Action goodLineSplitting (goodLineCoefficientRep 0) matrix cohomology) =
      Binary.homogeneousAction 1 0 (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (lowerRadicalH1CoordinateZero cohomology)
    rw [goodLineSplitH1Action]
    exact lowerRadicalH1CoordinateZero_equivariant matrix cohomology))

end TernaryPeriodPolynomials.Argument.FacePairing
