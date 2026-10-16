module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Literal.Bijective
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.BadLineParabolic
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.GoodPlaneParabolic
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.BadPlaneParabolic

@[expose] public section


/-!
# The edge-map dictionary versus the Hochschild-Serre dictionary of `Face/*`

* Bad line (`badLineParabolic_eq_face`): the edge-map dictionary `-badLineEdge ∘ cuspRes false` is **minus** the
  Hochschild-Serre dictionary `Face.badLineLocallyInnerEquivParabolic` (mixed class of `radicalKernelMixedMap`, Kostant
  isomorphism, elimination of the unit factor); the two are definitionally equal up to the sign.
* Good plane (`goodPlaneParabolic_eq_face`) and identity plane (`badPlaneParabolic_eq_face`): `Face/*` defines its parabolic
  identifications at these faces by the same edge maps (`goodPlaneEdge`, `edgeH2`), so the dictionaries coincide by
  definition. This is NOT a comparison with the Hochschild-Serre composite (mixed class of `radicalKernelMixedMap`, then the
  plane Kostant coordinate); that comparison is `Literal.BadPlaneIdentification.badPlaneParabolic_eq_hs` and
  `Literal.GoodPlaneIdentification.goodPlaneParabolic_eq_hs`.
* Good line: not identified in this file (it is imported by the file that does it). `Face` realizes parabolic classes at
  the good line by the Hochschild-Serre inverse (`parabolicToGoodLine`), the library by the explicit edge `phiL`/`edgeK`;
  `Literal.GoodLineIdentification` proves that they agree with sign `+1` (`goodLineParabolic_eq_hs`). Bijectivity of the
  edge-map dictionary (`Literal.Bijective`) does not depend on it.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Spectral.CuspOrbits (cuspFlag cuspFlag_good_iff)
open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (parabolicCrossedH1)
open TernaryPeriodPolynomials.SphericalDetection.Helpers (arithmeticBinaryRep)
open TernaryPeriodPolynomials.LevelThree.TwoGenerator (parabolicH1)
open TernaryPeriodPolynomials.LevelThree.ParabolicBounds (levelRep)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.ArithmeticGenerators (upper lower)
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Face
open TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Literal

variable {n : ℕ}

/-- **Bad line.** The edge-map dictionary is minus the Hochschild-Serre dictionary
(`Face.badLineLocallyInnerEquivParabolic`, mixed class, Kostant isomorphism, elimination of the unit factor). -/
theorem badLineParabolic_eq_face (hn : 0 < n) (b : innerClasses n .line)
    (hx : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      standardBadLine b.val ∈ locallyInnerClasses n trivialCharacter .line standardBadLine) :
    ((badLineParabolic hn b : parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
        CrossedH1 (binaryArithmeticRepresentation n)) =
      -((badLineLocallyInnerEquivParabolic n hn ⟨_, hx⟩ :
        parabolicCrossedH1 (binaryArithmeticRepresentation n)) :
          CrossedH1 (binaryArithmeticRepresentation n)) := by
  rfl

/-- **Good plane.** The edge-map dictionary is the dictionary used for the dimension count in `Face/*`. -/
theorem goodPlaneParabolic_eq_face (hn : 0 < n) (ξ : innerClasses n .plane) :
    (↑(goodPlaneParabolic hn ξ) : CrossedH1 (levelRep (n + 1) (-1))) =
      (↑(goodPlaneLocallyInnerEquivParabolic n hn
        ⟨cuspRes n trivialCharacter .plane true ξ.val,
          innerBoundary_fixedPointH2_locallyInner ξ.property (cuspFlag .plane true)⟩) :
          CrossedH1 (levelRep (n + 1) (-1))) := rfl

/-- **Identity plane.** -/
theorem badPlaneParabolic_eq_face (hn : 0 < n) (hodd : Odd n) (ξ : innerClasses n .plane) :
    (↑(badPlaneParabolic hn hodd ξ) : groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))) =
      (↑(badPlaneLocallyInnerEquivParabolic n hn hodd
        ⟨cuspRes n trivialCharacter .plane false ξ.val,
          innerBoundary_fixedPointH2_locallyInner ξ.property (cuspFlag .plane false)⟩) :
          groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))) := rfl

end TernaryPeriodPolynomials.Argument.FacePairingFull.Literal
