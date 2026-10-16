module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineBoundaryNormalization
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AmbientGroupH2

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineHomogeneousPrimitive (degree : ℕ) (character : RankOneCharacter)
    (trivial : character = trivialCharacter)
    (primitive : cochains (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent degree character) 1) :
    flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep degree := by
  subst character
  exact fun element => primitive.val ![1, element.val]

theorem goodLineHomogeneousPrimitive_boundary (degree : ℕ) (character : RankOneCharacter)
    (trivial : character = trivialCharacter)
    (primitive : cochains (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent degree character) 1)
    (first second : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) :
    twoBoundaryCycle (goodLineCoefficientRep degree)
        (goodLineHomogeneousPrimitive degree character trivial primitive) (first, second) =
      (differentialOne (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent degree character) primitive).val ![1, first.val, first.val * second.val] := by
  subst character
  have equivariant := homogeneousOneCochain_equivariant
    (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
    (rationalCoefficientComponent degree trivialCharacter) primitive first 1 second.val
  rw [mul_one] at equivariant
  change rationalCoefficientComponent degree trivialCharacter first.val (primitive.val ![1, second.val]) -
      primitive.val ![1, first.val * second.val] + primitive.val ![1, first.val] =
    primitive.val ![first.val, first.val * second.val] -
      primitive.val ![1, first.val * second.val] + primitive.val ![1, first.val]
  rw [equivariant]

/-- The actual homogeneous coboundary gives an explicit radical-corrected target with zero binary edge. -/
theorem goodLineHomogeneousBoundary_exists_relative (degree : ℕ) (positive : 0 < degree)
    (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (cochain : (Fin 3 → RationalGL3) → goodLineCoefficientRep degree)
    (primitive : cochains (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent degree character) 1)
    (boundary : ∀ vertices, cochain vertices =
      (differentialOne (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
        (rationalCoefficientComponent degree character) primitive).val vertices) :
    ∃ (radical_primitive : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep degree)
      (relative : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree)),
      (∀ element, radical_primitive element =
        goodLineHomogeneousPrimitive degree character trivial primitive
          (goodLineRadicalInclusion (splitRadicalCoordinate goodLineSplitting element))) ∧
      (∀ first second : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine),
        relative.val (first, second) = cochain ![1, first.val, first.val * second.val] -
          ((goodLineCoefficientRep degree).ρ first (radical_primitive second) -
            radical_primitive (first * second) + radical_primitive first)) ∧
      ∀ matrix : GeneralLinearGroup (Fin 2) ℤ, goodLineBinaryEdgeCycle degree positive relative matrix = 0 := by
  let group_primitive := goodLineHomogeneousPrimitive degree character trivial primitive
  refine ⟨goodLineRadicalPrimitiveExtension degree group_primitive,
    goodLineBoundaryRelativeCycle degree group_primitive, fun _ => rfl, ?_,
    goodLineBoundaryRelativeCycle_edge_zero degree positive group_primitive⟩
  intro first second
  have value := congrArg (fun cycle : groupCohomology.cocycles₂ (goodLineCoefficientRep degree) => cycle (first, second))
    (goodLineBoundaryRelativeCycle_value degree group_primitive)
  change (goodLineBoundaryRelativeCycle degree group_primitive).val (first, second) =
    twoBoundaryCycle (goodLineCoefficientRep degree) group_primitive (first, second) -
      twoBoundaryCycle (goodLineCoefficientRep degree)
        (goodLineRadicalPrimitiveExtension degree group_primitive) (first, second) at value
  have actual := (goodLineHomogeneousPrimitive_boundary degree character trivial primitive first second).trans
    (boundary ![1, first.val, first.val * second.val]).symm
  exact value.trans (congrArg (fun polynomial : goodLineCoefficientRep degree => polynomial -
    twoBoundaryCycle (goodLineCoefficientRep degree)
      (goodLineRadicalPrimitiveExtension degree group_primitive) (first, second)) actual)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
