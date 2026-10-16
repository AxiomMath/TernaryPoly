module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.LowerRadicalEdgeFormula
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.CochainCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem lowerRadicalCocycleCoordinate_oneBoundary (degree : ℕ) (positive : 0 < degree)
    (potential : HomogeneousPoly degree) :
    lowerRadicalCocycleCoordinate degree (oneBoundaryCycle (lowerRadicalLatticeRep degree) potential) = 0 :=
  (lowerRadicalCocycleCoordinate_zero_iff positive _).mpr (oneBoundaryCycle_H1_zero _ _)

/-- Extend only the restriction of the supplied good-line primitive to the radical. -/
def goodLineRadicalPrimitiveExtension (degree : ℕ)
    (primitive : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep degree) :
    flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep degree :=
  fun element => primitive (goodLineRadicalInclusion (splitRadicalCoordinate goodLineSplitting element))

theorem goodLineRadicalPrimitiveExtension_inl (degree : ℕ)
    (primitive : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep degree)
    (radical : RadicalLattice) :
    goodLineRadicalPrimitiveExtension degree primitive (goodLineRadicalInclusion radical) =
      primitive (goodLineRadicalInclusion radical) := by
  unfold goodLineRadicalPrimitiveExtension
  exact congrArg (fun element => primitive (goodLineRadicalInclusion element))
    (splitRadicalCoordinate_inl goodLineSplitting radical)

/-- The supplied boundary, corrected on radical pairs by the same primitive. -/
def goodLineBoundaryRelativeCycle (degree : ℕ)
    (primitive : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep degree) :
    relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree) :=
  relativeBoundaryOfRestriction goodLineRadicalInclusion (goodLineCoefficientRep degree)
    (primitive - goodLineRadicalPrimitiveExtension degree primitive) 0 (by
      intro radical
      change primitive (goodLineRadicalInclusion radical) -
        goodLineRadicalPrimitiveExtension degree primitive (goodLineRadicalInclusion radical) = 0
      rw [goodLineRadicalPrimitiveExtension_inl, sub_self])

theorem goodLineBoundaryRelativeCycle_value (degree : ℕ)
    (primitive : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep degree) :
    (goodLineBoundaryRelativeCycle degree primitive).val =
      twoBoundaryCycle (goodLineCoefficientRep degree) primitive -
        twoBoundaryCycle (goodLineCoefficientRep degree) (goodLineRadicalPrimitiveExtension degree primitive) := by
  apply Subtype.ext
  funext pair
  change (goodLineCoefficientRep degree).ρ pair.1 (primitive pair.2 - goodLineRadicalPrimitiveExtension degree primitive pair.2) -
      (primitive (pair.1 * pair.2) - goodLineRadicalPrimitiveExtension degree primitive (pair.1 * pair.2)) +
      (primitive pair.1 - goodLineRadicalPrimitiveExtension degree primitive pair.1) =
    ((goodLineCoefficientRep degree).ρ pair.1 (primitive pair.2) - primitive (pair.1 * pair.2) + primitive pair.1) -
      ((goodLineCoefficientRep degree).ρ pair.1 (goodLineRadicalPrimitiveExtension degree primitive pair.2) -
        goodLineRadicalPrimitiveExtension degree primitive (pair.1 * pair.2) + goodLineRadicalPrimitiveExtension degree primitive pair.1)
  rw [map_sub]
  abel

theorem goodLineBoundaryRelativeCycle_H2_zero (degree : ℕ)
    (primitive : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep degree) :
    groupCohomology.H2π (goodLineCoefficientRep degree) (goodLineBoundaryRelativeCycle degree primitive).val = 0 :=
  relativeBoundaryOfRestriction_H2_zero _ _ _ _ _

/-- After the radical correction, every binary edge value of the supplied boundary is zero. -/
theorem goodLineBoundaryRelativeCycle_edge_zero (degree : ℕ) (positive : 0 < degree)
    (primitive : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep degree)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineBinaryEdgeCycle degree positive (goodLineBoundaryRelativeCycle degree primitive) matrix = 0 := by
  rw [goodLineBinaryEdgeCycle_apply]
  have identity := splitEdgeCycle_relativeBoundary goodLineSplitting (goodLineCoefficientRep degree)
    (primitive - goodLineRadicalPrimitiveExtension degree primitive) 0 (by
      intro radical
      change primitive (goodLineRadicalInclusion radical) -
        goodLineRadicalPrimitiveExtension degree primitive (goodLineRadicalInclusion radical) = 0
      rw [goodLineRadicalPrimitiveExtension_inl, sub_self]) matrix
  rw [map_zero, sub_zero] at identity
  have projected := congrArg (lowerRadicalCocycleCoordinate degree) identity
  change lowerRadicalCocycleCoordinate degree
      (goodLineRadicalEdgeCycle degree (goodLineBoundaryRelativeCycle degree primitive) matrix) =
    lowerRadicalCocycleCoordinate degree (0 - oneBoundaryCycle (lowerRadicalLatticeRep degree)
      ((primitive - goodLineRadicalPrimitiveExtension degree primitive) (goodLineLeviSection matrix))) at projected
  rw [map_sub, map_zero] at projected
  exact projected.trans ((congrArg (fun value : Binary.HomogeneousPoly (degree + 1) => 0 - value)
    (lowerRadicalCocycleCoordinate_oneBoundary degree positive
      ((primitive - goodLineRadicalPrimitiveExtension degree primitive) (goodLineLeviSection matrix)))).trans (sub_self _))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
