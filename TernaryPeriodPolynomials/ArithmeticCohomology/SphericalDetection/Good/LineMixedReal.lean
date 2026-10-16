module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineMixedCoordinate

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineRealVertices (pair : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) ×
    flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) : Fin 3 → RealGL3 :=
  fun index => GeneralLinearGroup.map (algebraMap ℚ ℝ) (![1, pair.1.val, pair.1.val * pair.2.val] index)

def goodLineRealGroupCochain (degree : ℕ) :
    ((Fin 3 → RealGL3) → HomogeneousPoly degree) →ₗ[ℂ]
      ((flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) ×
        flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine)) → goodLineCoefficientRep degree) where
  toFun values pair := values (goodLineRealVertices pair)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def goodLineMixedRealCoordinate (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    ((Fin 3 → RealGL3) → HomogeneousPoly degree) →ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  (goodLineMixedCoordinate degree matrix).comp (goodLineRealGroupCochain degree)

theorem goodLineMixedRealCoordinate_contributions (degree : ℕ) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (values : (Fin 3 → RealGL3) → HomogeneousPoly degree) :
    goodLineMixedRealCoordinate degree matrix values =
      lowerRadicalLatticeContribution degree 0
        (values (goodLineRealVertices (goodLineLeviSection matrix,
            goodLineRadicalInclusion (lowerLeviLatticeInput matrix radicalLatticeFirst))) -
          values (goodLineRealVertices (goodLineRadicalInclusion radicalLatticeFirst, goodLineLeviSection matrix))) +
      lowerRadicalLatticeContribution degree 1
        (values (goodLineRealVertices (goodLineLeviSection matrix,
            goodLineRadicalInclusion (lowerLeviLatticeInput matrix radicalLatticeSecond))) -
          values (goodLineRealVertices (goodLineRadicalInclusion radicalLatticeSecond, goodLineLeviSection matrix))) :=
  goodLineMixedCoordinate_contributions degree matrix (goodLineRealGroupCochain degree values)

theorem goodLineMixedRealCoordinate_correction (degree : ℕ) (positive : 0 < degree)
    (values : (Fin 3 → RealGL3) → HomogeneousPoly degree)
    (primitive : flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine) → goodLineCoefficientRep degree)
    (cycle : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep degree))
    (formula : ∀ pair, cycle.val pair = goodLineRealGroupCochain degree values pair -
      twoBoundaryCycle (goodLineCoefficientRep degree) primitive pair)
    (zero : ∀ matrix : GeneralLinearGroup (Fin 2) ℤ, goodLineBinaryEdgeCycle degree positive cycle matrix = 0)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    goodLineMixedRealCoordinate degree matrix values =
      goodLineMixedCoordinate degree matrix (fun pair => twoBoundaryCycle (goodLineCoefficientRep degree) primitive pair) :=
  goodLineMixedCoordinate_correction degree positive _ primitive cycle formula zero matrix

end TernaryPeriodPolynomials.SphericalDetection.Helpers
