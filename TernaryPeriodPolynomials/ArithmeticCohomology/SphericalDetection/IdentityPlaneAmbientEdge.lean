module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IdentityPlaneRestriction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AmbientGroupH2

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def identityPlaneAmbientBinaryEdge (degree : ℕ) (positive : 0 < degree) (odd : Odd degree)
    (character : RankOneCharacter) (trivial : character = trivialCharacter) :
    cocycles (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
      (rationalCoefficientComponent degree character) →ₗ[ℂ]
        groupCohomology.H1 (arithmeticBinaryRep (degree + 1) (-1)) := by
  subst character
  exact (identityPlaneFullBinaryEdge degree positive odd).comp
    ((groupCohomology.H2π (identityPlaneCoefficientRep degree)).hom.comp
      (ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent degree trivialCharacter)))

theorem identityPlaneAmbientBinaryEdge_apply (degree : ℕ) (positive : 0 < degree) (odd : Odd degree)
    (cycle : cocycles (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
      (rationalCoefficientComponent degree trivialCharacter)) :
    identityPlaneAmbientBinaryEdge degree positive odd trivialCharacter rfl cycle =
      identityPlaneFullBinaryEdge degree positive odd
        (groupCohomology.H2π (identityPlaneCoefficientRep degree)
          (ambientCocycleToGroup (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
            (rationalCoefficientComponent degree trivialCharacter) cycle)) := rfl

/-- Detection applies to the original ambient homogeneous cochains, with the supplied character equality. -/
theorem identityPlaneAmbientBinaryEdge_zero_iff (degree : ℕ) (positive : 0 < degree) (odd : Odd degree)
    (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (cycle : cocycles (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
      (rationalCoefficientComponent degree character)) :
    identityPlaneAmbientBinaryEdge degree positive odd character trivial cycle = 0 ↔
      ∃ primitive, differentialOne (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
        (rationalCoefficientComponent degree character) primitive = cycle.val := by
  subst character
  exact (identityPlaneFullBinaryEdge_zero_iff degree positive odd _).trans
    (ambientCocycle_H2_zero_iff (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
      (rationalCoefficientComponent degree trivialCharacter) cycle)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
