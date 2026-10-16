module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelBinaryCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.PlaneLevelCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realPlaneLevelRelativeArithmetic (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp trivialCharacter)) :
    relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree) :=
  ⟨realPlaneArithmeticCocycle degree cusp trivialCharacter cycle.val, by
    intro first second
    have evaluates := realPlaneArithmeticCocycle_apply degree cusp trivialCharacter cycle.val
      (identityPlaneRadicalInclusion first) (identityPlaneRadicalInclusion second)
    rw [identityPlaneRealGroup_radical, identityPlaneRealGroup_radical] at evaluates
    exact evaluates.trans (congrArg (fun values : realPlaneLevelCuspidalRep degree cusp trivialCharacter => values.val.val 1)
      (cycle.property (radicalLatticeReal first) (radicalLatticeReal second)))⟩

theorem realPlaneLevelBinaryCocycle_zero_arithmetic {index : Type} [Fintype index]
    (degree : ℕ) (positive : 0 < degree) (odd : Odd degree) (cusp : CuspidalRepresentation)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp trivialCharacter))
    (regular : RealPlaneLevelMixedRegular degree cusp trivialCharacter basis cycle)
    (zero : groupCohomology.H1π (binaryCuspidalRep cusp degree)
      (realPlaneLevelBinaryCocycle degree cusp trivialCharacter rfl basis cycle regular) = 0) :
    realPlaneArithmeticH2 degree cusp trivialCharacter (groupCohomology.H2π _ cycle.val) = 0 := by
  rw [realPlaneArithmeticH2_apply]
  apply realPlaneBinaryCocycle_zero_arithmetic degree positive odd cusp basis
    (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle)
    (realPlaneLevelMixedCocycle_differentiable degree cusp basis cycle regular)
    (fun first second => (cycle.val (first, second)).property)
    (realPlaneLevelRelativeArithmetic degree cusp cycle)
  · intro first second
    exact (realPlaneArithmeticCocycle_apply degree cusp trivialCharacter cycle.val first second).symm
  · exact zero

theorem realPlaneLevelBinaryCocycle_zero_arithmeticEdge {index : Type} [Fintype index]
    (degree : ℕ) (positive : 0 < degree) (odd : Odd degree) (cusp : CuspidalRepresentation)
    (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle)
    (zero : groupCohomology.H1π (binaryCuspidalRep cusp degree)
      (realPlaneLevelBinaryCocycle degree cusp character trivial basis cycle regular) = 0) :
    realPlaneLevelArithmeticBinaryEdge degree positive odd cusp character trivial (groupCohomology.H2π _ cycle.val) = 0 := by
  subst character
  change identityPlaneFullBinaryEdge degree positive odd
    (realPlaneArithmeticH2 degree cusp trivialCharacter (groupCohomology.H2π _ cycle.val)) = 0
  rw [realPlaneLevelBinaryCocycle_zero_arithmetic degree positive odd cusp basis cycle regular zero]
  exact (identityPlaneFullBinaryEdge degree positive odd).map_zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
