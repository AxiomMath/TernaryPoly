module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlanePrimitiveExtension
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneMixedCocycles

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realPlaneLevelForgetCycle (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (cycle : groupCohomology.cocycles₂ (realPlaneLevelCuspidalRep degree cusp character)) :
    groupCohomology.cocycles₂ (realPlaneCuspidalRep degree cusp character) :=
  twoCocycleCoefficientMap _ _ (cuspidalTensorFiniteLevel cusp (HomogeneousPoly degree)).subtype (fun _ _ => rfl) cycle

def realPlaneLevelForgetRelative (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character)) :
    relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp character) :=
  ⟨realPlaneLevelForgetCycle degree cusp character cycle.val, by
    intro first second
    exact congrArg Subtype.val (cycle.property first second)⟩

theorem realPlaneLevelForgetRelative_apply (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character)) (first second : RealPlaneGroup) :
    (realPlaneLevelForgetRelative degree cusp character cycle).val (first, second) = (cycle.val (first, second)).val := rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
