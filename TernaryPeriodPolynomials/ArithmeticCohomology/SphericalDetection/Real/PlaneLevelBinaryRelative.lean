module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneBinaryRelativeClass

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {index : Type} [Fintype index]

def realPlaneLevelBinaryRelativeCycle
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (trivial : character = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle) :
    relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp character) := by
  subst character
  exact realPlaneBinaryRelativeCycle degree cusp basis
    (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle)
    (realPlaneLevelMixedCocycle_differentiable degree cusp basis cycle regular)

theorem realPlaneLevelBinaryRelativeCycle_apply
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (trivial : character = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle)
    (first second : RealPlaneGroup) (argument : BinaryAdelicGL) :
    ((realPlaneLevelBinaryRelativeCycle degree cusp character trivial basis cycle regular).val (first, second)).val argument =
      (realUpperRadicalRep degree).ρ first.left
        (realUpperBinaryValue degree (realPlaneRadicalAction first.right second.left)
          ((realPlaneLevelBinaryCocycle degree cusp character trivial basis cycle regular first.right).val argument)) := by
  subst character
  change ((realPlaneCuspidalRep degree cusp trivialCharacter).ρ (SemidirectProduct.inl first.left)
    (realUpperCuspidalBinarySection degree cusp
      (realPlaneBinaryCochain degree cusp (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) first.right)
      (realPlaneRadicalAction first.right second.left))).val argument = _
  exact congrArg (fun values : cuspidalTensorValues cusp (HomogeneousPoly degree) => values.val argument)
    (realPlaneCuspidalRep_radical degree cusp first.left _)

theorem realPlaneLevelBinaryRelativeCycle_H2
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (trivial : character = trivialCharacter)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle) :
    groupCohomology.H2π (realPlaneCuspidalRep degree cusp character)
        (realPlaneLevelBinaryRelativeCycle degree cusp character trivial basis cycle regular).val =
      groupCohomology.H2π (realPlaneCuspidalRep degree cusp character)
        (realPlaneLevelForgetRelative degree cusp character cycle).val := by
  subst character
  exact realPlaneBinaryRelativeCycle_H2 degree cusp central_positive basis
    (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle)
    (realPlaneLevelMixedCocycle_differentiable degree cusp basis cycle regular)

theorem realPlaneLevelBinaryRelativeCycle_exists_primitive
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (trivial : character = trivialCharacter)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle) :
    ∃ primitive : RealPlaneGroup → cuspidalTensorValues cusp (HomogeneousPoly degree),
      (realPlaneLevelForgetRelative degree cusp character cycle).val =
        (realPlaneLevelBinaryRelativeCycle degree cusp character trivial basis cycle regular).val +
          twoBoundaryCycle (realPlaneCuspidalRep degree cusp character) primitive := by
  subst character
  exact realPlaneBinaryRelativeCycle_exists_primitive degree cusp central_positive basis
    (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle)
    (realPlaneLevelMixedCocycle_differentiable degree cusp basis cycle regular)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
