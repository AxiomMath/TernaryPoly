module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelBinaryCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.IntegralLevel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realPlaneLevelBinaryCocycle_finiteLevel {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle)
    (element : finiteIntegralGLLevel 2) (matrix : BinaryRealGL) :
    binaryRightTranslation cusp degree (atFinite element.val)
        (realPlaneLevelBinaryCocycle degree cusp character trivial basis cycle regular matrix) =
      realPlaneLevelBinaryCocycle degree cusp character trivial basis cycle regular matrix := by
  subst character
  obtain ⟨integral, integral_eq⟩ := element.property
  apply Subtype.ext
  funext argument
  change (realPlaneBinaryCochain degree cusp (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) matrix).val
      (argument * atFinite element.val) = _
  rw [← integral_eq]
  exact realPlaneBinaryCochain_finiteLevel degree cusp (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle)
    (fun first second => (cycle.val (first, second)).property) matrix integral argument

end TernaryPeriodPolynomials.SphericalDetection.Helpers
