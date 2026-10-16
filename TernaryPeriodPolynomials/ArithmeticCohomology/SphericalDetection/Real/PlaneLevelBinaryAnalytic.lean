module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneBinaryAnalytic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def RealPlaneLevelMixedAnalytic {index : Type} [Fintype index] (degree : ℕ)
    (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character)) : Prop :=
  ∀ radical : RealPlaneRadical, AnalyticAt ℝ (fun matrix : BinaryRealMatrix =>
    cuspidalTensorHilbertEmbedding cusp basis
      (cycle.val (SemidirectProduct.inr (invertibleMatrix matrix),
        SemidirectProduct.inl (realRadicalInverseLevi (invertibleMatrix matrix) radical))).val -
    cuspidalTensorHilbertEmbedding cusp basis
      (cycle.val (SemidirectProduct.inl radical, SemidirectProduct.inr (invertibleMatrix matrix))).val) 1

theorem realPlaneLevelMixedCocycle_analyticAt_one {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp trivialCharacter))
    (analytic : RealPlaneLevelMixedAnalytic degree cusp trivialCharacter basis cycle) (radical : RealPlaneRadical) :
    AnalyticAt ℝ (fun matrix : BinaryRealMatrix => cuspidalTensorHilbertEmbedding cusp basis
      (realPlaneMixedCocycle degree cusp (invertibleMatrix matrix)
        (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) radical)) 1 := by
  convert analytic radical using 1
  funext matrix
  let embedding : realPlaneCuspidalRep degree cusp trivialCharacter →ₗ[ℂ] (index → cusp.H) :=
    cuspidalTensorHilbertEmbedding cusp basis
  change embedding (realPlaneMixedCocycle degree cusp _ _ _) = _
  rw [realPlaneMixedCocycle_apply, map_sub]
  rfl

theorem realPlaneLevelBinaryCocycle_hilbert_analyticAt_one {index binaryIndex : Type} [Fintype index] [Fintype binaryIndex]
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter) (trivial : character = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (binaryBasis : Module.Basis binaryIndex ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle)
    (analytic : RealPlaneLevelMixedAnalytic degree cusp character basis cycle) :
    AnalyticAt ℝ (fun matrix : BinaryRealMatrix => binaryHilbertEmbedding cusp binaryBasis
      (realPlaneLevelBinaryCocycle degree cusp character trivial basis cycle regular (invertibleMatrix matrix))) 1 := by
  subst character
  have combined := realPlaneBinaryCochain_hilbert_analyticAt_one degree cusp basis binaryBasis
    (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle)
    (fun coordinate => realPlaneLevelMixedCocycle_analyticAt_one degree cusp basis cycle analytic (realRadicalAxis coordinate 1))
  convert combined using 1
  funext matrix
  exact binaryHilbertEmbedding_tensor cusp binaryBasis
    (realPlaneBinaryCochain degree cusp (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) (invertibleMatrix matrix))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
