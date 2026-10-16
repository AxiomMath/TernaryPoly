module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Split.MixedNormalForm
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelBinaryAnalytic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realPlaneLevelMixedValue_normalize (degree : ℕ) (cusp : CuspidalRepresentation)
    (character : RankOneCharacter)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character)) (matrix : BinaryRealGL) (radical : RealPlaneRadical) :
    let normalized := splitMixedNormalize realPlaneSplitting (realPlaneLevelCuspidalRep degree cusp character) cycle
    (normalized.val (SemidirectProduct.inr matrix,
        SemidirectProduct.inl (realRadicalInverseLevi matrix radical))).val -
      (normalized.val (SemidirectProduct.inl radical, SemidirectProduct.inr matrix)).val =
    (cycle.val (SemidirectProduct.inr matrix,
        SemidirectProduct.inl (realRadicalInverseLevi matrix radical))).val -
      (cycle.val (SemidirectProduct.inl radical, SemidirectProduct.inr matrix)).val := by
  have equality := congrArg (fun value : groupCohomology.cocycles₁
      (Rep.res (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
        (realPlaneLevelCuspidalRep degree cusp character)) => (value radical).val)
    (splitMixedNormalize_edge realPlaneSplitting (realPlaneLevelCuspidalRep degree cusp character) cycle matrix)
  simp only [splitEdgeCycle_apply, realPlaneSplitting_input] at equality
  exact equality

theorem realPlaneLevelMixedRegular_normalize {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle) :
    RealPlaneLevelMixedRegular degree cusp character basis
      (splitMixedNormalize realPlaneSplitting (realPlaneLevelCuspidalRep degree cusp character) cycle) := by
  let : AddCommGroup (cuspidalTensorValues cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues cusp (HomogeneousPoly degree)).addCommGroup
  intro matrix
  have equality (radical : RealPlaneRadical) := congrArg (cuspidalTensorHilbertEmbedding cusp basis)
    (realPlaneLevelMixedValue_normalize degree cusp character cycle matrix radical)
  simp only [map_sub] at equality
  convert regular matrix using 1
  funext point
  exact equality (Multiplicative.ofAdd point)

theorem realPlaneLevelMixedAnalytic_normalize {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (analytic : RealPlaneLevelMixedAnalytic degree cusp character basis cycle) :
    RealPlaneLevelMixedAnalytic degree cusp character basis
      (splitMixedNormalize realPlaneSplitting (realPlaneLevelCuspidalRep degree cusp character) cycle) := by
  let : AddCommGroup (cuspidalTensorValues cusp (HomogeneousPoly degree)) :=
    (cuspidalTensorValues cusp (HomogeneousPoly degree)).addCommGroup
  intro radical
  have equality (matrix : BinaryRealGL) := congrArg (cuspidalTensorHilbertEmbedding cusp basis)
    (realPlaneLevelMixedValue_normalize degree cusp character cycle matrix radical)
  simp only [map_sub] at equality
  convert analytic radical using 1
  funext matrix
  exact equality (invertibleMatrix matrix)

theorem realPlaneLevelMixedCocycle_normalize (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp trivialCharacter)) (matrix : BinaryRealGL) :
    realPlaneMixedCocycle degree cusp matrix
        (realPlaneLevelForgetRelative degree cusp trivialCharacter
          (splitMixedNormalize realPlaneSplitting (realPlaneLevelCuspidalRep degree cusp trivialCharacter) cycle)) =
      realPlaneMixedCocycle degree cusp matrix (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) := by
  apply groupCohomology.cocycles₁_ext
  intro radical
  rw [realPlaneMixedCocycle_apply, realPlaneMixedCocycle_apply]
  simp only [realPlaneLevelForgetRelative_apply]
  exact realPlaneLevelMixedValue_normalize degree cusp trivialCharacter cycle matrix radical

theorem realPlaneLevelBinaryCocycle_normalize {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (trivial : character = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle) :
    realPlaneLevelBinaryCocycle degree cusp character trivial basis
        (splitMixedNormalize realPlaneSplitting (realPlaneLevelCuspidalRep degree cusp character) cycle)
        (realPlaneLevelMixedRegular_normalize degree cusp character basis cycle regular) =
      realPlaneLevelBinaryCocycle degree cusp character trivial basis cycle regular := by
  subst character
  apply groupCohomology.cocycles₁_ext
  intro matrix
  apply Subtype.ext
  funext argument
  change (realPlaneBinaryCochain degree cusp
      (realPlaneLevelForgetRelative degree cusp trivialCharacter
        (splitMixedNormalize realPlaneSplitting (realPlaneLevelCuspidalRep degree cusp trivialCharacter) cycle))
      matrix).val argument =
    (realPlaneBinaryCochain degree cusp (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) matrix).val argument
  rw [realPlaneBinaryCochain, realPlaneLevelMixedCocycle_normalize]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
