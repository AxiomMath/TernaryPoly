module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperBinaryCorrection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelBinaryAnalytic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def realPlaneLevelBinaryCorrection
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (trivial : character = trivialCharacter)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character)) (matrix : BinaryRealGL) :
    realPlaneLevelCuspidalRep degree cusp character := by
  subst character
  refine ⟨realUpperBinaryCorrection degree cusp
    (realPlaneMixedCocycle degree cusp matrix (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle)), ?_⟩
  apply realUpperBinaryCorrection_finiteLevel
  · exact realPlaneMixedCocycle_finiteLevel degree cusp _ (fun first second => (cycle.val (first, second)).property) matrix _
  · exact realPlaneMixedCocycle_finiteLevel degree cusp _ (fun first second => (cycle.val (first, second)).property) matrix _
  · exact realPlaneBinaryCochain_finiteLevel degree cusp _ (fun first second => (cycle.val (first, second)).property) matrix

theorem realPlaneLevelBinaryCorrection_normal {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp trivialCharacter))
    (regular : RealPlaneLevelMixedRegular degree cusp trivialCharacter basis cycle) (matrix : BinaryRealGL) :
    realPlaneMixedCocycle degree cusp matrix (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) =
      realUpperCuspidalBinarySection degree cusp
          (realPlaneBinaryCochain degree cusp (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) matrix) +
        oneBoundaryCycle (realUpperCuspidalRep degree cusp)
          (realPlaneLevelBinaryCorrection degree cusp trivialCharacter rfl cycle matrix).val :=
  realUpperBinaryCorrection_normal degree cusp basis _
    (realPlaneLevelMixedCocycle_differentiable degree cusp basis cycle regular matrix)

theorem realPlaneLevelBinaryCorrection_one
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (trivial : character = trivialCharacter)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character)) :
    realPlaneLevelBinaryCorrection degree cusp character trivial cycle 1 = 0 := by
  subst character
  apply Subtype.ext
  change realUpperBinaryCorrection degree cusp
    (realPlaneMixedCocycle degree cusp 1 (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle)) = 0
  have zero : realPlaneMixedCocycle degree cusp 1 (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) = 0 := by
    change realPlaneRadicalCocycle degree cusp
      (splitEdgeCycle realPlaneSplitting (realPlaneCuspidalRep degree cusp trivialCharacter) 1 _) = 0
    rw [splitEdgeCycle_one, map_zero]
  rw [zero, realUpperBinaryCorrection_zero]

theorem realPlaneLevelBinaryCorrection_analyticAt_one {index binaryIndex : Type}
    [Fintype index] [Fintype binaryIndex]
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (trivial : character = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (binaryBasis : Module.Basis binaryIndex ℂ (Binary.HomogeneousPoly (degree + 1)))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (analytic : RealPlaneLevelMixedAnalytic degree cusp character basis cycle) :
    AnalyticAt ℝ (fun matrix : BinaryRealMatrix => cuspidalTensorHilbertEmbedding cusp basis
      (realPlaneLevelBinaryCorrection degree cusp character trivial cycle (invertibleMatrix matrix)).val) 1 := by
  subst character
  let relative := realPlaneLevelForgetRelative degree cusp trivialCharacter cycle
  let family (matrix : BinaryRealMatrix) :=
    realPlaneMixedCocycle degree cusp (invertibleMatrix matrix) relative -
      realUpperCuspidalBinarySection degree cusp (realPlaneBinaryCochain degree cusp relative (invertibleMatrix matrix))
  have binary_analytic := realPlaneBinaryCochain_hilbert_analyticAt_one degree cusp basis binaryBasis relative
    (fun coordinate => realPlaneLevelMixedCocycle_analyticAt_one degree cusp basis cycle analytic (realRadicalAxis coordinate 1))
  have regular (radical : RealPlaneRadical) : AnalyticAt ℝ
      (fun matrix : BinaryRealMatrix => cuspidalTensorHilbertEmbedding cusp basis (family matrix radical)) 1 := by
    let linear := cuspidalTensorHilbertMap cusp binaryBasis basis (realUpperBinaryValue degree radical)
    have section_analytic := ((linear.restrictScalars ℝ).analyticAt _).comp binary_analytic
    have mixed_analytic := realPlaneLevelMixedCocycle_analyticAt_one degree cusp basis cycle analytic radical
    convert mixed_analytic.sub section_analytic using 1
    funext matrix
    change cuspidalTensorHilbertEmbedding cusp basis
        (realPlaneMixedCocycle degree cusp (invertibleMatrix matrix) relative radical -
          realUpperCuspidalBinarySection degree cusp
            (realPlaneBinaryCochain degree cusp relative (invertibleMatrix matrix)) radical) = _
    refine (map_sub (cuspidalTensorHilbertEmbedding cusp basis) _ _).trans ?_
    exact congrArg (fun vector => cuspidalTensorHilbertEmbedding cusp basis
      (realPlaneMixedCocycle degree cusp (invertibleMatrix matrix) relative radical) - vector)
        (cuspidalTensorHilbertMap_embedding cusp binaryBasis basis (realUpperBinaryValue degree radical) _).symm
  exact realUpperBoundaryPotential_analyticAt degree cusp basis family 1
    (regular (radicalLatticeReal radicalLatticeFirst)) (regular (radicalLatticeReal radicalLatticeSecond))

theorem realPlaneLevelBinaryCorrection_value {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (character : RankOneCharacter)
    (trivial : character = trivialCharacter) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp character))
    (regular : RealPlaneLevelMixedRegular degree cusp character basis cycle)
    (matrix : BinaryRealGL) (radical : RealPlaneRadical) (argument : BinaryAdelicGL) :
    (cycle.val (SemidirectProduct.inr matrix,
        SemidirectProduct.inl (realRadicalInverseLevi matrix radical))).val.val argument -
      (cycle.val (SemidirectProduct.inl radical, SemidirectProduct.inr matrix)).val.val argument =
      realUpperBinaryValue degree radical
          ((realPlaneLevelBinaryCocycle degree cusp character trivial basis cycle regular matrix).val argument) +
        ((realUpperRadicalRep degree).ρ radical
            ((realPlaneLevelBinaryCorrection degree cusp character trivial cycle matrix).val.val argument) -
          (realPlaneLevelBinaryCorrection degree cusp character trivial cycle matrix).val.val argument) := by
  subst character
  have value := congrArg (fun cocycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp) =>
    (cocycle radical).val argument) (realPlaneLevelBinaryCorrection_normal degree cusp basis cycle regular matrix)
  change (realPlaneMixedCocycle degree cusp matrix
      (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) radical).val argument =
    realUpperBinaryValue degree radical
        ((realPlaneBinaryCochain degree cusp (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) matrix).val argument) +
      ((realUpperRadicalRep degree).ρ radical
        ((realPlaneLevelBinaryCorrection degree cusp trivialCharacter rfl cycle matrix).val.val argument) -
        (realPlaneLevelBinaryCorrection degree cusp trivialCharacter rfl cycle matrix).val.val argument) at value
  rw [realPlaneMixedCocycle_apply] at value
  exact value

end TernaryPeriodPolynomials.SphericalDetection.Helpers
