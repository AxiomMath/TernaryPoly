module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperBinaryLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelBinaryCocycle

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realUpperCuspidalBinarySection_levi (degree : ℕ) (cusp : CuspidalRepresentation)
    (matrix : BinaryRealGL)
    (values transformed : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)))
    (action : transformed.val = binaryCohomologicalAction degree matrix values.val) :
    realUpperCuspidalCocycleLevi degree cusp matrix (realUpperCuspidalBinarySection degree cusp values) =
      realUpperCuspidalBinarySection degree cusp transformed := by
  apply groupCohomology.cocycles₁_ext
  intro element
  apply Subtype.ext
  funext argument
  rw [realUpperCuspidalCocycleLevi_apply, realUpperCuspidalBinarySection_apply,
    realUpperCuspidalBinarySection_apply]
  change normPower (GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
      realCoefficientComponent degree trivialCharacter (planeLevi matrix 1)
        (realUpperBinaryValue degree (realRadicalInverseLevi matrix element) (values.val (argument * atInfinity matrix))) =
    realUpperBinaryValue degree element (transformed.val argument)
  rw [action]
  change _ = realUpperBinaryValue degree element
    (normPower (GeneralLinearGroup.det (atInfinity matrix)) (((degree : ℂ) + 3) / 2) •
      Binary.homogeneousAction (degree + 1) (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) matrix)
        (values.val (argument * atInfinity matrix)))
  rw [map_smul, realUpperBinaryValue_levi]

theorem realPlaneBinarySection_cocycle {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (regular : ∀ matrix coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
        (realPlaneMixedCocycle degree cusp matrix cycle (realRadicalAxis coordinate parameter))) 0)
    (first second : BinaryRealGL) :
    realUpperCuspidalBinarySection degree cusp (realPlaneBinaryCochain degree cusp cycle (first * second)) =
      realUpperCuspidalCocycleLevi degree cusp first
          (realUpperCuspidalBinarySection degree cusp (realPlaneBinaryCochain degree cusp cycle second)) +
        realUpperCuspidalBinarySection degree cusp (realPlaneBinaryCochain degree cusp cycle first) := by
  let : AddCommGroup (cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1))) :=
    (cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1))).addCommGroup
  have action : (realPlaneBinaryCochain degree cusp cycle (first * second) -
      realPlaneBinaryCochain degree cusp cycle first).val =
      binaryCohomologicalAction degree first (realPlaneBinaryCochain degree cusp cycle second).val := by
    funext argument
    change (realPlaneBinaryCochain degree cusp cycle (first * second)).val argument -
      (realPlaneBinaryCochain degree cusp cycle first).val argument = _
    rw [realPlaneBinaryCochain_cocycle degree cusp basis cycle regular]
    abel
  have equality := realUpperCuspidalBinarySection_levi degree cusp first
    (realPlaneBinaryCochain degree cusp cycle second)
    (realPlaneBinaryCochain degree cusp cycle (first * second) - realPlaneBinaryCochain degree cusp cycle first) action
  rw [map_sub] at equality
  exact (eq_sub_iff_add_eq.mp equality).symm

theorem realPlaneMixedCocycle_exists_binary_normal {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree cusp trivialCharacter))
    (regular : RealPlaneLevelMixedRegular degree cusp trivialCharacter basis cycle) :
    ∃ potential : BinaryRealGL → realUpperCuspidalRep degree cusp, ∀ matrix,
      realPlaneMixedCocycle degree cusp matrix (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) =
        realUpperCuspidalBinarySection degree cusp
            (realPlaneBinaryCochain degree cusp (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle) matrix) +
          oneBoundaryCycle (realUpperCuspidalRep degree cusp) (potential matrix) := by
  have exists_potential (matrix : BinaryRealGL) := realUpperCuspidalCocycle_exists_binary_normal degree cusp basis
    (realPlaneMixedCocycle degree cusp matrix (realPlaneLevelForgetRelative degree cusp trivialCharacter cycle))
    (realPlaneLevelMixedCocycle_differentiable degree cusp basis cycle regular matrix)
  choose potential equality using exists_potential
  exact ⟨potential, equality⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
