module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneBinaryCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cuspidal.TensorArithmetic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem radicalLatticeReal_inverseLevi (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    realRadicalInverseLevi (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix) (radicalLatticeReal radical) =
      radicalLatticeReal (upperLeviLatticeInput matrix radical) := by
  apply Multiplicative.toAdd.injective
  change (realPlaneRadicalAction (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix)⁻¹
    (radicalLatticeReal radical)).toAdd = _
  rw [realPlaneRadicalAction_apply, ← map_inv]
  funext coordinate
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, GeneralLinearGroup.map_apply]
  fin_cases coordinate
  · change (matrix⁻¹.val 0 0 : ℝ) * (radical.toAdd.1 : ℝ) +
      (matrix⁻¹.val 0 1 : ℝ) * (radical.toAdd.2 : ℝ) =
        ((matrix⁻¹.val 0 0 * radical.toAdd.1 + matrix⁻¹.val 0 1 * radical.toAdd.2 : ℤ) : ℝ)
    simp only [Int.cast_add, Int.cast_mul]
  · change (matrix⁻¹.val 1 0 : ℝ) * (radical.toAdd.1 : ℝ) +
      (matrix⁻¹.val 1 1 : ℝ) * (radical.toAdd.2 : ℝ) =
        ((matrix⁻¹.val 1 0 * radical.toAdd.1 + matrix⁻¹.val 1 1 * radical.toAdd.2 : ℤ) : ℝ)
    simp only [Int.cast_add, Int.cast_mul]

theorem realPlaneMixedCocycle_arithmetic (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (arithmetic : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree))
    (comparison : ∀ first second,
      (cycle.val (identityPlaneRealGroup first, identityPlaneRealGroup second)).val 1 = arithmetic.val (first, second))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (radical : RadicalLattice) :
    (realPlaneMixedCocycle degree cusp (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix) cycle
      (radicalLatticeReal radical)).val 1 = identityPlaneRadicalEdgeCycle degree arithmetic matrix radical := by
  rw [realPlaneMixedCocycle_apply, radicalLatticeReal_inverseLevi, identityPlaneSplitEdgeCycle_apply]
  change (cycle.val (SemidirectProduct.inr (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix),
      SemidirectProduct.inl (radicalLatticeReal (upperLeviLatticeInput matrix radical)))).val 1 -
    (cycle.val (SemidirectProduct.inl (radicalLatticeReal radical),
      SemidirectProduct.inr (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix))).val 1 = _
  rw [← identityPlaneRealGroup_levi, ← identityPlaneRealGroup_radical, ← identityPlaneRealGroup_radical,
    comparison, comparison]
  rfl

theorem realPlaneBinaryCochain_arithmetic (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (arithmetic : relativeTwoCocycles identityPlaneRadicalInclusion (identityPlaneCoefficientRep degree))
    (comparison : ∀ first second,
      (cycle.val (identityPlaneRealGroup first, identityPlaneRealGroup second)).val 1 = arithmetic.val (first, second))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    (realPlaneBinaryCochain degree cusp cycle (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix)).val 1 =
      identityPlaneBinaryEdgeCycle degree arithmetic matrix := by
  apply Subtype.ext
  change ((realUpperCuspidalBinaryCoordinate degree cusp
    (realPlaneMixedCocycle degree cusp (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix) cycle)).val 1).val = _
  rw [realUpperCuspidalBinaryCoordinate_value, realRadicalAxis_one, realRadicalAxis_one,
    realPlaneMixedCocycle_arithmetic degree cusp cycle arithmetic comparison,
    realPlaneMixedCocycle_arithmetic degree cusp cycle arithmetic comparison,
    identityPlaneBinaryEdgeCycle_apply, upperRadicalCocycleCoordinate_value]
  rfl

theorem binaryCohomologicalAction_integralReal (degree : ℕ) (cusp : CuspidalRepresentation)
    (values : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)))
    (fixed : values ∈ cuspidalTensorFiniteLevel cusp (Binary.HomogeneousPoly (degree + 1)))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) :
    binaryCohomologicalAction degree (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix) values.val 1 =
      Binary.homogeneousAction (degree + 1) (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix) (values.val 1) := by
  unfold binaryCohomologicalAction
  rw [normPower_binaryIntegralReal, one_smul, one_mul, cuspidalTensorFiniteLevel_integralReal cusp values fixed]
  unfold binaryCoefficient
  have casts : GeneralLinearGroup.map (algebraMap ℝ ℂ) (GeneralLinearGroup.map (Int.castRingHom ℝ) matrix) =
      GeneralLinearGroup.map (Int.castRingHom ℂ) matrix := by
    apply Units.ext
    funext row column
    simp [GeneralLinearGroup.map_apply]
  rw [casts]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
