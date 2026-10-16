module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Standard.ThreeCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finiteLevel_of_integral_of_three (matrix : FiniteGL)
    (integral : matrix ∈ finiteIntegralGLLevel 3)
    (three : InLocalThreeLevel (GeneralLinearGroup.map finiteThree matrix)) : matrix ∈ finiteLevel := by
  obtain ⟨compact, compact_eq⟩ := integral
  obtain ⟨integer, fixed, integer_eq⟩ := three
  rw [padicThreeEmbedding_matrix] at integer_eq
  have same : GeneralLinearGroup.map integralThree compact = integer := by
    apply generalLinearGroup_map_injective padicThreeEmbedding padicThreeEmbedding_injective
    rw [finiteThree_integralMatrix, compact_eq, integer_eq]
  refine ⟨compact, ?_, compact_eq⟩
  change lastRow ᵥ* (GeneralLinearGroup.map integralReduction compact).val = lastRow
  rw [← integralThree_reduceMatrix, same]
  exact fixed

theorem finiteAtThree_plane (matrix : planeParabolic ℚ_[3]) :
    finiteAtThree matrix.val ∈ planeParabolic FiniteAdeles := by
  constructor
  · change (0 : FiniteAdeles) + finiteAtThreeScalar (matrix.val.val 2 0 - finiteThree 0) = 0
    simp only [matrix.property.1, map_zero, sub_self, finiteAtThreeScalar_zero, zero_add]
  · change (0 : FiniteAdeles) + finiteAtThreeScalar (matrix.val.val 2 1 - finiteThree 0) = 0
    simp only [matrix.property.2, map_zero, sub_self, finiteAtThreeScalar_zero, zero_add]

/-- When the local component at three is in the level, the finite plane factor can be chosen to be one there. -/
theorem finiteGL_plane_level_factorization (matrix : FiniteGL)
    (three : InLocalThreeLevel (GeneralLinearGroup.map finiteThree matrix)) :
    ∃ (parabolic : planeParabolic FiniteAdeles) (compact : finiteLevel),
      GeneralLinearGroup.map finiteThree parabolic.val = 1 ∧ matrix = parabolic.val * compact.val := by
  obtain ⟨parabolic, compact, factors⟩ := finiteGL_parabolic_compact_factorization matrix
  have original_three := three
  obtain ⟨integer, _, integer_eq⟩ := three
  rw [padicThreeEmbedding_matrix] at integer_eq
  let local_lift := integer * (GeneralLinearGroup.map integralThree compact)⁻¹
  have local_lift_eq : GeneralLinearGroup.map padicThreeEmbedding local_lift =
      GeneralLinearGroup.map finiteThree parabolic.val := by
    dsimp only [local_lift]
    rw [map_mul, map_inv, finiteThree_integralMatrix, integer_eq, factors, map_mul, mul_inv_cancel_right]
  let local_parabolic : planeParabolic ℚ_[3] :=
    ⟨GeneralLinearGroup.map finiteThree parabolic.val, generalLinearGroup_map_plane finiteThree parabolic⟩
  let correction := finiteAtThree local_parabolic.val
  have correction_integral : correction ∈ finiteIntegralGLLevel 3 := by
    change finiteAtThree (GeneralLinearGroup.map finiteThree parabolic.val) ∈ _
    rw [← local_lift_eq]
    exact finiteAtThree_integral local_lift
  have correction_plane : correction ∈ planeParabolic FiniteAdeles := finiteAtThree_plane local_parabolic
  let new_parabolic : planeParabolic FiniteAdeles :=
    parabolic * (⟨correction, correction_plane⟩ : planeParabolic FiniteAdeles)⁻¹
  let new_compact := correction * GeneralLinearGroup.map integralEmbedding compact
  have compact_integral : new_compact ∈ finiteIntegralGLLevel 3 :=
    (finiteIntegralGLLevel 3).mul_mem correction_integral ⟨compact, rfl⟩
  have compact_three : GeneralLinearGroup.map finiteThree new_compact = GeneralLinearGroup.map finiteThree matrix := by
    dsimp only [new_compact, correction, local_parabolic]
    rw [map_mul, finiteAtThree_three, ← map_mul, ← factors]
  have compact_level : new_compact ∈ finiteLevel :=
    finiteLevel_of_integral_of_three new_compact compact_integral (compact_three ▸ original_three)
  refine ⟨new_parabolic, ⟨new_compact, compact_level⟩, ?_, ?_⟩
  · change GeneralLinearGroup.map finiteThree (parabolic.val * correction⁻¹) = 1
    rw [map_mul, map_inv]
    change GeneralLinearGroup.map finiteThree parabolic.val *
      (GeneralLinearGroup.map finiteThree (finiteAtThree (GeneralLinearGroup.map finiteThree parabolic.val)))⁻¹ = 1
    rw [finiteAtThree_three, mul_inv_cancel]
  · change matrix = (parabolic.val * correction⁻¹) *
      (correction * GeneralLinearGroup.map integralEmbedding compact)
    rw [mul_assoc, inv_mul_cancel_left]
    exact factors

end TernaryPeriodPolynomials.SphericalDetection.Helpers
