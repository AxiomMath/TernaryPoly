module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.GroupAverageCancellation
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Reduced.PlaneContraction
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearLipschitzKernels
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.EisensteinQuotient

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped Matrix.Norms.Elementwise Pointwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

theorem normalizedBoundaryResidueAverage_reduced_decay
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    {kernel : RealSL3 → ℂ} (kernel_continuous : Continuous kernel) (support : HasCompactSupport kernel)
    {constant : ℝ} (constant_nonnegative : 0 ≤ constant)
    (lipschitz : ∀ first second, ‖kernel first - kernel second‖ ≤ constant * ‖first.val - second.val‖) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ m n : ℕ,
      ∀ matrix ∈ realSpecialScaling m n • realSpecialShrinkingBox m n (realSpecialDiagonalBox (1 / 64) 64),
      ∀ integral : GL3 IntegralAdeles,
        ‖normalizedBoundaryResidueAverage degree continuation integral kernel matrix‖ ≤ bound * (8 : ℝ)⁻¹ ^ n := by
  obtain ⟨contractionBound, contraction_nonnegative, contraction⟩ :=
    realSpecialShrinkingTranslate_plane_contraction (realSpecialDiagonalBox_isCompact (1 / 64) 64)
  obtain ⟨kernelBound, kernel_nonnegative, kernel_bound⟩ :=
    realSpecialLinear_lipschitz_kernel_translation_bound support constant_nonnegative lipschitz
      (realSpecialLinear_norm_ball_compact 1 contractionBound)
  obtain ⟨residueBound, residue_nonnegative, residue_bound⟩ :=
    normalizedBoundaryResidue_global_bound flat continuation_spec
  refine ⟨residueBound * (kernelBound * contractionBound), by positivity, ?_⟩
  intro m n matrix member integral
  have estimate := rightGroupAverage_bound_of_zero_average realSpecialLinearHaar realPlaneUnitMeasure
    (normalizedBoundaryResidue_measurable flat continuation_spec (realSpecialIntegralSlice_continuous integral))
    kernel_continuous.measurable (kernel_continuous.integrable_of_hasCompactSupport support)
    residue_nonnegative (fun point => residue_bound (realSpecialIntegralSlice integral point))
    (fun point : ℝ × ℝ => realSpecialPlane (3 * point.1) (3 * point.2))
    (realSpecialPlane_continuous.comp
      ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))).measurable
    (normalizedBoundaryResidue_realSpecialPlane_average_zero flat continuation_spec integral) matrix
    (decay := (kernelBound * contractionBound) * (8 : ℝ)⁻¹ ^ n) (by
      rw [realPlaneUnitMeasure, Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ico.prod measurableSet_Ico)] with point point_member
      have first_bound : |-(3 * point.1)| ≤ 3 := by
        apply abs_le.mpr
        constructor <;> linarith [point_member.1.1, point_member.1.2]
      have second_bound : |-(3 * point.2)| ≤ 3 := by
        apply abs_le.mpr
        constructor <;> linarith [point_member.2.1, point_member.2.2]
      have contracted := contraction m n matrix member _ _ first_bound second_bound
      rw [realSpecialPlane_inverse]
      have in_ball : matrix⁻¹ * realSpecialPlane (-(3 * point.1)) (-(3 * point.2)) * matrix ∈
          {argument : RealSL3 | ‖argument.val - 1‖ ≤ contractionBound} := by
        exact contracted.trans ((mul_le_mul_of_nonneg_left
          (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 8⁻¹) (by norm_num)) contraction_nonnegative).trans_eq (mul_one _))
      exact (kernel_bound _ in_ball).trans
        ((mul_le_mul_of_nonneg_left contracted kernel_nonnegative).trans_eq (mul_assoc _ _ _).symm))
  simpa only [normalizedBoundaryResidueAverage, mul_assoc] using estimate

theorem normalizedBoundaryResidueAverage_integer_inverse
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (integer : SpecialLinearGroup (Fin 3) ℤ) (integral : GL3 IntegralAdeles)
    (kernel : RealSL3 → ℂ) (matrix : RealSL3) :
    normalizedBoundaryResidueAverage degree continuation integral kernel
      ((SpecialLinearGroup.map (Int.castRingHom ℝ) integer)⁻¹ * matrix) =
      normalizedBoundaryResidueAverage degree continuation
        (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) (SpecialLinearGroup.toGL integer) * integral)
        kernel matrix := by
  unfold normalizedBoundaryResidueAverage rightGroupAverage
  apply integral_congr_ae
  filter_upwards with shift
  rw [mul_assoc, ← integer_inverse_slice_identity, normalizedBoundaryResidue_rational_invariant flat continuation_spec]

theorem normalizedBoundaryResidueAveragePrincipalQuotient_piece_decay
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    {kernel : RealSL3 → ℂ} (kernel_continuous : Continuous kernel) (support : HasCompactSupport kernel)
    {constant : ℝ} (constant_nonnegative : 0 ≤ constant)
    (lipschitz : ∀ first second, ‖kernel first - kernel second‖ ≤ constant * ‖first.val - second.val‖) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ residue : integerSpecialLinearReduction.range, ∀ m n : ℕ,
      ∀ point ∈ principalQuotientPiece residue m n, ∀ integral : GL3 IntegralAdeles,
        ‖normalizedBoundaryResidueAveragePrincipalQuotient flat continuation_spec integral kernel point‖ ≤
          bound * (8 : ℝ)⁻¹ ^ n := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedBoundaryResidueAverage_reduced_decay
    flat continuation_spec kernel_continuous support constant_nonnegative lipschitz
  refine ⟨bound, nonnegative, ?_⟩
  intro residue m n point member integral
  obtain ⟨representative, representative_member, rfl⟩ := member
  obtain ⟨reduced, reduced_member, rfl⟩ := representative_member
  change ‖normalizedBoundaryResidueAverage degree continuation integral kernel
    ((SpecialLinearGroup.map (Int.castRingHom ℝ) (integerSpecialLinearReductionRepresentative residue))⁻¹ * reduced)‖ ≤ _
  rw [normalizedBoundaryResidueAverage_integer_inverse flat continuation_spec]
  exact bounded m n reduced reduced_member _

theorem normalizedBoundaryResidueTentAverage_piece_decay
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (radius : ℝ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ residue : integerSpecialLinearReduction.range, ∀ m n : ℕ,
      ∀ point ∈ principalQuotientPiece residue m n, ∀ integral : GL3 IntegralAdeles,
        ‖normalizedBoundaryResidueAveragePrincipalQuotient flat continuation_spec integral (realSpecialTent radius) point‖ ≤
          bound * (8 : ℝ)⁻¹ ^ n := by
  apply normalizedBoundaryResidueAveragePrincipalQuotient_piece_decay flat continuation_spec
    (realSpecialTent_continuous radius) (realSpecialTent_compactSupport radius) (constant := 1) (by norm_num)
  intro first second
  simpa only [one_mul] using realSpecialTent_lipschitz radius first second

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
