module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.RealSliceBound
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.ResidueSymmetries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem ternary_atInfinity_scalar (scalar : ℝˣ) :
    atInfinity (GeneralLinearGroup.scalar (Fin 3) scalar) =
      GeneralLinearGroup.scalar (Fin 3) (realAdeleUnit scalar) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, combineGL, pairMatrix, realAdeleUnit,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem real_matrix_positive_scalar_unit_det (matrix : RealGL3) :
    ∃ scalar : ℝˣ, 0 < scalar.val ∧
      |(GeneralLinearGroup.scalar (Fin 3) scalar * matrix).val.det| = 1 := by
  have determinant_positive : 0 < |matrix.val.det| := abs_pos.mpr matrix.det_ne_zero
  let scalar : ℝˣ := Units.mk0 (|matrix.val.det| ^ (-(1 : ℝ) / 3))
    (ne_of_gt (Real.rpow_pos_of_pos determinant_positive _))
  have scalar_positive : 0 < scalar.val := Real.rpow_pos_of_pos determinant_positive _
  refine ⟨scalar, scalar_positive, ?_⟩
  have scalar_cube : scalar.val ^ 3 = |matrix.val.det|⁻¹ := by
    change (|matrix.val.det| ^ (-(1 : ℝ) / 3)) ^ 3 = _
    rw [← Real.rpow_mul_natCast determinant_positive.le]
    norm_num [Real.rpow_neg_one]
  change |(GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) scalar * matrix)).val| = 1
  rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, Units.val_mul, Units.val_pow_eq_pow_val,
    GeneralLinearGroup.val_det_apply, abs_mul, abs_pow, abs_of_pos scalar_positive,
    scalar_cube, inv_mul_cancel₀ (ne_of_gt determinant_positive)]

theorem normalizedBoundaryResidue_central_norm
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (idele : Adelesˣ) (matrix : AdelicGL) :
    ‖normalizedBoundaryResidue degree continuation (GeneralLinearGroup.scalar (Fin 3) idele * matrix)‖ =
      ‖normalizedBoundaryResidue degree continuation matrix‖ := by
  rw [normalizedBoundaryResidue_central_character flat continuation_spec, norm_mul, norm_mul,
    inducingData.chi.unitary, inducingData.cusp.centralUnitary, one_mul, one_mul]

theorem normalizedBoundaryResidue_integral_finite_bound
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ matrix : AdelicGL,
      finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding) →
      ‖normalizedBoundaryResidue degree continuation matrix‖ ≤ bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedBoundaryResidue_unitDet_integral_bound flat continuation_spec
  refine ⟨bound, nonnegative, ?_⟩
  intro matrix integral
  obtain ⟨scalar, _, unit_det⟩ := real_matrix_positive_scalar_unit_det (realGroup matrix)
  let scaled := atInfinity (GeneralLinearGroup.scalar (Fin 3) scalar) * matrix
  have scaled_integral : finiteGroup scaled ∈ Set.range (GeneralLinearGroup.map integralEmbedding) := by
    simpa only [scaled, map_mul, finiteGroup_atInfinity, one_mul] using integral
  have scaled_unit_det : |(realGroup scaled).val.det| = 1 := by
    simpa only [scaled, map_mul, realGroup_atInfinity] using unit_det
  have scaled_bound := bounded scaled scaled_integral scaled_unit_det
  simpa only [scaled, ternary_atInfinity_scalar,
    normalizedBoundaryResidue_central_norm flat continuation_spec] using scaled_bound

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
