module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Compact.FlagNormBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem det_atInfinity_binary (matrix : BinaryRealGL) :
    GeneralLinearGroup.det (atInfinity matrix) = realAdeleUnit (GeneralLinearGroup.det matrix) := by
  apply Units.ext
  apply Prod.ext <;>
    simp [GeneralLinearGroup.val_det_apply, atInfinity, combineGL, pairMatrix, realAdeleUnit, Matrix.det_fin_two]

theorem realOrthogonal_abs_det (matrix : RealGL3) (orthogonal : matrix.val.transpose * matrix.val = 1) :
    |matrix.val.det| = 1 := by
  have determinant := congrArg Matrix.det orthogonal
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at determinant
  nlinarith [sq_abs matrix.val.det, abs_nonneg matrix.val.det]

theorem combineGL_eq_real_finite (realMatrix : RealGL3) (finiteMatrix : FiniteGL) :
    combineGL realMatrix finiteMatrix = atInfinity realMatrix * atFinite finiteMatrix := by
  simpa only [realGroup_combineGL, finiteGroup_combineGL] using
    adelicGroup_real_finite (combineGL realMatrix finiteMatrix)

theorem normalizedCuspVector_real_compact_reduction
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (matrix : AdelicGL) :
    ∃ compactMatrix : RealGL3, compactMatrix.val.transpose * compactMatrix.val = 1 ∧ ∀ parameter : ℂ,
      ‖(normalizedCuspVector induced parameter matrix).val‖ =
        Real.exp ((inductionExponent .plane parameter).re * Real.log |(realGroup matrix).val.det| -
          (3 / 2 + parameter.re) * Real.log (realPlaneHeight (realGroup matrix))) *
        ‖(normalizedCuspVector induced parameter (combineGL compactMatrix (finiteGroup matrix))).val‖ := by
  obtain ⟨first, second, binary, scalar, compactMatrix, decomposition, orthogonal, scalar_height⟩ :=
    real_plane_levi_decomposition (realGroup matrix)
  refine ⟨compactMatrix, orthogonal, ?_⟩
  have adelic_decomposition : matrix = planeUnipotent (first, (0 : FiniteAdeles)) (second, (0 : FiniteAdeles)) *
      planeLevi (atInfinity binary) (realAdeleUnit scalar) * combineGL compactMatrix (finiteGroup matrix) := by
    calc
      matrix = atInfinity (realGroup matrix) * atFinite (finiteGroup matrix) := adelicGroup_real_finite matrix
      _ = _ := by
        rw [decomposition, atInfinity_mul, atInfinity_mul, atInfinity_planeUnipotent, atInfinity_planeLevi,
          combineGL_eq_real_finite, mul_assoc]
  have determinant_eq := congrArg GeneralLinearGroup.det decomposition
  have unipotent_det : GeneralLinearGroup.det (planeUnipotent first second : RealGL3) = 1 := by
    apply Units.ext
    simp [GeneralLinearGroup.val_det_apply, planeUnipotent, Matrix.det_fin_three]
  have levi_det : GeneralLinearGroup.det (planeLevi binary scalar) = GeneralLinearGroup.det binary * scalar := by
    apply Units.ext
    simp [GeneralLinearGroup.val_det_apply, planeLevi, planeBlock, Matrix.det_fin_three, Matrix.det_fin_two]
    ring
  simp only [map_mul, unipotent_det, one_mul, levi_det] at determinant_eq
  have absolute_det : |(realGroup matrix).val.det| = |binary.val.det| * realPlaneHeight (realGroup matrix) := by
    have absolute := congrArg (fun value : ℝˣ => |value.val|) determinant_eq
    simpa only [Units.val_mul, GeneralLinearGroup.val_det_apply, abs_mul, scalar_height,
      abs_of_pos (realPlaneHeight_pos (realGroup matrix)), realOrthogonal_abs_det compactMatrix orthogonal,
      mul_one] using absolute
  have log_det : Real.log |(realGroup matrix).val.det| =
      Real.log |binary.val.det| + Real.log (realPlaneHeight (realGroup matrix)) := by
    rw [absolute_det, Real.log_mul (abs_ne_zero.mpr (GeneralLinearGroup.det_ne_zero binary))
      (ne_of_gt (realPlaneHeight_pos _))]
  intro parameter
  conv_lhs =>
    rw [adelic_decomposition, mul_assoc, normalizedCuspVector_unipotent, planeLevi_rankOne_binary,
      mul_assoc, normalizedCuspVector_rankOne_norm, normalizedCuspVector_binary_norm,
      det_atInfinity_binary, adeleNorm_realAdeleUnit, adeleNorm_realAdeleUnit, scalar_height,
      abs_of_pos (realPlaneHeight_pos (realGroup matrix)), GeneralLinearGroup.val_det_apply]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  rw [log_det]
  norm_num [inductionExponent, Complex.mul_re, Complex.div_re]
  ring

theorem integralRational_real_abs_det (matrix : IntegralGL3) :
    |(realGroup (rationalGroup (integralRational matrix))).val.det| = 1 := by
  change |(GeneralLinearGroup.det (realGroup (rationalGroup (integralRational matrix)))).val| = 1
  rw [realGroup, GeneralLinearGroup.map_det, rationalGroup, GeneralLinearGroup.map_det,
    integralRational, GeneralLinearGroup.map_det]
  change |((((GeneralLinearGroup.det matrix).val : ℤ) : ℚ) : ℝ)| = 1
  push_cast
  rcases Int.units_eq_one_or (GeneralLinearGroup.det matrix) with positive | negative
  · rw [positive]
    norm_num
  · rw [negative]
    norm_num

theorem real_log_abs_det_continuous :
    Continuous (fun matrix : AdelicGL => Real.log |(realGroup matrix).val.det|) := by
  have determinant : Continuous (fun matrix : AdelicGL => (realGroup matrix).val.det) :=
    (Units.continuous_val.comp realGroup_continuous).matrix_det
  exact determinant.abs.log (fun matrix => abs_ne_zero.mpr (GeneralLinearGroup.det_ne_zero (realGroup matrix)))

theorem normalizedCuspVector_compact_real_finite_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (parameters : Set ℂ) (finiteMatrices : Set FiniteGL)
    (parameters_compact : IsCompact parameters) (finite_compact : IsCompact finiteMatrices) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter ∈ parameters, ∀ matrix : AdelicGL,
      finiteGroup matrix ∈ finiteMatrices →
      ‖(normalizedCuspVector flat.1 parameter matrix).val‖ ≤
        Real.exp ((inductionExponent .plane parameter).re * Real.log |(realGroup matrix).val.det| -
          (3 / 2 + parameter.re) * Real.log (realPlaneHeight (realGroup matrix))) * bound := by
  let baseMatrices : Set AdelicGL := (fun input : RealGL3 × FiniteGL => combineGL input.1 input.2) ''
    ({matrix : RealGL3 | matrix.val.transpose * matrix.val = 1} ×ˢ finiteMatrices)
  have base_compact : IsCompact baseMatrices :=
    (realOrthogonal_isCompact.prod finite_compact).image combineGL_continuous
  obtain ⟨bound, bounded⟩ := (parameters_compact.prod base_compact).exists_bound_of_continuousOn
    (normalizedCuspVector_joint_continuous flat).continuousOn
  refine ⟨max 0 bound, le_max_left _ _, ?_⟩
  intro parameter parameter_in matrix finite_in
  obtain ⟨compactMatrix, orthogonal, reduction⟩ := normalizedCuspVector_real_compact_reduction flat.1 matrix
  rw [reduction parameter]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply le_trans _ (le_max_right _ _)
  exact bounded (parameter, combineGL compactMatrix (finiteGroup matrix))
    ⟨parameter_in, (show combineGL compactMatrix (finiteGroup matrix) ∈ baseMatrices from
      ⟨(compactMatrix, finiteGroup matrix), ⟨orthogonal, finite_in⟩, rfl⟩)⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
