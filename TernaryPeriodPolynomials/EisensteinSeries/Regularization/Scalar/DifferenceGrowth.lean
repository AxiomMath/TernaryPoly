module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.ProfileDifferences

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem normalizedScalarDifferenceProfile_real_compact_reduction
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (shift : AdelicGL)
    (matrix : AdelicGL) :
    ∃ compactMatrix : RealGL3, compactMatrix.val.transpose * compactMatrix.val = 1 ∧ ∀ parameter : ℂ,
      ‖normalizedScalarDifferenceProfile flat shift parameter matrix‖ =
        Real.exp ((inductionExponent .plane parameter).re * Real.log |(realGroup matrix).val.det| -
          (3 / 2 + parameter.re) * Real.log (realPlaneHeight (realGroup matrix))) *
        ‖normalizedScalarDifferenceProfile flat shift parameter (combineGL compactMatrix (finiteGroup matrix))‖ := by
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
    rw [adelic_decomposition, mul_assoc, normalizedScalarDifferenceProfile_unipotent, planeLevi_rankOne_binary,
      mul_assoc, normalizedScalarDifferenceProfile_rankOne_norm, normalizedScalarDifferenceProfile_binary_norm,
      det_atInfinity_binary, adeleNorm_realAdeleUnit, adeleNorm_realAdeleUnit, scalar_height,
      abs_of_pos (realPlaneHeight_pos (realGroup matrix)), GeneralLinearGroup.val_det_apply]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  rw [log_det]
  norm_num [inductionExponent, Complex.mul_re, Complex.div_re]
  ring

theorem normalizedScalarDifferenceProfile_parabolic_rational_norm
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (shift : AdelicGL) (parameter : ℂ) (rationalMatrix : RationalGL3)
    (parabolic : rationalMatrix ∈ GeneralEisenstein.parabolic .plane) (matrix : AdelicGL) :
    ‖normalizedScalarDifferenceProfile flat shift parameter (rationalGroup rationalMatrix * matrix)‖ =
      ‖normalizedScalarDifferenceProfile flat shift parameter matrix‖ := by
  obtain ⟨first, second, binary, scalar, factorization⟩ :=
    planeParabolic_factorization rationalMatrix parabolic
  rw [factorization, map_mul, mul_assoc]
  change ‖normalizedScalarDifferenceProfile flat shift parameter
    (GeneralLinearGroup.map rationalAdele (planeUnipotent first second) *
      (GeneralLinearGroup.map rationalAdele (planeLevi binary scalar) * matrix))‖ = _
  rw [map_planeUnipotent, normalizedScalarDifferenceProfile_unipotent, map_planeLevi,
    planeLevi_rankOne_binary, mul_assoc, normalizedScalarDifferenceProfile_rankOne_norm,
    normalizedScalarDifferenceProfile_binary_norm, GeneralLinearGroup.map_det,
    adeleNorm_rational, adeleNorm_rational]
  simp

theorem normalizedScalarDifferenceProfile_norm_of_representative
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (shift : AdelicGL) (parameter : ℂ)
    (representative : RationalGL3) (matrix : AdelicGL) :
    ‖normalizedScalarDifferenceProfile flat shift parameter
      (rationalGroup (Quotient.out (QuotientGroup.mk representative : Flags .plane))⁻¹ * matrix)‖ =
      ‖normalizedScalarDifferenceProfile flat shift parameter (rationalGroup representative⁻¹ * matrix)‖ := by
  obtain ⟨parabolic, equality⟩ :=
    QuotientGroup.mk_out_eq_mul (GeneralEisenstein.parabolic .plane) representative
  rw [equality, _root_.mul_inv_rev, map_mul, mul_assoc]
  exact normalizedScalarDifferenceProfile_parabolic_rational_norm flat shift parameter parabolic.val⁻¹
    ((GeneralEisenstein.parabolic .plane).inv_mem parabolic.property) _

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
