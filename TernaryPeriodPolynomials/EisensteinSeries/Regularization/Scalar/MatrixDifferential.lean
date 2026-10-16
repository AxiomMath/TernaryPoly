module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.InvariantOperators
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.CentralDerivedAction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cohomological_realize_positive_scalar {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (scalar : ℝˣ) (positive : 0 < scalar.val)
    (vector : cusp.smooth) (argument : BinaryAdelicGL) :
    cusp.realize vector (argument * atInfinity (GeneralLinearGroup.scalar (Fin 2) scalar)) =
      cusp.realize vector argument := by
  rw [atInfinity_scalar, ← GeneralLinearGroup.scalar_commute, cusp.central,
    cohomological_centralCharacter_positive cohomological scalar positive, one_mul]

theorem cohomological_scalar_fderiv_identity {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (vector : cusp.smooth) (argument : BinaryAdelicGL) :
    fderiv ℝ (cuspScalarMatrixOrbit cusp vector argument) 1 1 = 0 := by
  have smooth := cuspScalarMatrixOrbit_contDiffAt cusp vector argument 1
  have curve_derivative : HasDerivAt
      (fun scalar : ℝ => scalar • (1 : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const (1 : Matrix (Fin 2) (Fin 2) ℝ)
  have orbit_derivative := (smooth.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    1 curve_derivative (by simp)
  have near : (fun scalar : ℝ => cuspScalarMatrixOrbit cusp vector argument (scalar • 1)) =ᶠ[nhds 1]
      (fun _ => cusp.realize vector argument) := by
    have positive_near : ∀ᶠ scalar : ℝ in nhds 1, 0 < scalar :=
      (isOpen_lt continuous_const continuous_id).eventually_mem (by norm_num)
    filter_upwards [positive_near] with scalar positive
    let unit : ℝˣ := Units.mk0 scalar positive.ne'
    have value : (GeneralLinearGroup.scalar (Fin 2) unit).val = scalar • 1 := by
      ext row column
      fin_cases row <;> fin_cases column <;> simp [unit, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    rw [← value, cuspScalarMatrixOrbit, invertibleMatrix_val]
    exact cohomological_realize_positive_scalar cohomological unit positive vector argument
  have constant_derivative := (hasDerivAt_const (1 : ℝ) (cusp.realize vector argument)).congr_of_eventuallyEq near
  simpa only [one_smul, Units.val_one] using orbit_derivative.unique constant_derivative

theorem cohomological_scalar_fderiv {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (vector : cusp.smooth) (argument : BinaryAdelicGL)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    fderiv ℝ (cuspScalarMatrixOrbit cusp vector argument) 1 direction =
      cusp.realize (cuspDerivedAction cusp direction vector) argument := by
  have traceless : Matrix.trace (direction - (Matrix.trace direction / 2) • 1) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
    norm_num
  have transferred := cuspScalarMatrixOrbit_fderiv_traceless cusp vector argument
    (direction - (Matrix.trace direction / 2) • 1) traceless
  simpa only [map_sub, map_smul, cohomological_scalar_fderiv_identity cohomological,
    smul_zero, sub_zero, cohomological_derived_identity_zero cohomological] using transferred

theorem cuspScalarMatrixOrbit_mul (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (first : BinaryRealGL) {second : Matrix (Fin 2) (Fin 2) ℝ}
    (invertible : second.det ≠ 0) :
    cuspScalarMatrixOrbit cusp vector argument (first.val * second) =
      cuspScalarMatrixOrbit cusp vector (argument * atInfinity first) second := by
  have value : first.val * second = (first * invertibleMatrix second).val := by
    simp only [Units.val_mul, invertibleMatrix, dite_eq_left invertible, GeneralLinearGroup.val_mkOfDetNeZero]
  simp only [cuspScalarMatrixOrbit, value, invertibleMatrix_val, binary_atInfinity_mul, mul_assoc]

theorem cuspScalarMatrixOrbit_left_derivative (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (argument : BinaryAdelicGL) (matrix : BinaryRealGL) (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    fderiv ℝ (cuspScalarMatrixOrbit cusp vector argument) matrix.val (matrix.val * direction) =
      fderiv ℝ (cuspScalarMatrixOrbit cusp vector (argument * atInfinity matrix)) 1 direction := by
  let left : Matrix (Fin 2) (Fin 2) ℝ →L[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ matrix.val)
  have at_image : DifferentiableAt ℝ (cuspScalarMatrixOrbit cusp vector argument) (left 1) := by
    change DifferentiableAt ℝ (cuspScalarMatrixOrbit cusp vector argument) (matrix.val * 1)
    rw [mul_one]
    exact (cuspScalarMatrixOrbit_contDiffAt cusp vector argument matrix).differentiableAt (by simp)
  have differentiated := at_image.hasFDerivAt.comp 1 left.hasFDerivAt
  have applied := congrArg (fun linear => linear direction) differentiated.fderiv
  change fderiv ℝ (fun entries => cuspScalarMatrixOrbit cusp vector argument (matrix.val * entries)) 1 direction =
    fderiv ℝ (cuspScalarMatrixOrbit cusp vector argument) (matrix.val * 1) (matrix.val * direction) at applied
  rw [mul_one] at applied
  have near : (fun entries => cuspScalarMatrixOrbit cusp vector argument (matrix.val * entries)) =ᶠ[nhds 1]
      cuspScalarMatrixOrbit cusp vector (argument * atInfinity matrix) := by
    have domain_near : ∀ᶠ entries : Matrix (Fin 2) (Fin 2) ℝ in nhds 1, entries.det ≠ 0 :=
      (isOpen_ne.preimage continuous_id.matrix_det).eventually_mem (by simp)
    filter_upwards [domain_near] with entries invertible
    exact cuspScalarMatrixOrbit_mul cusp vector argument matrix invertible
  rw [near.fderiv_eq] at applied
  exact applied.symm

theorem cohomological_scalar_fderiv_at_matrix {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (vector : cusp.smooth) (argument : BinaryAdelicGL)
    (matrix : BinaryRealGL) (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    fderiv ℝ (cuspScalarMatrixOrbit cusp vector argument) matrix.val direction =
      cusp.realize (cuspDerivedAction cusp (matrix.inv * direction) vector)
        (argument * atInfinity matrix) := by
  have tangent : direction = matrix.val * (matrix.inv * direction) := by
    rw [← mul_assoc, matrix.val_inv, one_mul]
  calc
    _ = fderiv ℝ (cuspScalarMatrixOrbit cusp vector argument) matrix.val
        (matrix.val * (matrix.inv * direction)) := congrArg _ tangent
    _ = _ := by rw [cuspScalarMatrixOrbit_left_derivative, cohomological_scalar_fderiv cohomological]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
