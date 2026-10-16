module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.PolynomialDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryMatrixDerivative

def path (direction : BinaryMatrix) (parameter : ℝ) : BinaryMatrix := 1 + parameter • direction

theorem path_zero (direction : BinaryMatrix) : path direction 0 = 1 := by simp [path]

theorem path_derivative (direction : BinaryMatrix) : HasDerivAt (path direction) direction 0 := by
  have derivative := ((hasDerivAt_id (0 : ℝ)).smul_const direction).const_add (1 : BinaryMatrix)
  simp only [one_smul] at derivative
  exact derivative

theorem path_entry_derivative (direction : BinaryMatrix) (row column : Fin 2) :
    HasDerivAt (fun parameter => path direction parameter row column) (direction row column) 0 := by
  have derivative := ((hasDerivAt_id (0 : ℝ)).mul_const (direction row column)).const_add
    ((1 : BinaryMatrix) row column)
  simp only [one_mul] at derivative
  exact derivative

theorem path_invertible (direction : BinaryMatrix) :
    ∀ᶠ parameter in nhds (0 : ℝ), (path direction parameter).det ≠ 0 := by
  have membership : path direction 0 ∈ binaryDomain := by simp [path_zero, binaryDomain]
  exact (path_derivative direction).continuousAt.preimage_mem_nhds (binaryDomain_isOpen.mem_nhds membership)

theorem determinant_derivative (direction : BinaryMatrix) :
    HasDerivAt (fun parameter => (path direction parameter).det) (direction 0 0 + direction 1 1) 0 := by
  have derivative := ((path_entry_derivative direction 0 0).mul (path_entry_derivative direction 1 1)).sub
    ((path_entry_derivative direction 0 1).mul (path_entry_derivative direction 1 0))
  norm_num [path_zero, Matrix.one_apply] at derivative
  simp only [Matrix.det_fin_two]
  exact derivative

theorem adjugate_entry_derivative (direction : BinaryMatrix) (row column : Fin 2) :
    HasDerivAt (fun parameter => (path direction parameter).adjugate row column)
      (!![direction 1 1, -direction 0 1; -direction 1 0, direction 0 0] row column) 0 := by
  simp only [Matrix.adjugate_fin_two]
  fin_cases row <;> fin_cases column
  · exact path_entry_derivative direction 1 1
  · exact (path_entry_derivative direction 0 1).neg
  · exact (path_entry_derivative direction 1 0).neg
  · exact path_entry_derivative direction 0 0

theorem inverse_entry_derivative (direction : BinaryMatrix) (row column : Fin 2) :
    HasDerivAt (fun parameter => (invertibleMatrix (path direction parameter))⁻¹.val row column)
      (-direction row column) 0 := by
  have determinantNonzero : (path direction 0).det ≠ 0 := by simp [path_zero]
  have derivative := ((determinant_derivative direction).inv determinantNonzero).mul
    (adjugate_entry_derivative direction row column)
  have valueEquality : -(direction 0 0 + direction 1 1) / (path direction 0).det ^ 2 *
      (path direction 0).adjugate row column + (path direction 0).det⁻¹ *
        !![direction 1 1, -direction 0 1; -direction 1 0, direction 0 0] row column = -direction row column := by
    rw [path_zero]
    fin_cases row <;> fin_cases column <;> simp
  change HasDerivAt (fun parameter => (path direction parameter).det⁻¹ *
    (path direction parameter).adjugate row column) _ 0 at derivative
  have modelDerivative : HasDerivAt (fun parameter => (path direction parameter).det⁻¹ *
      (path direction parameter).adjugate row column) (-direction row column) 0 := by
    convert derivative using 1
    exact valueEquality.symm
  apply modelDerivative.congr_of_eventuallyEq
  filter_upwards [path_invertible direction] with parameter invertibility
  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_def, Ring.inverse_eq_inv,
    invertibleMatrix_val _ invertibility]
  rfl

theorem normPower_derivative (exponent : ℂ) (direction : BinaryMatrix) :
    HasDerivAt (fun parameter =>
      normPower (Matrix.GeneralLinearGroup.det (atInfinity (invertibleMatrix (path direction parameter)))) exponent)
      (exponent * ((direction 0 0 + direction 1 1 : ℝ) : ℂ)) 0 := by
  have determinantNonzero : (path direction 0).det ≠ 0 := by simp [path_zero]
  have derivative := (((determinant_derivative direction).log determinantNonzero).ofReal_comp.const_mul exponent).cexp
  simp only [path_zero, Matrix.det_one, Real.log_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, div_one] at derivative
  apply derivative.congr_of_eventuallyEq
  filter_upwards [path_invertible direction] with parameter invertibility
  rw [normPower, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_det_atInfinity, invertibleMatrix_val _ invertibility,
    Real.log_abs]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryMatrixDerivative
