module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.SubstitutionDerivative

@[expose] public section


open GeneralEisenstein Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binary_matrix_det_hasDerivAt_one
    (matrix : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (tangent : Matrix (Fin 2) (Fin 2) ℝ)
    (point : ℝ) (identity : matrix point = 1)
    (derivative : ∀ row column, HasDerivAt (fun t => matrix t row column) (tangent row column) point) :
    HasDerivAt (fun t => (matrix t).det) (Matrix.trace tangent) point := by
  have computed := ((derivative 0 0).mul (derivative 1 1)).sub
    ((derivative 0 1).mul (derivative 1 0))
  convert! computed using 1
  · ext t
    simp only [Matrix.det_fin_two, Pi.sub_apply, Pi.mul_apply]
  · simp [identity, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem binary_matrix_inv_hasDerivAt_one
    (matrix : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (tangent : Matrix (Fin 2) (Fin 2) ℝ)
    (point : ℝ) (identity : matrix point = 1)
    (derivative : ∀ row column, HasDerivAt (fun t => matrix t row column) (tangent row column) point)
    (row column : Fin 2) :
    HasDerivAt (fun t => (matrix t)⁻¹ row column) (-tangent row column) point := by
  have determinant := binary_matrix_det_hasDerivAt_one matrix tangent point identity derivative
  have inverse : HasDerivAt (fun t => ((matrix t).det)⁻¹) (-Matrix.trace tangent) point := by
    convert! determinant.inv (by simp [identity]) using 1
    simp [identity]
  fin_cases row <;> fin_cases column
  · convert! inverse.mul (derivative 1 1) using 1
    · ext t
      simp [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two]
    · simp [identity, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  · convert! inverse.mul (derivative 0 1).neg using 1
    · ext t
      simp [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two]
    · simp [identity]
  · convert! inverse.mul (derivative 1 0).neg using 1
    · ext t
      simp [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two]
    · simp [identity]
  · convert! inverse.mul (derivative 0 0) using 1
    · ext t
      simp [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two]
    · simp [identity, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem binary_group_inv_hasDerivAt_one
    (path : ℝ → BinaryRealGL) (tangent : Matrix (Fin 2) (Fin 2) ℝ)
    (point : ℝ) (identity : path point = 1)
    (derivative : ∀ row column, HasDerivAt (fun t => (path t).val row column) (tangent row column) point)
    (row column : Fin 2) :
    HasDerivAt (fun t => ((path t)⁻¹).val row column) (-tangent row column) point := by
  simpa only [GeneralLinearGroup.coe_inv] using
    binary_matrix_inv_hasDerivAt_one (fun t => (path t).val) tangent point
      (by simp [identity]) derivative row column

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
