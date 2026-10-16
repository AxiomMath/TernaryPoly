module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Jacobi

@[expose] public section

/-! The actual normalized tangent correction underlying the Levi-Civita connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

theorem formHessian_transpose (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates) :
    (formHessian x u v).transpose = formHessian x u v := by
  have hd := hasDerivAt_formDerivative_line x hx u v
  have ht : HasDerivAt (fun t : ℝ => (formDerivative (x + t • u) v).transpose)
      (formHessian x u v).transpose 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hd j) i
  have he : (fun t : ℝ => formDerivative (x + t • u) v) =ᶠ[nhds 0]
      (fun t : ℝ => (formDerivative (x + t • u) v).transpose) := by
    filter_upwards [eventually_coordinateLine_positive x hx u] with t ht
    exact (formDerivative_symmetric (x + t • u) ht v).symm
  exact (ht.congr_of_eventuallyEq he).unique hd

/-- The actual normalized second derivative minus the symmetric-space product correction. -/
def tangentCorrection (x u v : Coordinates) : Mat :=
  formHessian x u v - (1/2 : ℝ) •
    (formDerivative x u * (coordinateForm x)⁻¹ * formDerivative x v +
      formDerivative x v * (coordinateForm x)⁻¹ * formDerivative x u)

theorem tangentCorrection_swap (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates) :
    tangentCorrection x u v = tangentCorrection x v u := by
  rw [tangentCorrection, tangentCorrection, formHessian_symmetric x hx u v, add_comm]

theorem tangentCorrection_symmetric (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates) :
    (tangentCorrection x u v).transpose = tangentCorrection x u v := by
  simp only [tangentCorrection, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_add,
    Matrix.transpose_mul, Matrix.transpose_nonsing_inv, coordinateForm_symmetric,
    formDerivative_symmetric x hx u, formDerivative_symmetric x hx v, formHessian_transpose x hx u v]
  rw [add_comm]
  simp only [mul_assoc]

/-- The logarithmic version of the tangent correction is the derivative of C minus half its bracket. -/
theorem tangentCorrection_logarithmic (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates) :
    tangentCorrection x u v * (coordinateForm x)⁻¹ =
      logarithmicDerivative x u v - (1/2 : ℝ) •
        (logarithmicForm x u * logarithmicForm x v - logarithmicForm x v * logarithmicForm x u) := by
  rw [logarithmicDerivative_formula x hx u v]
  simp only [tangentCorrection, sub_mul, Matrix.smul_mul, add_mul, logarithmicForm, mul_assoc]
  module

/-- The correction is a genuine tangent to the determinant-one symmetric space. -/
theorem tangentCorrection_trace (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates) :
    (tangentCorrection x u v * (coordinateForm x)⁻¹).trace = 0 := by
  rw [tangentCorrection_logarithmic x hx u v, Matrix.trace_sub, logarithmicDerivative_trace x hx u v,
    Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_comm (logarithmicForm x u) (logarithmicForm x v)]
  simp

end TernaryPoly.PolynomialFormConnection
