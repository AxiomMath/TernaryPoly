module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tangent.Metric

@[expose] public section

/-! Metric compatibility of the constructed genuine tangent connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

theorem hasDerivAt_logarithmicDerivative_line (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) :
    HasDerivAt (fun t : ℝ => logarithmicForm (x + t • u) v) (logarithmicDerivative x u v) 0 :=
  hasDerivAt_matrixField_line _ x u
    (((contDiffOn_logarithmicForm v x hx).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))

theorem hasDerivAt_coordinatePair_logarithmic (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v w : Coordinates) :
    HasDerivAt (fun t : ℝ => coordinatePair (x + t • u) v w)
      ((logarithmicDerivative x u v * logarithmicForm x w +
        logarithmicForm x v * logarithmicDerivative x u w).trace) 0 := by
  have hp := hasDerivAt_matrix_product (hasDerivAt_logarithmicDerivative_line x hx u v)
    (hasDerivAt_logarithmicDerivative_line x hx u w)
  have ht := traceCLM.hasFDerivAt.comp_hasDerivAt 0 hp
  have he : (fun t : ℝ => coordinatePair (x + t • u) v w) =ᶠ[nhds 0]
      (fun t : ℝ => (logarithmicForm (x + t • u) v * logarithmicForm (x + t • u) w).trace) := by
    filter_upwards [eventually_coordinateLine_positive x hx u] with t ht
    exact coordinatePair_logarithmic (x + t • u) ht v w
  have h := ht.congr_of_eventuallyEq he
  convert! h using 1
  simp only [zero_smul, add_zero]
  rfl

/-- Direct metric compatibility for coordinate-constant tangent fields. -/
theorem hasDerivAt_tangentMetric_connection_constants (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v w : Coordinates) :
    HasDerivAt (fun t : ℝ => coordinatePair (x + t • u) v w)
      (coordinatePair x (tangentConnection x u v) w + coordinatePair x v (tangentConnection x u w)) 0 := by
  convert hasDerivAt_coordinatePair_logarithmic x hx u v w using 1
  rw [coordinatePair_logarithmic x hx, coordinatePair_logarithmic x hx,
    logarithmicForm_tangentConnection x hx u v, logarithmicForm_tangentConnection x hx u w]
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_add, smul_eq_mul, mul_assoc]
  have hc := Matrix.trace_mul_comm (logarithmicForm x u) (logarithmicForm x v * logarithmicForm x w)
  simp only [mul_assoc] at hc
  rw [hc]
  ring

end TernaryPoly.PolynomialFormConnection
