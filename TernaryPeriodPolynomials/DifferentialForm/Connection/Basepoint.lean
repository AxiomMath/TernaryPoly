module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Determinant

@[expose] public section


/-! The exact one-half normalization of the actual symmetric coefficient connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open PolynomialFormMetric
open scoped ContDiff Matrix.Norms.Elementwise

@[simp] theorem coordinateForm_basepoint : coordinateForm (coordinateChart basepoint) = 1 := by
  rw [coordinateForm, reconstruct_basepoint]
  exact normalizedForm_basepoint

/-- The normalization factor itself is forced to be three at the trace-one identity. -/
theorem normalizationScalar_basepoint :
    (reconstruct (coordinateChart basepoint)).det ^ (-(1/3 : ℝ)) = 3 := by
  have h := congrArg (fun A : Mat => A 0 0) coordinateForm_basepoint
  change (reconstruct (coordinateChart basepoint)).det ^ (-(1/3 : ℝ)) *
    (reconstruct (coordinateChart basepoint)) 0 0 = 1 at h
  rw [reconstruct_basepoint, basepoint_matrix] at h ⊢
  rw [Matrix.diagonal_apply_eq] at h
  linarith

/-- Literal derivative of determinant normalization at the base point. -/
theorem hasDerivAt_coordinateForm_basepoint (v : Coordinates) :
    HasDerivAt (fun t : ℝ => coordinateForm (coordinateChart basepoint + t • v))
      ((3 : ℝ) • tangentMatrix v) 0 := by
  have hdet : (reconstruct (coordinateChart basepoint + (0 : ℝ) • v)).det ≠ 0 := by
    rw [zero_smul, add_zero, reconstruct_basepoint]
    exact basepoint.property.1.det_pos.ne'
  have hs := (hasDerivAt_det_reconstruct_basepoint v).rpow_const
    (p := -(1/3 : ℝ)) (Or.inl hdet)
  have hs' : HasDerivAt (fun t : ℝ =>
      (reconstruct (coordinateChart basepoint + t • v)).det ^ (-(1/3 : ℝ))) 0 0 := by
    simpa only [zero_mul] using hs
  have h := hs'.smul (hasDerivAt_reconstruct_line (coordinateChart basepoint) v)
  convert! h using 1
  simp only [zero_smul, add_zero, normalizationScalar_basepoint]

theorem formDerivative_basepoint (v : Coordinates) :
    formDerivative (coordinateChart basepoint) v = (3 : ℝ) • tangentMatrix v :=
  (hasDerivAt_coordinateForm_line (coordinateChart basepoint) (extract_mem basepoint) v).unique
    (hasDerivAt_coordinateForm_basepoint v)

theorem logarithmicForm_basepoint (v : Coordinates) :
    logarithmicForm (coordinateChart basepoint) v = (3 : ℝ) • tangentMatrix v := by
  rw [logarithmicForm, formDerivative_basepoint, coordinateForm_basepoint, inv_one, mul_one]

theorem logarithmicForm_baseFrame (i : Fin 5) :
    logarithmicForm (coordinateChart basepoint) (baseFrame i) = tangentFrame i := by
  rw [logarithmicForm_basepoint, tangentMatrix_baseFrame, smul_smul]
  norm_num

/-- The B=tr frame has half the infinitesimal GL connection action. -/
theorem symmetricPart_baseFrame (n : ℕ) (i : Fin 5) :
    symmetricPart n (coordinateChart basepoint) (baseFrame i) =
      (1/2 : ℝ) • infinitesimalCLM n (tangentFrame i) := by
  rw [symmetricPart, logarithmicForm_baseFrame]

end TernaryPoly.PolynomialFormConnection
