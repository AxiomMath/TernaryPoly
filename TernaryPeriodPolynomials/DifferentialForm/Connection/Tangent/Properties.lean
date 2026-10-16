module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tangent.Compatibility

@[expose] public section

/-! Bilinearity and smoothness of the actual tangent connection coefficients. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

theorem extract_add (A B : Mat) : extract (A + B) = extract A + extract B := by
  ext i
  fin_cases i <;> rfl

theorem extract_smul (c : ℝ) (A : Mat) : extract (c • A) = c • extract A := by
  ext i
  fin_cases i <;> rfl

theorem formHessian_add_left (x u v w : Coordinates) :
    formHessian x (u + v) w = formHessian x u w + formHessian x v w := by
  exact congrArg (fun L => L w) (map_add (fderiv ℝ (fderiv ℝ coordinateForm) x) u v)

theorem formHessian_smul_left (x u v : Coordinates) (c : ℝ) :
    formHessian x (c • u) v = c • formHessian x u v := by
  exact congrArg (fun L => L v) (map_smul (fderiv ℝ (fderiv ℝ coordinateForm) x) c u)

theorem tangentCorrection_add_left (x u v w : Coordinates) :
    tangentCorrection x (u + v) w = tangentCorrection x u w + tangentCorrection x v w := by
  simp only [tangentCorrection, formHessian_add_left, formDerivative_add, add_mul, mul_add, smul_add]
  module

theorem tangentCorrection_smul_left (x u v : Coordinates) (c : ℝ) :
    tangentCorrection x (c • u) v = c • tangentCorrection x u v := by
  simp only [tangentCorrection, formHessian_smul_left, formDerivative_smul, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, smul_sub, smul_smul]
  module

theorem tangentConnection_add_left (x u v w : Coordinates) :
    tangentConnection x (u + v) w = tangentConnection x u w + tangentConnection x v w := by
  rw [tangentConnection, tangentCorrection_add_left, map_add, extract_add]
  rfl

theorem tangentConnection_smul_left (x u v : Coordinates) (c : ℝ) :
    tangentConnection x (c • u) v = c • tangentConnection x u v := by
  rw [tangentConnection, tangentCorrection_smul_left, map_smul, extract_smul]
  rfl

theorem tangentConnection_add_right (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v w : Coordinates) :
    tangentConnection x u (v + w) = tangentConnection x u v + tangentConnection x u w := by
  rw [tangentConnection_symmetric x hx u (v + w), tangentConnection_add_left,
    tangentConnection_symmetric x hx v u, tangentConnection_symmetric x hx w u]

theorem tangentConnection_smul_right (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) (c : ℝ) :
    tangentConnection x u (c • v) = c • tangentConnection x u v := by
  rw [tangentConnection_symmetric x hx u (c • v), tangentConnection_smul_left,
    tangentConnection_symmetric x hx v u]

theorem contDiffOn_formHessian (u v : Coordinates) :
    ContDiffOn ℝ ∞ (fun x => formHessian x u v) positiveCoordinates := by
  have h1 := ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_positiveCoordinates).mp contDiffOn_coordinateForm).2
  have h2 := ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_positiveCoordinates).mp h1).2
  exact (h2.clm_apply (contDiffOn_const (c := u))).clm_apply (contDiffOn_const (c := v))

theorem contDiffOn_tangentCorrection (u v : Coordinates) :
    ContDiffOn ℝ ∞ (fun x => tangentCorrection x u v) positiveCoordinates := by
  have h (a b : Coordinates) := contDiffOn_matrix_mul
    (contDiffOn_matrix_mul (contDiffOn_formDerivative a) contDiffOn_inverse_coordinateForm)
    (contDiffOn_formDerivative b)
  exact (contDiffOn_formHessian u v).sub (((h u v).add (h v u)).const_smul (1/2 : ℝ))

theorem contDiffOn_tangentConnection (u v : Coordinates) :
    ContDiffOn ℝ ∞ (fun x => tangentConnection x u v) positiveCoordinates := by
  have hi := (contDiffOn_trace contDiffOn_coordinateForm).inv
    (fun x hx => (coordinateForm_positive x hx).trace_pos.ne')
  have hw := contDiffOn_tangentCorrection u v
  have hs := hi.smul (hw.add ((hi.neg.mul (contDiffOn_trace hw)).smul contDiffOn_coordinateForm))
  have he : (fun x => tangentConnection x u v) = (fun x => extract ((coordinateForm x).trace⁻¹ •
      (tangentCorrection x u v + (-(coordinateForm x).trace⁻¹ * (tangentCorrection x u v).trace) • coordinateForm x))) := by
    funext x
    exact congrArg extract (normalizationDerivative_apply (coordinateForm x) (tangentCorrection x u v))
  rw [he]
  exact contDiff_extract.comp_contDiffOn hs

end TernaryPoly.PolynomialFormConnection
