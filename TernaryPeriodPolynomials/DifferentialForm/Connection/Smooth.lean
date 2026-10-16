module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Basepoint

@[expose] public section


/-! Smoothness of the actual logarithmic form and metric connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

theorem contDiffOn_formDerivative (v : Coordinates) :
    ContDiffOn ℝ ∞ (fun x => formDerivative x v) positiveCoordinates :=
  ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_positiveCoordinates).mp
    contDiffOn_coordinateForm).2.clm_apply contDiffOn_const

theorem contDiffOn_inverse_coordinateForm :
    ContDiffOn ℝ ∞ (fun x => (coordinateForm x)⁻¹) positiveCoordinates :=
  contDiffOn_inverse contDiffOn_coordinateForm (fun x hx => (coordinateForm_positive x hx).isUnit)

theorem contDiffOn_logarithmicForm (v : Coordinates) :
    ContDiffOn ℝ ∞ (fun x => logarithmicForm x v) positiveCoordinates :=
  contDiffOn_matrix_mul (contDiffOn_formDerivative v) contDiffOn_inverse_coordinateForm

theorem contDiffOn_symmetricPart (n : ℕ) (v : Coordinates) :
    ContDiffOn ℝ ∞ (fun x => symmetricPart n x v) positiveCoordinates :=
  ((contDiff_infinitesimalCLM n).comp_contDiffOn (contDiffOn_logarithmicForm v)).const_smul (1/2 : ℝ)

theorem contDiffOn_connectionMatrix (n : ℕ) (v : Coordinates) :
    ContDiffOn ℝ ∞ (fun x => connectionMatrix n x v) positiveCoordinates :=
  (contDiffOn_symmetricPart n v).neg

@[simp] theorem formDerivative_add (x u v : Coordinates) :
    formDerivative x (u + v) = formDerivative x u + formDerivative x v :=
  map_add (fderiv ℝ coordinateForm x) u v

@[simp] theorem formDerivative_smul (x v : Coordinates) (c : ℝ) :
    formDerivative x (c • v) = c • formDerivative x v :=
  map_smul (fderiv ℝ coordinateForm x) c v

@[simp] theorem logarithmicForm_add (x u v : Coordinates) :
    logarithmicForm x (u + v) = logarithmicForm x u + logarithmicForm x v := by
  simp only [logarithmicForm, formDerivative_add, add_mul]

@[simp] theorem logarithmicForm_smul (x v : Coordinates) (c : ℝ) :
    logarithmicForm x (c • v) = c • logarithmicForm x v := by
  simp only [logarithmicForm, formDerivative_smul, Matrix.smul_mul]

@[simp] theorem symmetricPart_add (n : ℕ) (x u v : Coordinates) :
    symmetricPart n x (u + v) = symmetricPart n x u + symmetricPart n x v := by
  apply ContinuousLinearMap.ext
  intro p
  simp [symmetricPart, smul_add]

@[simp] theorem symmetricPart_smul (n : ℕ) (x v : Coordinates) (c : ℝ) :
    symmetricPart n x (c • v) = c • symmetricPart n x v := by
  apply ContinuousLinearMap.ext
  intro p
  simp only [symmetricPart, _root_.smul_apply, infinitesimalCLM_apply,
    logarithmicForm_smul, coefficientInfinitesimal_smul]
  exact smul_comm _ _ _

end TernaryPoly.PolynomialFormConnection
