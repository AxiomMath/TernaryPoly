module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Inverse

@[expose] public section


/-! The Maurer-Cartan identity for the literal right logarithmic differential. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

/-- The genuine second Frechet derivative of determinant normalization. -/
def formHessian (x u v : Coordinates) : Mat := fderiv ℝ (fderiv ℝ coordinateForm) x u v

theorem formHessian_symmetric (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates) :
    formHessian x u v = formHessian x v u := by
  exact (((contDiffOn_coordinateForm x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).eq u v

theorem hasDerivAt_formDerivative_line (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) :
    HasDerivAt (fun t : ℝ => formDerivative (x + t • u) v) (formHessian x u v) 0 := by
  have hs := ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_positiveCoordinates).mp
    contDiffOn_coordinateForm).2
  have hd := ((hs x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_coordinateLine x u)
    (by simp only [zero_smul, add_zero])
  have hh := h.clm_apply (hasDerivAt_const (0 : ℝ) v)
  convert! hh using 1
  simp [formHessian]
  rfl

/-- Differentiate dQ(v) Q-inverse along u, using the actual inverse derivative. -/
theorem hasDerivAt_logarithmicForm_line (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) :
    HasDerivAt (fun t : ℝ => logarithmicForm (x + t • u) v)
      (formHessian x u v * (coordinateForm x)⁻¹ - logarithmicForm x v * logarithmicForm x u) 0 := by
  have h := hasDerivAt_matrix_product (hasDerivAt_formDerivative_line x hx u v)
    (hasDerivAt_inverse_coordinateForm_line x hx u)
  convert! h using 1
  simp only [zero_smul, add_zero, logarithmicForm, mul_neg, sub_eq_add_neg, mul_assoc]

/-- The literal directional derivative of the logarithmic coefficient. -/
def logarithmicDerivative (x u v : Coordinates) : Mat :=
  fderiv ℝ (fun y => logarithmicForm y v) x u

theorem logarithmicDerivative_formula (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) :
    logarithmicDerivative x u v =
      formHessian x u v * (coordinateForm x)⁻¹ - logarithmicForm x v * logarithmicForm x u := by
  have hd := (((contDiffOn_logarithmicForm v x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  exact (hasDerivAt_matrixField_line _ x u hd).unique (hasDerivAt_logarithmicForm_line x hx u v)

/-- The right Maurer-Cartan sign is fixed by direct second differentiation. -/
theorem logarithmic_maurerCartan (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates) :
    logarithmicDerivative x u v - logarithmicDerivative x v u =
      logarithmicForm x u * logarithmicForm x v - logarithmicForm x v * logarithmicForm x u := by
  rw [logarithmicDerivative_formula x hx u v, logarithmicDerivative_formula x hx v u,
    formHessian_symmetric x hx u v]
  noncomm_ring

end TernaryPoly.PolynomialFormConnection
