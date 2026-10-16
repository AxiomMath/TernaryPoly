module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.SelfAdjoint

@[expose] public section


/-! The genuine normalized positive form and its logarithmic tangent in the fixed chart. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Matrix.Norms.Elementwise

/-- Actual determinant-one matrix defining the coefficient metric. -/
def coordinateForm (x : Coordinates) : Mat := determinantNormalize (reconstruct x)

theorem coordinateForm_positive (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    (coordinateForm x).PosDef := determinantNormalize_positive _ hx

theorem coordinateForm_symmetric (x : Coordinates) : (coordinateForm x).transpose = coordinateForm x := by
  simp only [coordinateForm, determinantNormalize, Matrix.transpose_smul,
    (Matrix.isHermitian_iff_isSymm.mp (reconstruct_isHermitian x)).eq]

theorem contDiffOn_coordinateForm : ContDiffOn ℝ ∞ coordinateForm positiveCoordinates :=
  contDiffOn_normalizedForm_coordinates

theorem coordinateForm_differentiable (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    DifferentiableAt ℝ coordinateForm x :=
  ((contDiffOn_coordinateForm x hx).contDiffAt (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)

/-- The actual differential of Q along a coordinate direction. -/
def formDerivative (x v : Coordinates) : Mat := fderiv ℝ coordinateForm x v

theorem hasDerivAt_coordinateForm_line (x : Coordinates) (hx : x ∈ positiveCoordinates) (v : Coordinates) :
    HasDerivAt (fun t : ℝ => coordinateForm (x + t • v)) (formDerivative x v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hQ : HasFDerivAt coordinateForm (fderiv ℝ coordinateForm x) (x + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using (coordinateForm_differentiable x hx).hasFDerivAt
  have hd := hQ.comp_hasDerivAt 0 hl
  convert! hd using 1

theorem formDerivative_symmetric (x : Coordinates) (hx : x ∈ positiveCoordinates) (v : Coordinates) :
    (formDerivative x v).transpose = formDerivative x v := by
  have hd := hasDerivAt_coordinateForm_line x hx v
  have ht : HasDerivAt (fun t : ℝ => (coordinateForm (x + t • v)).transpose)
      (formDerivative x v).transpose 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    exact hasDerivAt_pi.mp (hasDerivAt_pi.mp hd j) i
  simp only [coordinateForm_symmetric] at ht
  exact ht.unique hd

/-- The actual right logarithmic differential dQ Q-inverse. -/
def logarithmicForm (x v : Coordinates) : Mat := formDerivative x v * (coordinateForm x)⁻¹

/-- Exact scalar directional derivative of the coefficient metric. -/
theorem hasDerivAt_coordinateMetric_line (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) (p q : Coefficients n) :
    HasDerivAt (fun t : ℝ => coordinateCoefficientMetric n (x + t • v) p q)
      (-(coordinateCoefficientMetric n x p (coefficientInfinitesimal n (logarithmicForm x v) q))) 0 :=
  hasDerivAt_matrixMetric n (fun t => coordinateForm (x + t • v)) (coordinateForm x)
    (formDerivative x v) (coordinateForm_positive x hx).isUnit (hasDerivAt_coordinateForm_line x hx v)
    (by simp) p q

theorem logarithmicInfinitesimal_selfAdjoint (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) (p q : Coefficients n) :
    coordinateCoefficientMetric n x (coefficientInfinitesimal n (logarithmicForm x v) p) q =
      coordinateCoefficientMetric n x p (coefficientInfinitesimal n (logarithmicForm x v) q) :=
  metricInfinitesimal_selfAdjoint n (coordinateForm x) (formDerivative x v)
    (coordinateForm_positive x hx).isUnit (coordinateForm_symmetric x) (formDerivative_symmetric x hx v) p q

end TernaryPoly.PolynomialFormConnection
