module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Smooth

@[expose] public section


/-! Differentiate the actual inverse by differentiating the matrix identity. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

theorem hasDerivAt_matrixField_line (A : Coordinates → Mat) (x v : Coordinates)
    (hA : DifferentiableAt ℝ A x) :
    HasDerivAt (fun t : ℝ => A (x + t • v)) (fderiv ℝ A x v) 0 := by
  have h : HasFDerivAt A (fderiv ℝ A x) (x + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using hA.hasFDerivAt
  have hh := h.comp_hasDerivAt 0 (hasDerivAt_coordinateLine x v)
  convert! hh using 1

/-- The coordinate line remains in the genuine positive cone near zero. -/
theorem eventually_coordinateLine_positive (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) : ∀ᶠ t : ℝ in nhds 0, x + t • v ∈ positiveCoordinates := by
  have hc := (hasDerivAt_coordinateLine x v).continuousAt
  have hn : positiveCoordinates ∈ nhds (x + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using isOpen_positiveCoordinates.mem_nhds hx
  exact hc.preimage_mem_nhds hn

/-- The actual inverse derivative, without replacing the matrix norm or assuming an inverse rule. -/
theorem inverseFormDerivative (x : Coordinates) (hx : x ∈ positiveCoordinates) (v : Coordinates) :
    fderiv ℝ (fun y => (coordinateForm y)⁻¹) x v =
      -((coordinateForm x)⁻¹ * formDerivative x v * (coordinateForm x)⁻¹) := by
  have hi := (((contDiffOn_inverse_coordinateForm x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  have hd := hasDerivAt_matrixField_line _ x v hi
  have hp := hasDerivAt_matrix_product (hasDerivAt_coordinateForm_line x hx v) hd
  have hc : HasDerivAt (fun _ : ℝ => (1 : Mat))
      (formDerivative x v * (coordinateForm x)⁻¹ +
        coordinateForm x * fderiv ℝ (fun y => (coordinateForm y)⁻¹) x v) 0 := by
    have he : (fun _ : ℝ => (1 : Mat)) =ᶠ[nhds 0]
        (fun t : ℝ => coordinateForm (x + t • v) * (coordinateForm (x + t • v))⁻¹) := by
      filter_upwards [eventually_coordinateLine_positive x hx v] with t ht
      exact (Matrix.mul_nonsing_inv _
        ((coordinateForm (x + t • v)).isUnit_iff_isUnit_det.mp (coordinateForm_positive (x + t • v) ht).isUnit)).symm
    have hh := hp.congr_of_eventuallyEq he
    convert! hh using 1
    simp only [zero_smul, add_zero]
  have hz := hc.unique (hasDerivAt_const (0 : ℝ) (1 : Mat))
  have he := congrArg (fun A : Mat => (coordinateForm x)⁻¹ * A) hz
  have hinv := Matrix.nonsing_inv_mul (coordinateForm x)
    ((coordinateForm x).isUnit_iff_isUnit_det.mp (coordinateForm_positive x hx).isUnit)
  simp only [mul_add, ← mul_assoc, hinv, one_mul, mul_zero] at he
  exact eq_neg_of_add_eq_zero_right he

/-- The actual inverse field differentiated along a chart line. -/
theorem hasDerivAt_inverse_coordinateForm_line (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) :
    HasDerivAt (fun t : ℝ => (coordinateForm (x + t • v))⁻¹)
      (-((coordinateForm x)⁻¹ * formDerivative x v * (coordinateForm x)⁻¹)) 0 := by
  rw [← inverseFormDerivative x hx v]
  exact hasDerivAt_matrixField_line _ x v
    (((contDiffOn_inverse_coordinateForm x hx).contDiffAt
      (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))

end TernaryPoly.PolynomialFormConnection
