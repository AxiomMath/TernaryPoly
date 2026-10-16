module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Split

@[expose] public section


/-! Metric compatibility for arbitrary differentiable coefficient sections. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Matrix.Norms.Elementwise

theorem hasDerivAt_coordinateLine (x v : Coordinates) :
    HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
  convert! (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
  simp

theorem hasDerivAt_section_line (n : ℕ) (f : Coordinates → Coefficients n)
    (x v : Coordinates) (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
  have h : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using hf.hasFDerivAt
  have hh := h.comp_hasDerivAt 0 (hasDerivAt_coordinateLine x v)
  convert! hh using 1

theorem hasDerivAt_coordinateMetric_operator (n : ℕ) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (v : Coordinates) :
    HasDerivAt (fun t : ℝ => coordinateCoefficientMetric n (x + t • v))
      (fderiv ℝ (coordinateCoefficientMetric n) x v) 0 := by
  have hd := (((contDiffOn_coordinateCoefficientMetric n) x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp)
  have h : HasFDerivAt (coordinateCoefficientMetric n)
      (fderiv ℝ (coordinateCoefficientMetric n) x) (x + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using hd.hasFDerivAt
  have hh := HasFDerivAt.comp_hasDerivAt
    (E := Coefficients n →L[ℝ] Coefficients n →L[ℝ] ℝ) (F := Coordinates)
    (l := coordinateCoefficientMetric n) (l' := fderiv ℝ (coordinateCoefficientMetric n) x)
    0 h (hasDerivAt_coordinateLine x v)
  convert! hh using 1

/-- The exact operator-valued metric differential equals the two connection terms. -/
theorem metricDerivative_apply (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) (p q : Coefficients n) :
    fderiv ℝ (coordinateCoefficientMetric n) x v p q =
      coordinateCoefficientMetric n x (connectionMatrix n x v p) q +
        coordinateCoefficientMetric n x p (connectionMatrix n x v q) := by
  have h := ((hasDerivAt_coordinateMetric_operator n x hx v).clm_apply
    (hasDerivAt_const (0 : ℝ) p)).clm_apply (hasDerivAt_const (0 : ℝ) q)
  have h' : HasDerivAt (fun t : ℝ => coordinateCoefficientMetric n (x + t • v) p q)
      (fderiv ℝ (coordinateCoefficientMetric n) x v p q) 0 := by
    simpa only [map_zero, add_zero] using h
  exact h'.unique (hasDerivAt_metric_connection_constants n x hx v p q)

/-- Genuine metric compatibility, including derivatives of both coefficient sections. -/
theorem hasDerivAt_metric_connection (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) (f g : Coordinates → Coefficients n)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (fun t : ℝ => coordinateCoefficientMetric n (x + t • v)
      (f (x + t • v)) (g (x + t • v)))
      (coordinateCoefficientMetric n x (covariantDerivative n f x v) (g x) +
        coordinateCoefficientMetric n x (f x) (covariantDerivative n g x v)) 0 := by
  have h := ((hasDerivAt_coordinateMetric_operator n x hx v).clm_apply
    (hasDerivAt_section_line n f x v hf)).clm_apply (hasDerivAt_section_line n g x v hg)
  convert! h using 1
  simp only [zero_smul, add_zero, covariantDerivative, map_add, _root_.add_apply]
  rw [metricDerivative_apply n x hx v (f x) (g x)]
  ring

end TernaryPoly.PolynomialFormConnection
