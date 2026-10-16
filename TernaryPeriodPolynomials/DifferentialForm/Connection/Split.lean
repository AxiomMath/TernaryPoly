module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Geometry

@[expose] public section


/-! The metric connection obtained from the actual flat polynomial coefficient system. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Matrix.Norms.Elementwise

/-- Symmetric part of the flat connection in the coefficient trivialization. -/
def symmetricPart (n : ℕ) (x v : Coordinates) : Coefficients n →L[ℝ] Coefficients n :=
  (1 / 2 : ℝ) • infinitesimalCLM n (logarithmicForm x v)

/-- The actual metric connection matrix. -/
def connectionMatrix (n : ℕ) (x v : Coordinates) : Coefficients n →L[ℝ] Coefficients n :=
  -symmetricPart n x v

/-- Covariant derivative in the fixed coordinate trivialization. -/
def covariantDerivative (n : ℕ) (f : Coordinates → Coefficients n) (x v : Coordinates) : Coefficients n :=
  fderiv ℝ f x v + connectionMatrix n x v (f x)

theorem flat_eq_covariant_add_symmetric (n : ℕ) (f : Coordinates → Coefficients n) (x v : Coordinates) :
    fderiv ℝ f x v = covariantDerivative n f x v + symmetricPart n x v (f x) := by
  simp [covariantDerivative, connectionMatrix]

theorem symmetricPart_selfAdjoint (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) (p q : Coefficients n) :
    coordinateCoefficientMetric n x (symmetricPart n x v p) q =
      coordinateCoefficientMetric n x p (symmetricPart n x v q) := by
  simp only [symmetricPart, _root_.smul_apply, infinitesimalCLM_apply,
    map_smul, _root_.smul_apply, smul_eq_mul]
  rw [logarithmicInfinitesimal_selfAdjoint n x hx v p q]

/-- Compatibility for the constant coefficient sections; the metric is genuinely differentiated. -/
theorem hasDerivAt_metric_connection_constants (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (v : Coordinates) (p q : Coefficients n) :
    HasDerivAt (fun t : ℝ => coordinateCoefficientMetric n (x + t • v) p q)
      (coordinateCoefficientMetric n x (connectionMatrix n x v p) q +
        coordinateCoefficientMetric n x p (connectionMatrix n x v q)) 0 := by
  have h := hasDerivAt_coordinateMetric_line n x hx v p q
  convert h using 1
  simp only [connectionMatrix, symmetricPart, _root_.neg_apply,
    _root_.smul_apply, infinitesimalCLM_apply, map_neg, map_smul,
    _root_.neg_apply, _root_.smul_apply, smul_eq_mul]
  rw [logarithmicInfinitesimal_selfAdjoint n x hx v p q]
  ring

end TernaryPoly.PolynomialFormConnection
