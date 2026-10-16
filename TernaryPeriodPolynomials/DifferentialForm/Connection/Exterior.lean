module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Curvature

@[expose] public section


/-! The symmetric endomorphism one-form is closed for the actual metric connection. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

theorem symmetricExteriorDerivative_apply (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) (p : Coefficients n) :
    fderiv ℝ (fun y => symmetricPart n y v p) x u -
      fderiv ℝ (fun y => symmetricPart n y u p) x v =
      (1/2 : ℝ) • coefficientInfinitesimal n
        (logarithmicForm x u * logarithmicForm x v - logarithmicForm x v * logarithmicForm x u) p := by
  rw [symmetricPartDerivative_apply n x hx u v p, symmetricPartDerivative_apply n x hx v u p,
    ← smul_sub, ← coefficientInfinitesimal_sub, logarithmic_maurerCartan x hx u v]

/-- The actual covariant exterior derivative on endomorphism-valued one-forms. -/
def covariantExteriorSymmetric (n : ℕ) (x u v : Coordinates) (p : Coefficients n) : Coefficients n :=
  fderiv ℝ (fun y => symmetricPart n y v p) x u -
    fderiv ℝ (fun y => symmetricPart n y u p) x v +
    connectionMatrix n x u (symmetricPart n x v p) - symmetricPart n x v (connectionMatrix n x u p) -
    connectionMatrix n x v (symmetricPart n x u p) + symmetricPart n x u (connectionMatrix n x v p)

/-- No closedness premise is used: it follows from actual metric differentiation. -/
theorem covariantExteriorSymmetric_zero (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) (p : Coefficients n) : covariantExteriorSymmetric n x u v p = 0 := by
  rw [covariantExteriorSymmetric, symmetricExteriorDerivative_apply n x hx u v p,
    coefficientInfinitesimal_commutator]
  simp only [connectionMatrix, symmetricPart, _root_.neg_apply, _root_.smul_apply,
    infinitesimalCLM_apply, map_neg, map_smul]
  module

end TernaryPoly.PolynomialFormConnection
