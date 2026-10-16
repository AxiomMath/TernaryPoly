module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Retraction

@[expose] public section


/-! The actual tangent connection and parallelism of the symmetric coefficient one-form. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

/-- The normalized symmetric-space tangent connection pulled back by the literal inverse chart. -/
def tangentConnection (x u v : Coordinates) : Coordinates :=
  extract (normalizationDerivative (coordinateForm x) (tangentCorrection x u v))

/-- Symmetry of the connection coefficients is the actual torsion-free identity in this chart. -/
theorem tangentConnection_symmetric (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates) :
    tangentConnection x u v = tangentConnection x v u := by
  rw [tangentConnection, tangentConnection, tangentCorrection_swap x hx u v]

/-- The constructed connection has exactly the genuine normalized tangent correction. -/
theorem formDerivative_tangentConnection (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates) :
    formDerivative x (tangentConnection x u v) = tangentCorrection x u v :=
  formDerivative_matrixChart_tangent x hx _ (tangentCorrection_symmetric x hx u v)
    (tangentCorrection_trace x hx u v)

theorem logarithmicForm_tangentConnection (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v : Coordinates) :
    logarithmicForm x (tangentConnection x u v) =
      logarithmicDerivative x u v - (1/2 : ℝ) •
        (logarithmicForm x u * logarithmicForm x v - logarithmicForm x v * logarithmicForm x u) := by
  rw [logarithmicForm, formDerivative_tangentConnection x hx u v, tangentCorrection_logarithmic x hx u v]

/-- The full covariant derivative of Ψ includes the actual tangent-connection correction. -/
def symmetricCovariantDerivative (n : ℕ) (x u v : Coordinates) (p : Coefficients n) : Coefficients n :=
  fderiv ℝ (fun y => symmetricPart n y v p) x u +
    connectionMatrix n x u (symmetricPart n x v p) - symmetricPart n x v (connectionMatrix n x u p) -
    symmetricPart n x (tangentConnection x u v) p

/-- Actual parallelism of the symmetric coefficient one-form for the constructed connections. -/
theorem symmetricPart_parallel (n : ℕ) (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u v : Coordinates) (p : Coefficients n) : symmetricCovariantDerivative n x u v p = 0 := by
  rw [symmetricCovariantDerivative, symmetricPartDerivative_apply n x hx u v p]
  simp only [connectionMatrix, symmetricPart, _root_.neg_apply, _root_.smul_apply, infinitesimalCLM_apply,
    map_neg, map_smul]
  rw [logarithmicForm_tangentConnection x hx u v, coefficientInfinitesimal_sub,
    coefficientInfinitesimal_smul, coefficientInfinitesimal_commutator]
  module

end TernaryPoly.PolynomialFormConnection
