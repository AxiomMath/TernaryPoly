module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Tangent.Properties

@[expose] public section


/-! Genuine tangent covariant derivatives and metric compatibility for varying fields. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

/-- Covariant differentiation of a genuine tangent field in the fixed chart. -/
def tangentCovariantDerivative (V : Coordinates → Coordinates) (x u : Coordinates) : Coordinates :=
  fderiv ℝ V x u + tangentConnection x u (V x)

/-- The torsion is zero for arbitrary actual coordinate tangent fields. -/
theorem tangentCovariantDerivative_torsion (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (U V : Coordinates → Coordinates) :
    tangentCovariantDerivative V x (U x) - tangentCovariantDerivative U x (V x) =
      fderiv ℝ V x (U x) - fderiv ℝ U x (V x) := by
  rw [tangentCovariantDerivative, tangentCovariantDerivative, tangentConnection_symmetric x hx (U x) (V x)]
  abel

theorem hasDerivAt_tangentSection_line (V : Coordinates → Coordinates) (x u : Coordinates)
    (hV : DifferentiableAt ℝ V x) :
    HasDerivAt (fun t : ℝ => V (x + t • u)) (fderiv ℝ V x u) 0 := by
  have h := hV.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hasDerivAt_coordinateLine x u)
    (by simp only [zero_smul, add_zero])
  convert! h using 1

theorem hasDerivAt_tangentMetric_operator (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) :
    HasDerivAt (fun t : ℝ => coordinateContinuousBilin (x + t • u))
      (fderiv ℝ coordinateContinuousBilin x u) 0 := by
  have hd := (((contDiffOn_coordinateContinuousBilin x hx).contDiffAt
    (isOpen_positiveCoordinates.mem_nhds hx)).differentiableAt (by simp))
  have h := HasFDerivAt.comp_hasDerivAt_of_eq
    (E := Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ) (F := Coordinates)
    (l := coordinateContinuousBilin) (l' := fderiv ℝ coordinateContinuousBilin x)
    0 hd.hasFDerivAt (hasDerivAt_coordinateLine x u) (by simp only [zero_smul, add_zero])
  convert! h using 1

theorem tangentMetricDerivative_apply (x : Coordinates) (hx : x ∈ positiveCoordinates) (u v w : Coordinates) :
    fderiv ℝ coordinateContinuousBilin x u v w =
      coordinateContinuousBilin x (tangentConnection x u v) w +
        coordinateContinuousBilin x v (tangentConnection x u w) := by
  have h := ((hasDerivAt_tangentMetric_operator x hx u).clm_apply
    (hasDerivAt_const (0 : ℝ) v)).clm_apply (hasDerivAt_const (0 : ℝ) w)
  have h' : HasDerivAt (fun t : ℝ => coordinatePair (x + t • u) v w)
      (fderiv ℝ coordinateContinuousBilin x u v w) 0 := by
    simpa only [map_zero, add_zero, coordinateContinuousBilin_apply] using h
  exact h'.unique (hasDerivAt_tangentMetric_connection_constants x hx u v w)

/-- Full compatibility with the tangent metric, including both varying tangent fields. -/
theorem hasDerivAt_tangentMetric_connection (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (u : Coordinates) (V W : Coordinates → Coordinates)
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x) :
    HasDerivAt (fun t : ℝ => coordinateContinuousBilin (x + t • u) (V (x + t • u)) (W (x + t • u)))
      (coordinateContinuousBilin x (tangentCovariantDerivative V x u) (W x) +
        coordinateContinuousBilin x (V x) (tangentCovariantDerivative W x u)) 0 := by
  have h := ((hasDerivAt_tangentMetric_operator x hx u).clm_apply
    (hasDerivAt_tangentSection_line V x u hV)).clm_apply (hasDerivAt_tangentSection_line W x u hW)
  convert! h using 1
  simp only [zero_smul, add_zero, tangentCovariantDerivative, map_add, _root_.add_apply]
  rw [tangentMetricDerivative_apply x hx u (V x) (W x)]
  ring

end TernaryPoly.PolynomialFormConnection
