module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Compatibility

@[expose] public section


/-! An explicit determinant derivative at a scalar matrix, for the actual normalization. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceTraceMetric
open scoped ContDiff Matrix.Norms.Elementwise

/-- Differentiate the six terms of the genuine three by three determinant. -/
theorem hasDerivAt_det_scalar (A : ℝ → Mat) (R : Mat) (s : ℝ)
    (hA : HasDerivAt A R 0) (h0 : A 0 = s • (1 : Mat)) :
    HasDerivAt (fun t => (A t).det) (s ^ 2 * R.trace) 0 := by
  have h (i j : Fin 3) : HasDerivAt (fun t => A t i j) (R i j) 0 :=
    hasDerivAt_pi.mp (hasDerivAt_pi.mp hA i) j
  have hd := ((((((h 0 0).mul (h 1 1)).mul (h 2 2)).sub
    (((h 0 0).mul (h 1 2)).mul (h 2 1))).sub
    (((h 0 1).mul (h 1 0)).mul (h 2 2))).add
    (((h 0 1).mul (h 1 2)).mul (h 2 0))).add
    (((h 0 2).mul (h 1 0)).mul (h 2 1))
  have he := hd.sub (((h 0 2).mul (h 1 1)).mul (h 2 0))
  convert! he using 1
  · funext t
    exact Matrix.det_fin_three (A t)
  · simp [h0, Matrix.trace, Fin.sum_univ_succ]
    ring

/-- The unnormalized trace-one chart derivative is exactly the tangent matrix. -/
theorem hasDerivAt_reconstruct_line (x v : Coordinates) :
    HasDerivAt (fun t : ℝ => reconstruct (x + t • v)) (tangentMatrix v) 0 := by
  have h := (hasFDerivAt_reconstruct (x + (0 : ℝ) • v)).comp_hasDerivAt
    0 (hasDerivAt_coordinateLine x v)
  convert! h using 1

/-- At I/3, all chart tangent matrices have zero first determinant variation. -/
theorem hasDerivAt_det_reconstruct_basepoint (v : Coordinates) :
    HasDerivAt (fun t : ℝ => (reconstruct (coordinateChart basepoint + t • v)).det) 0 0 := by
  have h0 : reconstruct (coordinateChart basepoint + (0 : ℝ) • v) = (1/3 : ℝ) • (1 : Mat) := by
    rw [zero_smul, add_zero, PolynomialFormMetric.reconstruct_basepoint]
    rw [PolynomialFormMetric.basepoint_matrix]
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply]
  have h := hasDerivAt_det_scalar _ _ (1/3) (hasDerivAt_reconstruct_line (coordinateChart basepoint) v) h0
  simpa only [tangentMatrix_trace, mul_zero] using h

end TernaryPoly.PolynomialFormConnection
