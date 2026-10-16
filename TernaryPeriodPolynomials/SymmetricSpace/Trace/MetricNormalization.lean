module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricCongruence

@[expose] public section

/-! The invariant metric survives trace normalization and radial derivative corrections. -/
namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix

@[simp] theorem tracePair_add_scalar_left (A B : Mat) (c : ℝ) :
    tracePair (A + c • 1) B = tracePair A B := by
  simp only [tracePair, center_add_scalar]

@[simp] theorem tracePair_add_scalar_right (A B : Mat) (c : ℝ) :
    tracePair A (B + c • 1) = tracePair A B := by
  simp only [tracePair, center_add_scalar]

theorem tangentPair_add_radial (S : Matˣ) (U V : Mat) (a b : ℝ) :
    tangentPair (S : Mat) (U + a • (S : Mat)) (V + b • (S : Mat)) = tangentPair S U V := by
  simp only [tangentPair]
  rw [← coe_units_inv S]
  simp [-coe_units_inv, mul_add]

/-- Scaling the base form and both tangents by the same nonzero scalar leaves
its metric unchanged. -/
theorem tangentPair_scale (S : Matˣ) (U V : Mat) (c : ℝ) (hc : c ≠ 0) :
    tangentPair (c • (S : Mat)) (c • U) (c • V) = tangentPair S U V := by
  let := invertibleOfNonzero hc
  have hd : IsUnit (S : Mat).det := ((S : Mat).isUnit_iff_isUnit_det).mp S.isUnit
  simp [tangentPair, Matrix.inv_smul (S : Mat) c hd, invOf_eq_inv, smul_smul, hc]

/-- Full algebraic invariance for the normalized congruence derivative,
including the radial correction in each tangent direction. -/
theorem tangentPair_normalized_congruence (g S : Matˣ) (U V : Mat)
    (c : ℝ) (hc : c ≠ 0) (a b : ℝ) :
    tangentPair (c • (↑(g * S * star g) : Mat))
      (c • ((g : Mat) * U * star (g : Mat) + a • (↑(g * S * star g) : Mat)))
      (c • ((g : Mat) * V * star (g : Mat) + b • (↑(g * S * star g) : Mat))) =
      tangentPair S U V := by
  rw [tangentPair_scale _ _ _ c hc, tangentPair_add_radial, tangentPair_congruence]

end TernaryPoly.SymmetricSpaceTraceMetric
