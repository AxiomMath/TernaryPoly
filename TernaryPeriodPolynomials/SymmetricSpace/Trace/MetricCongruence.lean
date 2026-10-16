module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricAlgebra

@[expose] public section


/-! The invariant trace metric for positive matrix rays. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix

/-- The scalar direction is removed after taking the logarithmic tangent. -/
def tangentPair (S U V : Mat) : ℝ := tracePair (S⁻¹ * U) (S⁻¹ * V)

theorem tangentPair_formula (S U V : Mat) : tangentPair S U V =
    (S⁻¹ * U * (S⁻¹ * V)).trace - (S⁻¹ * U).trace * (S⁻¹ * V).trace / 3 :=
  tracePair_formula _ _

/-- Congruence transforms the logarithmic tangent by an actual similarity. -/
theorem inverse_congruence_tangent (g S : Matˣ) (U : Mat) :
    (↑(g * S * star g) : Mat)⁻¹ * ((g : Mat) * U * star (g : Mat)) =
      (↑((star g)⁻¹) : Mat) * ((↑S⁻¹ : Mat) * U) * (↑(star g) : Mat) := by
  rw [← coe_units_inv (g * S * star g)]
  simp [-coe_units_inv, mul_assoc]

/-- Invariance under arbitrary invertible frame changes, before normalization. -/
theorem tangentPair_congruence (g S : Matˣ) (U V : Mat) :
    tangentPair (↑(g * S * star g)) ((g : Mat) * U * star (g : Mat))
      ((g : Mat) * V * star (g : Mat)) = tangentPair (S : Mat) U V := by
  simp only [tangentPair, inverse_congruence_tangent]
  have h := tracePair_conjugate ((star g)⁻¹) ((↑S⁻¹ : Mat) * U) ((↑S⁻¹ : Mat) * V)
  simpa only [inv_inv, coe_units_inv] using h

/-- In a positive frame the invariant metric is exactly the scalar-removed Euclidean trace form. -/
theorem tangentPair_frame (g : Matˣ) (U V : Mat) :
    tangentPair ((g : Mat) * star (g : Mat)) ((g : Mat) * U * star (g : Mat))
      ((g : Mat) * V * star (g : Mat)) = tracePair U V := by
  simpa [tangentPair] using tangentPair_congruence g 1 U V

end TernaryPoly.SymmetricSpaceTraceMetric
