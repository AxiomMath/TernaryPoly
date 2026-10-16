module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricFrames
public import TernaryPeriodPolynomials.SymmetricSpace.PositiveAction

@[expose] public section


/-! The actual positive-form model is homogeneous under real congruence. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian

open Matrix SymmetricSpacePositive SymmetricSpaceTraceMetric

/-- Positive frames give an actual real invertible matrix carrying any form to any other form. -/
theorem exists_act_eq (S T : Space) : ∃ g : RealGL, act g S = T := by
  obtain ⟨s, hs⟩ := exists_positive_frame S.val S.property.1
  obtain ⟨t, ht⟩ := exists_positive_frame T.val T.property.1
  refine ⟨t * s⁻¹, ?_⟩
  apply Subtype.ext
  change normalize (conjugate (t * s⁻¹) S.val) = T.val
  have h : conjugate (t * s⁻¹) S.val = T.val := by
    rw [hs, ht]
    simp [conjugate, mul_assoc, ← star_mul]
  rw [h, normalize_of_trace_one _ T.property.2]

end TernaryPoly.SymmetricSpaceRiemannian
