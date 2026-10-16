module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricFrames
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricCongruence

@[expose] public section

/-! Positive definiteness on the actual trace-one tangent hyperplane. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix

/-- Pull a tangent matrix to an invertible Euclidean frame. -/
def framePullback (g : Matˣ) (U : Mat) : Mat := (↑g⁻¹ : Mat) * U * star (↑g⁻¹ : Mat)

theorem framePullback_isHermitian (g : Matˣ) (U : Mat) (hU : U.IsHermitian) :
    (framePullback g U).IsHermitian := by
  have h := isHermitian_conjTranspose_mul_mul (star (↑g⁻¹ : Mat)) hU
  simpa only [framePullback, star_eq_conjTranspose, conjTranspose_conjTranspose] using h

@[simp] theorem framePush_pull (g : Matˣ) (U : Mat) :
    (g : Mat) * framePullback g U * star (g : Mat) = U := by
  simp [framePullback, mul_assoc, ← star_mul]

/-- The invariant trace metric is semidefinite before removing radial tangents. -/
theorem tangentPair_self_nonneg (S U : Mat) (hS : S.PosDef) (hU : U.IsHermitian) :
    0 ≤ tangentPair S U U := by
  obtain ⟨g, rfl⟩ := exists_positive_frame S hS
  have h := tangentPair_frame g (framePullback g U) (framePullback g U)
  rw [framePush_pull] at h
  rw [h]
  exact tracePair_self_nonneg _ (framePullback_isHermitian g U hU)

/-- The null directions at a positive form are exactly its scalar multiples. -/
theorem tangentPair_self_eq_zero (S U : Mat) (hS : S.PosDef) (hU : U.IsHermitian) :
    tangentPair S U U = 0 ↔ ∃ c : ℝ, U = c • S := by
  obtain ⟨g, rfl⟩ := exists_positive_frame S hS
  have h := tangentPair_frame g (framePullback g U) (framePullback g U)
  rw [framePush_pull] at h
  rw [h, tracePair_self_eq_zero _ (framePullback_isHermitian g U hU)]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← framePush_pull g U, hc]
    simp
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    simp [framePullback, ← star_mul]

/-- On trace-zero tangents to the trace-one model the metric is strictly positive. -/
theorem tangentPair_self_pos (S U : Mat) (hS : S.PosDef) (htrace : S.trace = 1)
    (hU : U.IsHermitian) (hUtrace : U.trace = 0) (hne : U ≠ 0) :
    0 < tangentPair S U U := by
  apply lt_of_le_of_ne (tangentPair_self_nonneg S U hS hU)
  intro h
  obtain ⟨c, hc⟩ := (tangentPair_self_eq_zero S U hS hU).mp h.symm
  have ht := congrArg Matrix.trace hc
  simp only [trace_smul, htrace, hUtrace, smul_eq_mul, mul_one] at ht
  exact hne (by simpa [← ht] using hc)

end TernaryPoly.SymmetricSpaceTraceMetric
