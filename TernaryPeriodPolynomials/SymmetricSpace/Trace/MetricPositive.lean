module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricAlgebra
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Topology.WithTopology

@[expose] public section


/-! Positivity of the projective trace pairing in a symmetric frame. -/
namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix

@[simp] theorem center_transpose (A : Mat) : center A.transpose = (center A).transpose := by
  simp [center]

theorem center_isHermitian (A : Mat) (hA : A.IsHermitian) : (center A).IsHermitian :=
  hA.sub (IsHermitian.smul (isHermitian_one : (1 : Mat).IsHermitian) (by simp [IsSelfAdjoint]))

/-- The trace pairing is positive semidefinite on real symmetric matrices. -/
theorem tracePair_self_nonneg (A : Mat) (hA : A.IsHermitian) : 0 ≤ tracePair A A := by
  have h := (posSemidef_conjTranspose_mul_self (center A)).trace_nonneg
  rw [(center_isHermitian A hA).eq] at h
  exact h

/-- Its only null directions are scalar matrices. -/
theorem tracePair_self_eq_zero (A : Mat) (hA : A.IsHermitian) :
    tracePair A A = 0 ↔ ∃ c : ℝ, A = c • 1 := by
  change (center A * center A).trace = 0 ↔ _
  have h : (center A * center A).trace = 0 ↔ center A = 0 := by
    simpa only [(center_isHermitian A hA).eq] using
      (trace_conjTranspose_mul_self_eq_zero_iff (A := center A))
  exact h.trans (center_eq_zero A)

/-- Removing the scalar direction makes the form strictly positive. -/
theorem tracePair_self_pos (A : Mat) (hA : A.IsHermitian)
    (hscalar : ¬ ∃ c : ℝ, A = c • 1) : 0 < tracePair A A := by
  exact lt_of_le_of_ne (tracePair_self_nonneg A hA)
    (Ne.symm fun h => hscalar ((tracePair_self_eq_zero A hA).mp h))

end TernaryPoly.SymmetricSpaceTraceMetric
