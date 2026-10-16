module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricCongruence

@[expose] public section

namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix

theorem tracePair_add_left (A B C : Mat) : tracePair (A + B) C = tracePair A C + tracePair B C := by
  simp [tracePair, add_mul]

theorem tracePair_smul_left (c : ℝ) (A B : Mat) : tracePair (c • A) B = c * tracePair A B := by
  simp [tracePair]

theorem tracePair_add_right (A B C : Mat) : tracePair A (B + C) = tracePair A B + tracePair A C := by
  simp [tracePair, mul_add]

theorem tracePair_smul_right (c : ℝ) (A B : Mat) : tracePair A (c • B) = c * tracePair A B := by
  simp [tracePair]

theorem tangentPair_add_left (S U V W : Mat) :
    tangentPair S (U + V) W = tangentPair S U W + tangentPair S V W := by
  simp only [tangentPair, mul_add, tracePair_add_left]

theorem tangentPair_smul_left (c : ℝ) (S U V : Mat) :
    tangentPair S (c • U) V = c * tangentPair S U V := by
  simp [tangentPair, tracePair_smul_left]

theorem tangentPair_add_right (S U V W : Mat) :
    tangentPair S U (V + W) = tangentPair S U V + tangentPair S U W := by
  simp only [tangentPair, mul_add, tracePair_add_right]

theorem tangentPair_smul_right (c : ℝ) (S U V : Mat) :
    tangentPair S U (c • V) = c * tangentPair S U V := by
  simp [tangentPair, tracePair_smul_right]

theorem tangentPair_comm (S U V : Mat) : tangentPair S U V = tangentPair S V U :=
  tracePair_comm _ _

end TernaryPoly.SymmetricSpaceTraceMetric
