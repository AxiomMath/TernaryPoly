module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricCoordinates
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricSmooth

@[expose] public section


namespace TernaryPoly.SymmetricSpaceTraceMetric

open Matrix SymmetricSpaceCharts
open scoped ContDiff Matrix.Norms.Elementwise

theorem contDiff_tangentMatrix : ContDiff ℝ ∞ tangentMatrix := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact contDiff_apply ℝ ℝ 0
  · exact contDiff_apply ℝ ℝ 1
  · exact contDiff_apply ℝ ℝ 2
  · exact contDiff_apply ℝ ℝ 1
  · exact contDiff_apply ℝ ℝ 3
  · exact contDiff_apply ℝ ℝ 4
  · exact contDiff_apply ℝ ℝ 2
  · exact contDiff_apply ℝ ℝ 4
  · exact (contDiff_apply ℝ ℝ 0).neg.sub (contDiff_apply ℝ ℝ 3)

/-- Smoothness holds jointly in the base point and both tangent vectors, on the
literal open coordinate domain used by the arithmetic quotient atlas. -/
theorem contDiffOn_coordinatePair :
    ContDiffOn ℝ ∞ (fun p : Coordinates × Coordinates × Coordinates =>
      coordinatePair p.1 p.2.1 p.2.2) {p | p.1 ∈ positiveCoordinates} := by
  apply contDiffOn_tangentPair
  · exact (contDiff_reconstruct.comp contDiff_fst).contDiffOn
  · exact (contDiff_tangentMatrix.comp (contDiff_fst.comp contDiff_snd)).contDiffOn
  · exact (contDiff_tangentMatrix.comp (contDiff_snd.comp contDiff_snd)).contDiffOn
  · intro p hp
    exact hp.isUnit

end TernaryPoly.SymmetricSpaceTraceMetric
