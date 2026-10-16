module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricQuotientInvariant
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

@[expose] public section


/-! Exact tangent-bundle transition coordinates for the actual quotient metric. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold Manifold Bundle
open scoped ContDiff Manifold Matrix.Norms.Elementwise

/-- The backward tangent trivialization is the derivative of the actual quotient-chart overlap. -/
theorem orbit_tangent_symmL (q b : OrbitSpace) (hb : b ∈ (chartAt Coordinates q).source) :
    (trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) q).symmL ℝ b =
      fderiv ℝ ((chartAt Coordinates q).symm.trans (chartAt Coordinates b))
        (chartAt Coordinates q b) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core hb]
  simp only [tangentBundleCore_coordChange_achart, extChartAt, OpenPartialHomeomorph.extend,
    modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  rfl

/-- Pairing after inverse tangent trivialization has the same coordinate expression. -/
theorem coordinatePair_orbit_symmL (q b : OrbitSpace)
    (hb : b ∈ (chartAt Coordinates q).source) (v w : Coordinates) :
    coordinatePair (chartAt Coordinates b b)
      ((trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) q).symmL ℝ b v)
      ((trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) q).symmL ℝ b w) =
      coordinatePair (chartAt Coordinates q b) v w := by
  rw [orbit_tangent_symmL q b hb]
  have hx : chartAt Coordinates q b ∈
      ((chartAt Coordinates q).symm.trans (chartAt Coordinates b)).source := by
    refine ⟨(chartAt Coordinates q).map_source hb, ?_⟩
    change (chartAt Coordinates q).symm (chartAt Coordinates q b) ∈ (chartAt Coordinates b).source
    rw [(chartAt Coordinates q).left_inv hb]
    exact mem_chart_source Coordinates b
  have h := coordinatePair_atlas_invariant (chartAt Coordinates q) (chartAt Coordinates b)
    (chart_mem_atlas Coordinates q) (chart_mem_atlas Coordinates b)
    (chartAt Coordinates q b) hx v w
  simp only [OpenPartialHomeomorph.trans_apply, (chartAt Coordinates q).left_inv hb] at h
  exact h

end TernaryPoly.SymmetricSpaceTraceMetric
