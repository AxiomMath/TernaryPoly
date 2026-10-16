module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricSpaceBundle
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricOrbitSmooth

@[expose] public section


/-! The actual covering projection preserves the two smooth tangent metrics. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold Manifold Bundle
open scoped ContDiff Manifold Matrix.Norms.Elementwise Topology

/-- The inverse lifting chart is literally projection after inverse global coordinates. -/
theorem quotientChart_symm_projection_coordinates (S : Space) (x : Coordinates) :
    (quotientChart S).symm x = quotientProjection (coordinateChart.symm x) := by
  change (localLift S).symm (coordinateChart.symm x) = _
  rw [localLift_symm]

theorem projection_coordinate_mem_overlap (S : Space) :
    coordinateChart S ∈ ((quotientChart S).symm.trans
      (chartAt Coordinates (quotientProjection S))).source := by
  rw [coordinateChart_apply, ← quotientChart_self S]
  refine ⟨(quotientChart S).map_source (self_mem_quotientChart S), ?_⟩
  change (quotientChart S).symm (quotientChart S (quotientProjection S)) ∈
    (chartAt Coordinates (quotientProjection S)).source
  rw [(quotientChart S).left_inv (self_mem_quotientChart S)]
  exact mem_chart_source Coordinates _

/-- Its manifold derivative is the actual overlap derivative into the preferred quotient chart. -/
theorem mfderiv_quotientProjection (S : Space) :
    mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) quotientProjection S =
      fderiv ℝ ((quotientChart S).symm.trans (chartAt Coordinates (quotientProjection S)))
        (coordinateChart S) := by
  have h : HasMFDerivAt 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) quotientProjection S
      (fderiv ℝ ((quotientChart S).symm.trans (chartAt Coordinates (quotientProjection S)))
        (coordinateChart S)) := by
    refine ⟨quotientProjection_contMDiff.continuous.continuousAt, ?_⟩
    simp only [modelWithCornersSelf_coe, Set.range_id]
    change HasFDerivWithinAt
      (chartAt Coordinates (quotientProjection S) ∘ quotientProjection ∘ coordinateChart.symm)
      _ Set.univ (coordinateChart S)
    have he : (chartAt Coordinates (quotientProjection S) ∘ quotientProjection ∘ coordinateChart.symm) =
        ((quotientChart S).symm.trans (chartAt Coordinates (quotientProjection S))) := by
      funext x
      simp only [Function.comp_apply, OpenPartialHomeomorph.trans_apply,
        quotientChart_symm_projection_coordinates]
    rw [he]
    exact (((quotientChart_transition_contDiffOn S (quotientProjection S).out).contDiffAt
      (((quotientChart S).symm.trans (quotientChart (quotientProjection S).out)).open_source.mem_nhds
        (projection_coordinate_mem_overlap S))).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  exact h.mfderiv

/-- The literal projection is a local Riemannian isometry at the level of tangent metrics. -/
theorem orbitInner_mfderiv_quotientProjection (S : Space)
    (v w : TangentSpace 𝓘(ℝ, Coordinates) S) :
    orbitInner (quotientProjection S)
      (mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) quotientProjection S v)
      (mfderiv 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates) quotientProjection S w) = spaceInner S v w := by
  have h := coordinatePair_quotientChart_invariant S (quotientProjection S).out
    (coordinateChart S) (projection_coordinate_mem_overlap S) v w
  have hp : (quotientChart S).symm (coordinateChart S) = quotientProjection S := by
    rw [coordinateChart_apply, ← quotientChart_self S, (quotientChart S).left_inv (self_mem_quotientChart S)]
  simp only [OpenPartialHomeomorph.trans_apply, hp] at h
  simp only [orbitInner_apply, spaceInner_apply, mfderiv_quotientProjection]
  exact h

end TernaryPoly.SymmetricSpaceTraceMetric
