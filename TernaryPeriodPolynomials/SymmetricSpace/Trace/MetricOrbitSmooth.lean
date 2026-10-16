module

public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricOrbitBundle
public import TernaryPeriodPolynomials.SymmetricSpace.Trace.MetricTangentCoordinates
public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.ManifoldProjection

@[expose] public section


/-! Smoothness of the actual quotient tangent metric, by exact atlas invariance. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceTraceMetric

open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold Manifold Bundle ContinuousLinearMap
open scoped ContDiff Manifold Matrix.Norms.Elementwise Topology

/-- The metric section, in any preferred tangent trivialization, is the same coordinate metric. -/
theorem orbitInner_inCoordinates (q b : OrbitSpace)
    (hb : b ∈ (chartAt Coordinates q).source) :
    inCoordinates Coordinates (TangentSpace 𝓘(ℝ, Coordinates) : OrbitSpace → Type)
      (Coordinates →L[ℝ] ℝ) (fun b : OrbitSpace => TangentSpace 𝓘(ℝ, Coordinates) b →L[ℝ] ℝ)
      q b q b (orbitInner b) = coordinateContinuousBilin (chartAt Coordinates q b) := by
  have hb' : b ∈ (trivializationAt Coordinates
      (TangentSpace 𝓘(ℝ, Coordinates) : OrbitSpace → Type) q).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hb
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  rw [inCoordinates_apply_eq₂ hb' hb' (by simp)]
  rw [← (trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) q).symmL_apply (R := ℝ) hb' v,
    ← (trivializationAt Coordinates (TangentSpace 𝓘(ℝ, Coordinates)) q).symmL_apply (R := ℝ) hb' w]
  simpa [orbitInner_apply, coordinateContinuousBilin_apply] using
    coordinatePair_orbit_symmL q b hb v w

/-- The local matrix of the metric is smooth on the actual quotient chart. -/
theorem contMDiffOn_coordinateBilin_quotientChart (S : Space) :
    ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ) ∞
      (fun q : OrbitSpace => coordinateContinuousBilin (quotientChart S q))
      (quotientChart S).source := by
  exact contDiffOn_coordinateContinuousBilin.contMDiffOn.comp (quotientChart_contMDiffOn S)
    (fun q hq => quotientChart_target_subset S ((quotientChart S).map_source hq))

/-- The genuine quotient metric is a smooth section of the bilinear hom bundle. -/
theorem contMDiff_orbitInner :
    ContMDiff 𝓘(ℝ, Coordinates)
      (𝓘(ℝ, Coordinates).prod 𝓘(ℝ, Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ)) ∞
      (fun q : OrbitSpace => TotalSpace.mk' (Coordinates →L[ℝ] Coordinates →L[ℝ] ℝ) q
        (orbitInner q)) := by
  intro q
  rw [contMDiffAt_section]
  simp only [hom_trivializationAt_apply]
  have h := (contMDiffOn_coordinateBilin_quotientChart q.out).contMDiffAt
    ((chartAt Coordinates q).open_source.mem_nhds (mem_chart_source Coordinates q))
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt Coordinates q).open_source.mem_nhds
    (mem_chart_source Coordinates q)] with b hb
  exact orbitInner_inCoordinates q b hb

/-- The smooth Riemannian metric on the actual principal-six arithmetic quotient. -/
def orbitContMDiffRiemannianMetric :
    ContMDiffRiemannianMetric 𝓘(ℝ, Coordinates) ∞ Coordinates
      (TangentSpace 𝓘(ℝ, Coordinates) : OrbitSpace → Type) where
  inner := orbitInner
  symm := orbitRiemannianMetric.symm
  pos := orbitRiemannianMetric.pos
  isVonNBounded := orbitRiemannianMetric.isVonNBounded
  contMDiff := contMDiff_orbitInner

end TernaryPoly.SymmetricSpaceTraceMetric
