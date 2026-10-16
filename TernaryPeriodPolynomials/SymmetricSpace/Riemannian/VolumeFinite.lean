module

public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.Volume
public import TernaryPeriodPolynomials.Analysis.ContinuousDensityLocallyFinite

@[expose] public section


/-! The actual Riemannian volume is locally finite in the original quotient topology. -/
namespace TernaryPoly.SymmetricSpaceRiemannian

open MeasureTheory Set Filter SymmetricSpacePositive SymmetricSpaceCharts
open SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped Topology

/-- The coordinate density is finite near every genuine positive coordinate. -/
theorem coordinateVolume_finiteAt {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    coordinateVolume.FiniteAtFilter (𝓝 x) :=
  ContinuousDensityLocallyFinite.finiteAt_withDensity
    ((contDiffOn_coordinateDensity.continuousOn x hx).continuousAt
      (isOpen_positiveCoordinates.mem_nhds hx))

/-- Every quotient point has a neighborhood of finite genuine Riemannian volume. -/
scoped instance orbitVolume_locallyFinite : IsLocallyFiniteMeasure orbitVolume := by
  constructor
  intro q
  obtain ⟨S, hS⟩ := quotientCharts_cover q
  let e := quotientChart S
  obtain ⟨A, hA, hfin⟩ := coordinateVolume_finiteAt
    (quotientChart_target_subset S (e.map_source hS))
  let U := e.source ∩ e ⁻¹' A
  have hU : U ∈ 𝓝 q := inter_mem (e.open_source.mem_nhds hS)
    ((e.continuousOn q hS).continuousAt (e.open_source.mem_nhds hS) hA)
  refine ⟨U, hU, ?_⟩
  have hsub : U ⊆ e.source := inter_subset_left
  have hv : orbitVolume U = coordinateVolume (e '' U) := by
    rw [orbitVolume_chart_apply S hsub, coordinateVolume_apply]
  rw [hv]
  apply lt_of_le_of_lt (measure_mono (show e '' U ⊆ A from ?_)) hfin
  rintro _ ⟨x, hx, rfl⟩
  exact hx.2

/-- Compact sets have finite Riemannian volume. -/
theorem orbitVolume_compact_lt_top (K : Set OrbitSpace) (hK : IsCompact K) :
    orbitVolume K < ⊤ := hK.measure_lt_top

/-- The measure used for L2 is sigma-finite on the actual second-countable quotient. -/
scoped instance orbitVolume_sigmaFinite : SigmaFinite orbitVolume := inferInstance

end TernaryPoly.SymmetricSpaceRiemannian
