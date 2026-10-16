module

public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.VolumeFinite
public import TernaryPeriodPolynomials.Analysis.ContinuousDensityOpenPositive

@[expose] public section


/-! The genuine quotient Riemannian volume detects every nonempty open set. -/
namespace TernaryPoly.SymmetricSpaceRiemannian

open MeasureTheory Set SymmetricSpacePositive SymmetricSpaceCharts
open SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped Topology

/-- The actual volume has full topological support. -/
scoped instance orbitVolume_openPositive : orbitVolume.IsOpenPosMeasure := by
  constructor
  intro U hU hne
  obtain ⟨q, hq⟩ := hne
  obtain ⟨S, hS⟩ := quotientCharts_cover q
  let e := quotientChart S
  let W := U ∩ e.source
  have hW : IsOpen W := hU.inter e.open_source
  have hsub : W ⊆ e.source := inter_subset_right
  have hx : e q ∈ positiveCoordinates := quotientChart_target_subset S (e.map_source hS)
  have hcont : ContinuousAt coordinateDensity (e q) :=
    (contDiffOn_coordinateDensity.continuousOn (e q) hx).continuousAt
      (isOpen_positiveCoordinates.mem_nhds hx)
  have hpos : 0 < coordinateVolume (e '' W) :=
    ContinuousDensityOpenPositive.withDensity_pos hcont (coordinateDensity_pos _ hx)
      ((e.isOpen_image_of_subset_source hW hsub).mem_nhds ⟨q, ⟨hq, hS⟩, rfl⟩)
  have heq : orbitVolume W = coordinateVolume (e '' W) := by
    rw [orbitVolume_chart_apply S hsub, coordinateVolume_apply]
  exact ne_of_gt ((heq.symm ▸ hpos).trans_le (measure_mono inter_subset_left))

/-- Almost-everywhere equality of continuous functions for the actual volume is pointwise equality. -/
theorem continuous_eq_of_ae_eq {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : OrbitSpace → Y} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[orbitVolume] g) : f = g := MeasureTheory.Measure.eq_of_ae_eq h hf hg

end TernaryPoly.SymmetricSpaceRiemannian
