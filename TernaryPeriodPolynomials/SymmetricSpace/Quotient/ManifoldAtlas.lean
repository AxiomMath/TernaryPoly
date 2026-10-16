module

public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.Manifold
public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.ManifoldTransitions
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Notation

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceQuotientManifold
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open Topology Set
open scoped Manifold ContDiff

/-- The atlas consists of the actual evenly-covered lifting charts already constructed. -/
instance orbitChartedSpace : ChartedSpace Coordinates OrbitSpace where
  atlas := Set.range quotientChart
  chartAt x := quotientChart x.out
  mem_chart_source x := by
    have h := self_mem_quotientChart x.out
    simpa only [quotientProjection,Quotient.out_eq] using h
  chart_mem_atlas x := ⟨x.out,rfl⟩

@[simp] theorem orbit_chartAt (x : OrbitSpace) :
    chartAt Coordinates x=quotientChart x.out := rfl

theorem quotientChart_mem_atlas (S : Space) : quotientChart S∈atlas Coordinates OrbitSpace :=
  ⟨S,rfl⟩

/-- Smoothness of the actual deck-coordinate transitions gives a smooth arithmetic quotient. -/
instance orbitIsManifold : IsManifold 𝓘(ℝ,Coordinates) ∞ OrbitSpace := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨S,rfl⟩ := he
  obtain ⟨T,rfl⟩ := he'
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.id_comp,
    Function.comp_id,preimage_id_eq,range_id,inter_univ,id_eq] using
      quotientChart_transition_contDiffOn S T

/-- Openness of the quotient projection preserves second countability. -/
instance orbitSecondCountable : SecondCountableTopology OrbitSpace :=
  ContinuousConstSMul.secondCountableTopology

/-- A precise positive-Jacobian compatibility statement for every pair in the actual atlas. -/
theorem atlas_transition_det_pos (e e' : OpenPartialHomeomorph OrbitSpace Coordinates)
    (he : e∈atlas Coordinates OrbitSpace) (he' : e'∈atlas Coordinates OrbitSpace)
    (x : Coordinates) (hx : x∈(e.symm.trans e').source) :
    0 < LinearMap.det (fderiv ℝ (e.symm.trans e') x).toLinearMap := by
  obtain ⟨S,rfl⟩ := he
  obtain ⟨T,rfl⟩ := he'
  exact quotientChart_transition_det_pos S T x hx

/-- Every explicit quotient chart is a smooth chart in the actual quotient structure. -/
theorem quotientChart_contMDiffOn (S : Space) :
    ContMDiffOn 𝓘(ℝ,Coordinates) 𝓘(ℝ,Coordinates) ∞ (quotientChart S)
      (quotientChart S).source :=
  contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (quotientChart_mem_atlas S))

theorem quotientChart_symm_contMDiffOn (S : Space) :
    ContMDiffOn 𝓘(ℝ,Coordinates) 𝓘(ℝ,Coordinates) ∞ (quotientChart S).symm
      (quotientChart S).target :=
  contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (quotientChart_mem_atlas S))

end TernaryPoly.SymmetricSpaceQuotientManifold
