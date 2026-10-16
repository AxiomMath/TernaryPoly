module

public import TernaryPeriodPolynomials.SymmetricSpace.Riemannian.CoordinateVolume
public import TernaryPeriodPolynomials.Analysis.ChartLocalMeasure
public import TernaryPeriodPolynomials.Analysis.CompatibleMeasureGluingExtension
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section


/-! The actual Riemannian volume measure on the arithmetic quotient. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian

open MeasureTheory Set SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceQuotientManifold

/-- The quotient's original topology supplies its Borel sigma-algebra. -/
scoped instance orbitMeasurableSpace : MeasurableSpace OrbitSpace := borel OrbitSpace
scoped instance orbitBorelSpace : BorelSpace OrbitSpace := ⟨rfl⟩

/-- The actual chart-local volume, extended by zero outside its source. -/
def chartVolume (S : Space) : Measure OrbitSpace :=
  ChartLocalMeasure.localMeasure (quotientChart S) coordinateVolume

/-- The coordinate Jacobian theorem makes actual local volumes compatible. -/
theorem chartVolume_compatible (S T : Space) :
    (chartVolume S).restrict (quotientChart T).source =
      (chartVolume T).restrict (quotientChart S).source :=
  ChartLocalMeasure.localMeasure_compatible _ _ _ (fun _ hs hsub =>
    coordinateVolume_quotientChart_image S T hs hsub)

theorem exists_countable_volume_atlas :
    ∃ c : ℕ → Space, (⋃ n, (quotientChart (c n)).source) = univ := by
  obtain ⟨c, hc⟩ := isLindelof_univ.indexed_countable_subcover
    (fun S : Space => (quotientChart S).source) (fun S => (quotientChart S).open_source)
    (show (univ : Set OrbitSpace) ⊆ ⋃ S, (quotientChart S).source from by
      intro x _
      obtain ⟨S, hS⟩ := quotientCharts_cover x
      exact mem_iUnion.mpr ⟨S, hS⟩)
  exact ⟨c, eq_univ_iff_forall.mpr (fun x => hc (mem_univ x))⟩

/-- A fixed countable subatlas, used only to construct the measure. -/
def volumeAtlas : ℕ → Space := exists_countable_volume_atlas.choose

theorem volumeAtlas_cover : (⋃ n, (quotientChart (volumeAtlas n)).source) = univ :=
  exists_countable_volume_atlas.choose_spec

/-- The genuine Riemannian volume is the unique measure with all the prescribed chart densities. -/
def orbitVolume : Measure OrbitSpace :=
  CompatibleMeasureGluing.glued (fun n => (quotientChart (volumeAtlas n)).source)
    (fun n => chartVolume (volumeAtlas n))

/-- Every actual chart has the exact Riemannian density; no chart-selection dependence remains. -/
theorem orbitVolume_restrict_chart (S : Space) :
    orbitVolume.restrict (quotientChart S).source = chartVolume S :=
  CompatibleMeasureGluing.glued_restrict_other _
    (fun n => (quotientChart (volumeAtlas n)).open_source.measurableSet) volumeAtlas_cover _
    (fun i j => chartVolume_compatible (volumeAtlas i) (volumeAtlas j)) _ _
    (fun i => chartVolume_compatible (volumeAtlas i) S)

/-- Exact integration density on every subset lying inside a chart. -/
theorem orbitVolume_chart_apply (S : Space) {s : Set OrbitSpace}
    (hsub : s ⊆ (quotientChart S).source) :
    orbitVolume s = ∫⁻ x in (quotientChart S) '' s, ENNReal.ofReal (coordinateDensity x) := by
  rw [← Measure.restrict_eq_self orbitVolume hsub, orbitVolume_restrict_chart,
    chartVolume, ChartLocalMeasure.localMeasure_apply, inter_eq_left.mpr hsub,
    coordinateVolume_apply]

end TernaryPoly.SymmetricSpaceRiemannian
