module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.Poincare

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothCoveringDeRham
open Set Filter ContinuousAlternatingMap SmoothLocalDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {n : ℕ}

/-- The ordinary chart representative of an actual global local-coefficient form. -/
def globalChartRepresentative (S : Space) (n : ℕ) : EquivariantForm ρ univ n →ₗ[ℝ]
    Form (F := F) (quotientChart S).target n :=
  (chartRestrict ρ S n).comp (restrictEquivariant ρ (subset_univ _) n)

@[simp] theorem globalChartRepresentative_apply (S : Space) (w : EquivariantForm ρ univ n)
    {x : Coordinates} (hx : x ∈ (quotientChart S).target) :
    (globalChartRepresentative ρ S n w : RawForm Coordinates F n) x =
      (w.val : RawForm Coordinates F n) x := by
  rw [globalChartRepresentative, LinearMap.comp_apply, chartRestrict_apply ρ S _ hx,
    restrictEquivariant_apply ρ _ w (quotientChart_target_liftedDomain S hx)]

/-- Actual local-system transition law: on every genuine chart overlap, the true coordinate
pullback equals the coefficient action of the locally constant arithmetic deck transition. -/
theorem globalChartRepresentative_transition (S T : Space) (x : Coordinates)
    (hx : x ∈ ((quotientChart S).symm.trans (quotientChart T)).source) :
    ∃ g : DeckGroup,
      ((quotientChart S).symm.trans (quotientChart T)) =ᶠ[𝓝 x] deckMap g ∧
      ∀ (n : ℕ) (w : EquivariantForm ρ univ n),
        pullRaw ((quotientChart S).symm.trans (quotientChart T))
          (globalChartRepresentative ρ T n w : RawForm Coordinates F n) x =
        coefficientFormMap (coefficientMap ρ g) n
          ((globalChartRepresentative ρ S n w : RawForm Coordinates F n) x) := by
  obtain ⟨g, hg⟩ := quotientChart_transition_eventually S T x hx
  change ((quotientChart S).symm.trans (quotientChart T)) =ᶠ[𝓝 x] deckMap g at hg
  refine ⟨g, hg, fun n w => ?_⟩
  have ht : deckMap g x ∈ (quotientChart T).target := by
    rw [← hg.self_of_nhds]
    exact (quotientChart T).map_source hx.2
  rw [pullRaw_eventuallyEq _ hg, globalChartRepresentative_apply ρ S w hx.1]
  change ((globalChartRepresentative ρ T n w : RawForm Coordinates F n) (deckMap g x)).compContinuousLinearMap _ = _
  rw [globalChartRepresentative_apply ρ T w ht]
  exact w.property g x ⟨quotientChart_target_subset S hx.1, mem_univ _⟩

end TernaryPoly.SmoothCoveringDeRham
