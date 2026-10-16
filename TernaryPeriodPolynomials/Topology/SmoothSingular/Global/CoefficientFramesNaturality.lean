module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FrameCoefficients

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory TopologicalSpace Set Filter
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts SymmetricSpacePositive
  SymmetricSpaceQuotientManifold
open scoped Topology
variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- The actual local coefficient frame identifications commute with all coordinate restrictions. -/
theorem chartCoefficientEquiv_restrict (S : Space) {V W : Set Coordinates}
    (hVt : V ⊆ (quotientChart S).target) (hWt : W ⊆ (quotientChart S).target) (hWV : W ⊆ V)
    (f : coefficientSections ρ (chartOpen S V)) :
    chartCoefficientEquiv ρ S hWt
      (coefficientRestriction ρ (SmoothSingularComparison.chartOpen_mono S hWV) f) =
      LocallyConstant.comap (SmoothSingularComparison.chartInclusion hWV).hom
        (chartCoefficientEquiv ρ S hVt f) := rfl

/-- The genuine local coefficient representative on the coordinate domain of any quotient open. -/
def localCoefficientRepresentative (S : Space) {U : Set OrbitSpace} :
    coefficientSections ρ U →ₗ[ℝ] LocallyConstant (chartDomain S U) F where
  toFun f := LocallyConstant.comap
    ⟨fun x => ⟨x.val, chartDomain_liftedDomain S x.property⟩,
      continuous_subtype_val.subtype_mk _⟩ f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual transition between covering frames acts on coefficients by the same real
representation ρ(g) as on the covering sections, using the genuine locally constant deck transition. -/
theorem localCoefficientRepresentative_transition {U : Set OrbitSpace} (S T : Space)
    (x : Coordinates) (hx : x ∈ ((quotientChart S).symm.trans (quotientChart T)).source)
    (hxU : (quotientChart S).symm x ∈ U) :
    ∃ g : DeckGroup,
      ((quotientChart S).symm.trans (quotientChart T)) =ᶠ[𝓝 x] deckMap g ∧
      ∃ (hy : deckMap g x ∈ chartDomain T U),
        ∀ f : coefficientSections ρ U,
          localCoefficientRepresentative ρ T f ⟨deckMap g x, hy⟩ =
            ρ g (localCoefficientRepresentative ρ S f ⟨x, hx.1, hxU⟩) := by
  obtain ⟨g, hg⟩ := quotientChart_transition_eventually S T x hx
  change ((quotientChart S).symm.trans (quotientChart T)) =ᶠ[𝓝 x] deckMap g at hg
  have hy : deckMap g x ∈ chartDomain T U := by
    rw [← hg.self_of_nhds]
    refine ⟨(quotientChart T).map_source hx.2, ?_⟩
    change (quotientChart T).symm (quotientChart T ((quotientChart S).symm x)) ∈ U
    have hxt : (quotientChart S).symm x ∈ (quotientChart T).source := hx.2
    rw [(quotientChart T).left_inv hxt]
    exact hxU
  exact ⟨g, hg, hy, fun f => f.property g ⟨x, chartDomain_liftedDomain S ⟨hx.1, hxU⟩⟩⟩

end TernaryPoly.SmoothSingularGlobal
