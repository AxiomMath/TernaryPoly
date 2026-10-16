module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.QuotientLocal
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.Pullback

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularComparison
open CategoryTheory Set HomologicalComplex SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (S : Space) {V W : Set Coordinates}

/-- Inclusion of coordinate domains gives the actual inclusion of their quotient opens. -/
theorem chartOpen_mono (hWV : W ⊆ V) : chartOpen S W ⊆ chartOpen S V :=
  fun _ hq => ⟨hq.1, hWV hq.2⟩

/-- The literal smaller covering-chart isomorphisms intertwine actual quotient restrictions. -/
theorem coveringChartComplexIso_restrict (hV : IsOpen V) (hW : IsOpen W)
    (hVt : V ⊆ (quotientChart S).target) (hWt : W ⊆ (quotientChart S).target) (hWV : W ⊆ V) :
    (coveringChartComplexIso ρ S hV hVt).hom ≫ deRhamRestriction hV hW hWV =
      restrictionChainMap ρ (chartOpen_isOpen S hV) (chartOpen_isOpen S hW) (chartOpen_mono S hWV) ≫
        (coveringChartComplexIso ρ S hW hWt).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  change EquivariantForm ρ (chartOpen S V) n at w
  apply Form.ext
  intro x hx
  change (restrictTo hWV n (coveringChartRestriction ρ S hVt n w) : RawForm Coordinates F n) x =
    (coveringChartRestriction ρ S hWt n (restrictEquivariant ρ (chartOpen_mono S hWV) n w) :
      RawForm Coordinates F n) x
  rw [restrictTo_apply hWV _ hx]
  change (restrictTo (chartSubset_liftedDomain S hVt) n w.val : RawForm Coordinates F n) x =
    (restrictTo (chartSubset_liftedDomain S hWt) n
      (restrictEquivariant ρ (chartOpen_mono S hWV) n w).val : RawForm Coordinates F n) x
  rw [restrictTo_apply _ _ (hWV hx), restrictTo_apply _ _ hx,
    restrictEquivariant_apply ρ _ w (chartSubset_liftedDomain S hWt hx)]

/-- The comparison on the actual local-coefficient covering complex commutes with actual
quotient restrictions and coordinate singular restrictions. -/
theorem coveringLocalComparison_restrict (hV : IsOpen V) (hW : IsOpen W)
    (hVt : V ⊆ (quotientChart S).target) (hWt : W ⊆ (quotientChart S).target)
    (hcV : Convex ℝ V) (hcW : Convex ℝ W) (hnV : V.Nonempty) (hnW : W.Nonempty)
    (hWV : W ⊆ V) (n : ℕ) :
    (coveringLocalComparison ρ S hV hVt hcV hnV n).hom ≫
        homologyMap (singularPullback (chartInclusion hWV) (ModuleCat.of ℝ F)) n =
      homologyMap (restrictionChainMap ρ (chartOpen_isOpen S hV) (chartOpen_isOpen S hW)
        (chartOpen_mono S hWV)) n ≫
        (coveringLocalComparison ρ S hW hWt hcW hnW n).hom := by
  change (homologyMap (coveringChartComplexIso ρ S hV hVt).hom n ≫
      (localComparison hV hcV hnV n).hom) ≫ _ = _ ≫
    (homologyMap (coveringChartComplexIso ρ S hW hWt).hom n ≫
      (localComparison hW hcW hnW n).hom)
  rw [Category.assoc, localComparison_restrict hV hW hcV hcW hnV hnW hWV n,
    ← Category.assoc, ← homologyMap_comp, coveringChartComplexIso_restrict ρ S hV hW hVt hWt hWV,
    homologyMap_comp, Category.assoc]

end TernaryPoly.SmoothSingularComparison
