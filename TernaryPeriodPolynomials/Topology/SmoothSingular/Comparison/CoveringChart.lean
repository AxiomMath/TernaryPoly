module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.Local
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Gluing

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularComparison
open CategoryTheory Set SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped Topology
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (S : Space) {V : Set Coordinates}

/-- The distinguished lifting-sheet coordinates over an actual smaller quotient chart. -/
theorem chartSubset_liftedDomain (hVt : V ⊆ (quotientChart S).target) :
    V ⊆ liftedDomain (chartOpen S V) := by
  intro x hx
  refine ⟨quotientChart_target_subset S (hVt hx), ?_⟩
  change coordinateProjection x ∈ chartOpen S V
  rw [← quotientChart_projection_coordinates S (hVt hx)]
  exact ⟨(quotientChart S).map_target (hVt hx), by
    change quotientChart S ((quotientChart S).symm x) ∈ V
    simpa only [(quotientChart S).right_inv (hVt hx)] using hx⟩

/-- Actual restriction from equivariant forms to a chosen smaller lifting sheet. -/
def coveringChartRestriction (hVt : V ⊆ (quotientChart S).target) (n : ℕ) :
    EquivariantForm ρ (chartOpen S V) n →ₗ[ℝ] Form (F := F) V n :=
  (restrictTo (chartSubset_liftedDomain S hVt) n).comp (equivariantSubmodule ρ _ n).subtype

/-- Extending from a smaller genuine lifting sheet and restricting returns the same form. -/
theorem coveringChartRestriction_extend (hV : IsOpen V) (hVt : V ⊆ (quotientChart S).target)
    (n : ℕ) (w : Form (F := F) V n) :
    coveringChartRestriction ρ S hVt n (chartExtendOn ρ S hV n w) = w := by
  apply Form.ext
  intro x hx
  change (restrictTo (chartSubset_liftedDomain S hVt) n (chartExtendOn ρ S hV n w).val :
    RawForm Coordinates F n) x = (w : RawForm Coordinates F n) x
  rw [restrictTo_apply _ _ hx, chartExtendOn_apply ρ S hV _ (chartSubset_liftedDomain S hVt hx)]
  have he : baseCoordinate S =ᶠ[𝓝 x] id := by
    filter_upwards [(quotientChart S).open_target.mem_nhds (hVt hx)] with y hy
    exact baseCoordinate_chart S hy
  rw [extendRaw, sheetElement_chart S (hVt hx), coefficientFormMap_one,
    pullRaw_eventuallyEq _ he, pullRaw_id]

/-- Actual equivariant reconstruction on a smaller quotient chart. -/
theorem coveringChartExtend_restrict (hV : IsOpen V) (hVt : V ⊆ (quotientChart S).target)
    (n : ℕ) (w : EquivariantForm ρ (chartOpen S V) n) :
    chartExtendOn ρ S hV n (coveringChartRestriction ρ S hVt n w) = w := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  rw [chartExtendOn_apply ρ S hV _ hx]
  have hb := baseCoordinate_mem_chartOpen S hx
  have he := extendRaw_reconstruction ρ S w hx (liftedDomain_mono (chartOpen_subset S V) hx)
  rw [← he]
  unfold extendRaw pullRaw
  congr 1
  congr 1
  exact congrArg (fun z : RawForm Coordinates F n => z (baseCoordinate S x))
    (show (coveringChartRestriction ρ S hVt n w : RawForm Coordinates F n) =
      (restrictTo (chartSubset_liftedDomain S hVt) n w.val : RawForm Coordinates F n) from rfl)
    |>.trans (restrictTo_apply _ _ hb)

/-- Restriction to the smaller lifting sheet intertwines the actual exterior differential. -/
theorem coveringChartRestriction_d (hV : IsOpen V) (hVt : V ⊆ (quotientChart S).target)
    (n : ℕ) (w : EquivariantForm ρ (chartOpen S V) n) :
    coveringChartRestriction ρ S hVt (n+1) (differential ρ (chartOpen_isOpen S hV) n w) =
      d hV n (coveringChartRestriction ρ S hVt n w) :=
  restrictTo_d (liftedDomain_isOpen (chartOpen_isOpen S hV)) hV
    (chartSubset_liftedDomain S hVt) w.val

/-- The actual smaller covering chart has a genuine isomorphism to the ordinary chart complex. -/
def coveringChartComplexIso (hV : IsOpen V) (hVt : V ⊆ (quotientChart S).target) :
    coveringComplex ρ (chartOpen_isOpen S hV) ≅ complex (F := F) hV :=
  HomologicalComplex.Hom.isoOfComponents (fun n =>
    (LinearEquiv.ofLinearMap (coveringChartRestriction ρ S hVt n) (chartExtendOn ρ S hV n)
      (LinearMap.ext (coveringChartRestriction_extend ρ S hV hVt n))
      (LinearMap.ext (coveringChartExtend_restrict ρ S hV hVt n))).toModuleIso)
    (fun i j hij => by
      obtain rfl : j = i+1 := hij.symm
      simp only [coveringComplex, complex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      exact LinearMap.ext (fun w => (coveringChartRestriction_d ρ S hV hVt i w).symm))

/-- Genuine local covering de Rham cohomology is identified with real singular cohomology
in the chosen trivializing coordinates, with arbitrary finite-dimensional real deck coefficients. -/
def coveringLocalComparison (hV : IsOpen V) (hVt : V ⊆ (quotientChart S).target)
    (hc : Convex ℝ V) (hne : V.Nonempty) (n : ℕ) :
    (coveringComplex ρ (chartOpen_isOpen S hV)).homology n ≅
      (realSingularCochains (TopCat.of V) (ModuleCat.of ℝ F)).homology n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) n).mapIso
    (coveringChartComplexIso ρ S hV hVt) ≪≫ localComparison hV hc hne n

end TernaryPoly.SmoothSingularComparison
