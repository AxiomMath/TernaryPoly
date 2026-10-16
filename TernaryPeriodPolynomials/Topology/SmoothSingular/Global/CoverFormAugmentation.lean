module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.ClosedForms
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FormAugmentation
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.CoveringChart

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits Set HomologicalComplex
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts SymmetricSpacePositive

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {U : Set OrbitSpace} (hU : IsOpen U)

/-- The actual coefficient section maps to the closed zero-form on the actual open. -/
theorem coveringCoefficientForm_closed : ModuleCat.ofHom (coefficientFormMap ρ hU) ≫
    (coveringComplex ρ hU).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact coefficientForm_closed ρ hU f

/-- The literal coefficient augmentation into the actual smooth covering complex on an open. -/
def coveringFormAugmentation :
    (CochainComplex.single₀ (ModuleCat ℝ)).obj (ModuleCat.of ℝ (coefficientSections ρ U)) ⟶
      coveringComplex ρ hU :=
  SmoothSingularComparison.augmentation (ModuleCat.ofHom (coefficientFormMap ρ hU))
    (coveringCoefficientForm_closed ρ hU)

/-- Its actual degree-zero map is the original coefficient-to-form map. -/
theorem coveringFormAugmentation_zero : (coveringFormAugmentation ρ hU).f 0 =
    ModuleCat.ofHom (coefficientFormMap ρ hU) :=
  SmoothSingularComparison.augmentation_f_zero _ _

/-- Positive exactness, once actually established on the open, suffices because the genuine
coefficient augmentation identifies all closed zero-forms on every quotient open. -/
theorem coveringFormAugmentation_quasiIso_of_exact
    (hpos : ∀ n : ℕ, (coveringComplex ρ hU).ExactAt (n+1)) :
    QuasiIso (coveringFormAugmentation ρ hU) := by
  have : Mono (ModuleCat.ofHom (coefficientFormMap ρ hU)) :=
    (ModuleCat.mono_iff_injective _).mpr (coefficientForm_injective ρ hU)
  unfold coveringFormAugmentation
  refine @SmoothSingularComparison.augmentation_quasiIso ℝ _ (coveringComplex ρ hU)
    (ModuleCat.of ℝ (coefficientSections ρ U)) (ModuleCat.ofHom (coefficientFormMap ρ hU))
      (coveringCoefficientForm_closed ρ hU) ?_ this ?_
  · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    exact coefficientFormMap_range ρ hU
  · exact hpos

/-- On every actual convex selected chart domain, the genuine covering form complex is exact
in positive degree by the actual chart isomorphism and Poincaré lemma. -/
theorem coveringForm_exactAt_convex (S : Space) {V : Set Coordinates} (hV : IsOpen V)
    (hVt : V ⊆ (quotientChart S).target) (hc : Convex ℝ V) (n : ℕ) :
    (coveringComplex ρ (chartOpen_isOpen S hV)).ExactAt (n+1) :=
  (SmoothSingularComparison.deRham_exactAt (F := F) hV hc n).of_iso
    (SmoothSingularComparison.coveringChartComplexIso ρ S hV hVt).symm

/-- The actual coefficient augmentation resolves actual smooth forms on every convex selected
chart, including the empty chart. -/
theorem coveringFormAugmentation_quasiIso_convex (S : Space) {V : Set Coordinates}
    (hV : IsOpen V) (hVt : V ⊆ (quotientChart S).target) (hc : Convex ℝ V) :
    QuasiIso (coveringFormAugmentation ρ (chartOpen_isOpen S hV)) :=
  coveringFormAugmentation_quasiIso_of_exact ρ _ (coveringForm_exactAt_convex ρ S hV hVt hc)

end TernaryPoly.SmoothSingularGlobal
