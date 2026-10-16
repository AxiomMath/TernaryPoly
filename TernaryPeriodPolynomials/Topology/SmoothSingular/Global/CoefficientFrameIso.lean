module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CoefficientFramesNaturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Opposite TopologicalSpace Set
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts SymmetricSpacePositive

/-- The genuine coordinate-open site of a selected quotient covering chart. -/
abbrev ChartOpenIndex (S : Space) :=
  Set.Iic (⟨(quotientChart S).target, (quotientChart S).open_target⟩ : Opens Coordinates)

variable {F : Type} [AddCommGroup F] [Module ℝ F] (ρ : Representation ℝ DeckGroup F)

/-- Restrict the actual coefficient sheaf to the true quotient opens of one covering chart. -/
def coefficientChartPresheaf (S : Space) : (ChartOpenIndex S)ᵒᵖ ⥤ ModuleCat ℝ where
  obj U := ModuleCat.of ℝ (coefficientSections ρ (chartOpen S (U.unop.val : Set Coordinates)))
  map f := ModuleCat.ofHom (coefficientRestriction ρ
    (SmoothSingularComparison.chartOpen_mono S f.unop.le))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual locally constant function presheaf on all open subsets of the covering chart target. -/
def locallyConstantChartPresheaf (S : Space) : (ChartOpenIndex S)ᵒᵖ ⥤ ModuleCat ℝ where
  obj U := ModuleCat.of ℝ (LocallyConstant (U.unop.val : Set Coordinates) F)
  map f := ModuleCat.ofHom
    { toFun c := LocallyConstant.comap (SmoothSingularComparison.chartInclusion f.unop.le).hom c
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual coefficient sheaf restricts to the locally constant function sheaf in each
true covering frame, as an explicit natural isomorphism on every coordinate open. -/
def coefficientChartIso (S : Space) :
    coefficientChartPresheaf ρ S ≅ locallyConstantChartPresheaf (F := F) S :=
  NatIso.ofComponents (fun U => (chartCoefficientEquiv ρ S U.unop.property).toModuleIso) (by
    intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact chartCoefficientEquiv_restrict ρ S U.unop.property V.unop.property f.unop.le c)

end TernaryPoly.SmoothSingularGlobal
