module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory TopologicalSpace Set
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts SymmetricSpacePositive
open scoped Topology

/-- Actual continuous lifting-frame data, with the genuine locally constant deck label. -/
structure SingularFrame (G : Type) [Group G] (X Y : TopCat.{0}) [MulAction G X] where
  base : X ⟶ Y
  lift : Y ⟶ X
  label : LocallyConstant X G
  base_lift : ∀ y : Y, base (lift y) = y
  reconstruction : ∀ x : X, label x • lift (base x) = x
  label_lift : ∀ y : Y, label (lift y) = 1
  base_action : ∀ (g : G) (x : X), base (g • x) = base x
  label_action : ∀ (g : G) (x : X), label (g • x) = g * label x

/-- The actual coordinate projection of the lifted quotient chart onto its selected sheet. -/
def chartFrameBase (S : Space) (V : Set Coordinates) :
    TopCat.of (CoverOpen (chartOpen S V)) ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x => ⟨baseCoordinate S x.val, baseCoordinate_mem_chartOpen S x.property⟩,
    Continuous.subtype_mk
      ((baseCoordinate_smooth S).continuousOn.comp_continuous continuous_subtype_val
        (fun x => liftedDomain_mono (chartOpen_subset S V) x.property)) _⟩

/-- The selected-sheet inclusion is the actual coordinate inclusion into the covering preimage. -/
def chartFrameLift (S : Space) {V : Set Coordinates} (hVt : V ⊆ (quotientChart S).target) :
    TopCat.of V ⟶ TopCat.of (CoverOpen (chartOpen S V)) :=
  TopCat.ofHom ⟨fun x => ⟨x.val, SmoothSingularComparison.chartSubset_liftedDomain S hVt x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The frame's actual deck label is locally constant on the genuine lifted domain. -/
def chartFrameLabel (S : Space) (V : Set Coordinates) :
    LocallyConstant (CoverOpen (chartOpen S V)) DeckGroup :=
  ⟨fun x => sheetElement S x.val, by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    exact (sheetElement_eventually S (liftedDomain_mono (chartOpen_subset S V) x.property)).comp_tendsto
      continuous_subtype_val.continuousAt⟩

/-- Genuine covering charts provide the actual singular lifting-frame data. -/
def chartSingularFrame (S : Space) {V : Set Coordinates} (hVt : V ⊆ (quotientChart S).target) :
    SingularFrame DeckGroup (TopCat.of (CoverOpen (chartOpen S V))) (TopCat.of V) where
  base := chartFrameBase S V
  lift := chartFrameLift S hVt
  label := chartFrameLabel S V
  base_lift y := Subtype.ext (baseCoordinate_chart S (hVt y.property))
  reconstruction x := Subtype.ext (baseCoordinate_sheet S
    (liftedDomain_mono (chartOpen_subset S V) x.property))
  label_lift y := sheetElement_chart S (hVt y.property)
  base_action g x := Subtype.ext (baseCoordinate_deck S g x.property.1)
  label_action g x := sheetElement_deck S g
    (liftedDomain_mono (chartOpen_subset S V) x.property)

end TernaryPoly.SmoothSingularGlobal
