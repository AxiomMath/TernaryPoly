module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.ExtensionBetween

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalOpenUnion
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport EquivariantSingularSmall

/-- Every compact subset lies in one member of an increasing open cover. -/
theorem compact_subset_stage {B : Type} [TopologicalSpace B] (U : ℕ → Opens B)
    (hU : Monotone U) (hcover : (⋃ i, (U i : Set B)) = Set.univ)
    (K : Set B) (hK : IsCompact K) : ∃ i, K ⊆ U i :=
  hK.elim_directed_cover (fun i => (U i : Set B)) (fun i => (U i).isOpen)
    (by rw [hcover]; exact Set.subset_univ _)
    (fun i j => ⟨max i j,hU (le_max_left _ _),hU (le_max_right _ _)⟩)

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [T2Space B]
  (U : ℕ → Opens B) (hU : Monotone U)

/-- The genuine increasing-open compact-cohomology diagram uses the actual open extensions. -/
def compactDiagram (a : ℕ) : ℕ ⥤ ModuleCat.{0} ℚ where
  obj i := compactCohomology (restrictedProjection p (U i)) V a
  map f := openExtensionBetween p V (U _) (U _) (hU (leOfHom f)) a
  map_id i := openExtensionBetween_self p V (U i) a
  map_comp f g := (openExtensionBetween_comp p V _ _ _ (hU (leOfHom f)) (hU (leOfHom g)) a).symm

/-- The ambient actual open extensions form a cocone over increasing-open cohomology. -/
def compactCocone (a : ℕ) : Cocone (compactDiagram p V U hU a) where
  pt := compactCohomology p V a
  ι := {
    app := fun i => openExtension p V (U i) a
    naturality := fun i j f => by
      change openExtensionBetween p V (U i) (U j) (hU (leOfHom f)) a ≫
        openExtension p V (U j) a = openExtension p V (U i) a ≫ 𝟙 _
      simpa only [Category.comp_id] using openExtensionBetween_ambient p V (U i) (U j) (hU (leOfHom f)) a }

/-- The canonical comparison from the genuine increasing-open colimit to ambient compact cohomology. -/
def compactColimitMap (a : ℕ) : colimit (compactDiagram p V U hU a) ⟶ compactCohomology p V a :=
  colimit.desc _ (compactCocone p V U hU a)

/-- The canonical colimit comparison retains exactly the actual open-extension map at every stage. -/
theorem compactColimitMap_ι (a i : ℕ) :
    colimit.ι (compactDiagram p V U hU a) i ≫ compactColimitMap p V U hU a =
      openExtension p V (U i) a :=
  colimit.ι_desc _ _

end TernaryPoly.SingularLocalOpenUnion
