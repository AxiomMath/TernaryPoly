module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.HomeomorphSupport
public import Mathlib.CategoryTheory.Limits.Final

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCapHomeomorph
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalConstant SingularLocalSupport

variable {X Y : TopCat.{0}} (h : X ≃ₜ Y) (V : ModuleCat.{0} ℚ)

/-- Homeomorphism inverse image is an actual order isomorphism of compact support sets. -/
def compactOrderIso : Compacts Y ≃o Compacts X where
  toFun K := ⟨h ⁻¹' (K : Set Y),h.isCompact_preimage.mpr K.isCompact⟩
  invFun L := ⟨h.symm ⁻¹' (L : Set X),h.symm.isCompact_preimage.mpr L.isCompact⟩
  left_inv K := by ext y; simp
  right_inv L := by ext x; simp
  map_rel_iff' := by
    intro K L
    constructor
    · intro hKL y hy
      have hh := hKL (show h (h.symm y) ∈ (K : Set Y) by simpa using hy)
      change h (h.symm y) ∈ (L : Set Y) at hh
      simpa using hh
    · exact Set.preimage_mono

/-- The actual relative cohomology diagrams are naturally isomorphic after reindexing supports. -/
def compactDiagramIso (a : ℕ) : compactCohomologyDiagram (𝟙 Y) (constantRep V) a ≅
    (compactOrderIso h).equivalence.functor ⋙ compactCohomologyDiagram (𝟙 X) (constantRep V) a :=
  NatIso.ofComponents (fun K => (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) a).mapIso
    (supportCochainIso h V (K : Set Y))) (fun {K L} f => by
      change homologyMap (supportMap (𝟙 Y) (constantRep V) K L (leOfHom f)) a ≫
        homologyMap (supportCochainIso h V L).hom a =
          homologyMap (supportCochainIso h V K).hom a ≫
            homologyMap (supportMap (𝟙 X) (constantRep V) (h ⁻¹' (K : Set Y)) (h ⁻¹' (L : Set Y))
              (Set.preimage_mono (leOfHom f))) a
      rw [← homologyMap_comp,← homologyMap_comp,supportCochainIso_natural])

/-- Actual compact-support cohomology pullback under a homeomorphism is an isomorphism. -/
def compactCohomologyIso (a : ℕ) : compactCohomology (𝟙 Y) (constantRep V) a ≅
    compactCohomology (𝟙 X) (constantRep V) a :=
  colim.mapIso (compactDiagramIso h V a) ≪≫
    Functor.Final.colimitIso (compactOrderIso h).equivalence.functor
      (compactCohomologyDiagram (𝟙 X) (constantRep V) a)

/-- The compact-support isomorphism acts by actual pullback on every actual support representative. -/
theorem compactCohomologyIso_classMap (a : ℕ) (K : Compacts Y) :
    compactClassMap (𝟙 Y) (constantRep V) K a ≫ (compactCohomologyIso h V a).hom =
      homologyMap (supportCochainIso h V K).hom a ≫
        compactClassMap (𝟙 X) (constantRep V) (compactOrderIso h K) a := by
  unfold compactCohomologyIso compactClassMap
  erw [Iso.trans_hom,Functor.mapIso_hom,colim_map,ι_colimMap_assoc]
  erw [Functor.Final.ι_colimitIso_hom]
  rfl

end TernaryPoly.SingularLocalCapHomeomorph
