module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.AugmentationNaturality
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalFlipNaturality

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory

variable {A B : CochainComplex (ModuleCat.{0} ℝ) ℕ} {K L : RealBicomplex}

/-- The actual vertical coefficient augmentation comparison after the genuine signed axis flip. -/
def verticalAugmentationDegreeTwoIso (a : TotalAugmentation A K.flip) (ha : a.ExactRows) :
    A.homology 2 ≅ (totalWindow K).homology :=
  augmentationDegreeTwoIso a ha ≪≫ (totalFlipHomologyIso K).symm

/-- Genuine vertical augmentation comparisons are natural for actual commuting coefficient maps. -/
theorem verticalAugmentationDegreeTwoIso_naturality (f : K ⟶ L)
    (a : TotalAugmentation A K.flip) (b : TotalAugmentation B L.flip) (ha : a.ExactRows) (hb : b.ExactRows)
    (g : A ⟶ B) (h : a.map ≫ ((HomologicalComplex₂.flipFunctor (ModuleCat ℝ)
      (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map f).f 0 = g ≫ b.map) :
    (verticalAugmentationDegreeTwoIso a ha).hom ≫ ShortComplex.homologyMap (totalWindowMap f) =
      HomologicalComplex.homologyMap g 2 ≫ (verticalAugmentationDegreeTwoIso b hb).hom := by
  let ff := (HomologicalComplex₂.flipFunctor (ModuleCat ℝ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map f
  let aa := (augmentationDegreeTwoIso a ha).hom
  let bb := (augmentationDegreeTwoIso b hb).hom
  let gg := HomologicalComplex.homologyMap g 2
  calc
    _ = aa ≫ ((totalFlipHomologyIso K).inv ≫ ShortComplex.homologyMap (totalWindowMap f)) := Category.assoc _ _ _
    _ = aa ≫ (ShortComplex.homologyMap (totalWindowMap ff) ≫ (totalFlipHomologyIso L).inv) :=
      congrArg (fun u => aa ≫ u) (totalFlipHomologyIso_inv_naturality f).symm
    _ = (aa ≫ ShortComplex.homologyMap (totalWindowMap ff)) ≫ (totalFlipHomologyIso L).inv :=
      (Category.assoc _ _ _).symm
    _ = (gg ≫ bb) ≫ (totalFlipHomologyIso L).inv :=
      congrArg (fun u => u ≫ (totalFlipHomologyIso L).inv)
        (augmentationDegreeTwoIso_naturality ff a b ha hb g h)
    _ = _ := Category.assoc _ _ _

/-- Passing through two genuine isomorphisms transports an exact commuting comparison square. -/
theorem isoComparison_square {C : Type*} [Category* C] {A B X Y : C}
    (a : A ≅ X) (b : B ≅ Y) (f : A ⟶ B) (g : X ⟶ Y)
    (h : a.hom ≫ g = f ≫ b.hom) : a.inv ≫ f = g ≫ b.inv := by
  apply (cancel_epi a.hom).mp
  rw [←Category.assoc,Iso.hom_inv_id,Category.id_comp,←Category.assoc,h,
    Category.assoc,Iso.hom_inv_id,Category.comp_id]

/-- The two actual arms of a common isomorphism span determine its exact naturality square. -/
theorem commonSpan_square {C : Type*} [Category* C] {S T A B X Y : C}
    (a : S ≅ A) (b : S ≅ B) (x : T ≅ X) (y : T ≅ Y)
    (s : S ⟶ T) (f : A ⟶ X) (g : B ⟶ Y)
    (ha : a.hom ≫ f = s ≫ x.hom) (hb : b.hom ≫ g = s ≫ y.hom) :
    (a.symm ≪≫ b).hom ≫ g = f ≫ (x.symm ≪≫ y).hom := by
  apply (cancel_epi a.hom).mp
  simp only [Iso.trans_hom,Iso.symm_hom,←Category.assoc,Iso.hom_inv_id,Category.id_comp]
  rw [hb,ha,Category.assoc,Category.assoc,Iso.hom_inv_id_assoc]

/-- Composing two actual comparison squares through inverse descent isomorphisms preserves naturality. -/
theorem descentComparison_square {C : Type*} [Category* C] {U V A B X Y : C}
    (u : U ≅ A) (v : V ≅ B) (a : X ≅ A) (b : Y ≅ B)
    (h : U ⟶ V) (s : X ⟶ Y) (t : A ⟶ B)
    (hu : u.hom ≫ t = h ≫ v.hom) (ha : a.hom ≫ t = s ≫ b.hom) :
    (u ≪≫ a.symm).hom ≫ s = h ≫ (v ≪≫ b.symm).hom := by
  simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc]
  rw [isoComparison_square a b s t ha,←Category.assoc,hu,Category.assoc]

end TernaryPoly.SmoothSingularGlobal
