module

public import TernaryPeriodPolynomials.Topology.Equivariant.MayerVietoris.HomologyAugmentation

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantMayerVietorisHomology
open CategoryTheory Limits

variable {C : Type*} [Category C]

theorem augmentation_composite {X Y Z W R : C} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : Z ⟶ W) (d : W ⟶ R) (e : Z ⟶ R) (h : c ≫ d=e) :
    (a ≫ b ≫ c) ≫ d=a ≫ b ≫ e := by
  simp only [Category.assoc,h]

theorem biprod_augmentation_square [Preadditive C] [HasBinaryBiproducts C]
    {X Y Z A B R : C} (f : X ⟶ Z) (g : Y ⟶ Z) (a : Z ⟶ R)
    (e : X ≅ A) (d : Y ≅ B) (p : A ⟶ R) (q : B ⟶ R)
    (hf : f ≫ a=e.hom ≫ p) (hg : g ≫ a=d.hom ≫ q) :
    biprod.desc f g ≫ a=(biprod.mapIso e d).hom ≫ biprod.desc p q := by
  apply biprod.hom_ext'
  · simpa only [biprod.mapIso_hom,biprod.inl_map_assoc,biprod.inl_desc_assoc,Category.assoc,
      biprod.inl_desc] using hf
  · simpa only [biprod.mapIso_hom,biprod.inr_map_assoc,biprod.inr_desc_assoc,Category.assoc,
      biprod.inr_desc] using hg

/-- Cancellation of the ambient comparison in a composite of actual comparison isomorphisms. -/
theorem iso_cancel_composite {X Y Z W R : C} (i : X ≅ Y) (e : X ≅ Z) (k : Z ≅ W) (a : W ≅ R) :
    i.hom ≫ ((i.symm ≪≫ e ≪≫ k) ≪≫ a).hom=e.hom ≫ k.hom ≫ a.hom := by
  simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc,Iso.hom_inv_id_assoc]

end TernaryPoly.EquivariantMayerVietorisHomology
