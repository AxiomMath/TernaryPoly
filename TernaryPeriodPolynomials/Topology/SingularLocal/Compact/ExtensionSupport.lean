module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Extension

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSupport
open CategoryTheory Limits HomologicalComplex TopologicalSpace SingularLocalCoefficient EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [T2Space B]

/-- An ambient compact support contained in an open set is also a genuine compact in that subspace. -/
def compactWithinOpen (D : Opens B) (K : Compacts B) (hKD : (K : Set B) ⊆ D) : Compacts D :=
  ⟨Subtype.val ⁻¹' (K : Set B), by
    apply Topology.IsInducing.isCompact_preimage' Topology.IsEmbedding.subtypeVal.isInducing K.isCompact
    exact fun x hx => ⟨⟨x,hKD hx⟩,rfl⟩⟩

omit [T2Space B] in
/-- The literal image of the compact support viewed inside its containing open set is unchanged. -/
theorem openCompactImage_compactWithin (D : Opens B) (K : Compacts B) (hKD : (K : Set B) ⊆ D) :
    openCompactImage D (compactWithinOpen D K hKD) = K := by
  apply SetLike.coe_injective
  apply Set.image_preimage_eq_of_subset
  exact fun x hx => ⟨⟨x,hKD hx⟩,rfl⟩

/-- The actual compact-support class on the open set represented by an ambient support class. -/
def classInOpen (D : Opens B) (K : Compacts B) (hKD : (K : Set B) ⊆ D) (k : ℕ) :
    (supportCochains p V (K : Set B)).homology k ⟶ compactCohomology (restrictedProjection p D) V k :=
  (supportExcisionIso p V D K K.isCompact.isClosed hKD k).hom ≫
    compactClassMap (restrictedProjection p D) V (compactWithinOpen D K hKD) k

/-- The open representative retains any explicit compact-support identification. -/
theorem classInOpen_congr (D : Opens B) (K : Compacts B) (hKD : (K : Set B) ⊆ D)
    (L : Compacts D) (hpre : (Subtype.val ⁻¹' (K : Set B) : Set D) = (L : Set D)) (k : ℕ) :
    classInOpen p V D K hKD k =
      homologyMap (supportToOpen p V D (K : Set B) ≫
        supportCongrMap (restrictedProjection p D) V _ _ hpre) k ≫
          compactClassMap (restrictedProjection p D) V L k := by
  have hL : compactWithinOpen D K hKD = L := SetLike.coe_injective hpre
  subst L
  rfl

/-- Open representatives commute with genuine enlargement of ambient compact support. -/
theorem classInOpen_natural (D : Opens B) (K L : Compacts B)
    (hKL : (K : Set B) ⊆ L) (hLD : (L : Set B) ⊆ D) (k : ℕ) :
    homologyMap (supportMap p V (K : Set B) (L : Set B) hKL) k ≫
      classInOpen p V D L hLD k = classInOpen p V D K (hKL.trans hLD) k := by
  change homologyMap _ k ≫ homologyMap (supportToOpen p V D (L : Set B)) k ≫ _ =
    homologyMap (supportToOpen p V D (K : Set B)) k ≫ _
  erw [← Category.assoc,← homologyMap_comp,supportToOpen_natural,homologyMap_comp,Category.assoc]
  erw [compactClassMap_natural (restrictedProjection p D) V (compactWithinOpen D K (hKL.trans hLD))
    (compactWithinOpen D L hLD) (fun _ hx => hKL hx) k]

/-- Open extension cancels genuine restriction with any explicit identification of the support. -/
theorem openExtension_restriction_congr (D : Opens B) (K : Compacts B) (L : Compacts D)
    (himage : openCompactImage D L = K)
    (hpre : (Subtype.val ⁻¹' (K : Set B) : Set D) = (L : Set D)) (k : ℕ) :
    homologyMap (supportToOpen p V D (K : Set B) ≫
      supportCongrMap (restrictedProjection p D) V _ _ hpre) k ≫
      compactClassMap (restrictedProjection p D) V L k ≫ openExtension p V D k =
        compactClassMap p V K k := by
  subst K
  exact openExtension_restriction p V D L k

/-- Restricting an ambient compact-support representative to a containing open set and extending it
back gives the original actual compact-support class. -/
theorem classInOpen_extension (D : Opens B) (K : Compacts B) (hKD : (K : Set B) ⊆ D) (k : ℕ) :
    classInOpen p V D K hKD k ≫ openExtension p V D k = compactClassMap p V K k := by
  have h := openExtension_restriction_congr p V D K (compactWithinOpen D K hKD)
    (openCompactImage_compactWithin D K hKD) rfl k
  simp only [supportCongrMap] at h
  exact (Category.assoc _ _ _).trans h

/-- The actual open-extension formula for any ambient compact support lying in the open set. -/
theorem openExtension_ambient_classMap (D : Opens B) (K : Compacts B)
    (hKD : (K : Set B) ⊆ D) (k : ℕ) :
    compactClassMap (restrictedProjection p D) V (compactWithinOpen D K hKD) k ≫
      openExtension p V D k =
    (supportExcisionIso p V D K K.isCompact.isClosed hKD k).inv ≫ compactClassMap p V K k := by
  apply (cancel_epi (supportExcisionIso p V D K K.isCompact.isClosed hKD k).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans (classInOpen_extension p V D K hKD k)

end TernaryPoly.SingularLocalSupport
