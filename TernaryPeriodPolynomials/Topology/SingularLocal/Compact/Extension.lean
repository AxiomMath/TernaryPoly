module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.ExtensionMaps

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSupport
open CategoryTheory Limits HomologicalComplex TopologicalSpace SingularLocalCoefficient EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [T2Space B]

/-- The inverse of actual compact-support excision is natural for support enlargement. -/
theorem openSupportIso_inv_natural (D : Opens B) (K L : Compacts D)
    (hKL : (K : Set D) ⊆ L) (k : ℕ) :
    (openSupportIso p V D K k).inv ≫
      homologyMap (supportMap p V (openCompactImage D K : Set B) (openCompactImage D L : Set B)
        (Set.image_mono hKL)) k =
    homologyMap (supportMap (restrictedProjection p D) V (K : Set D) (L : Set D) hKL) k ≫
      (openSupportIso p V D L k).inv := by
  apply (cancel_mono (openSupportIso p V D L k).hom).mp
  rw [Category.assoc,openSupportIso_natural p V D K L hKL k,
    ← Category.assoc,Iso.inv_hom_id,Category.id_comp,
    Category.assoc,Iso.inv_hom_id,Category.comp_id]

/-- A fixed compact-support class on an open set extends through inverse genuine excision. -/
def openExtensionClass (D : Opens B) (K : Compacts D) (k : ℕ) :
    (supportCochains (restrictedProjection p D) V (K : Set D)).homology k ⟶ compactCohomology p V k :=
  (openSupportIso p V D K k).inv ≫ compactClassMap p V (openCompactImage D K) k

/-- Genuine extension of fixed-support classes is compatible with enlargement of support. -/
theorem openExtensionClass_natural (D : Opens B) (K L : Compacts D)
    (hKL : (K : Set D) ⊆ L) (k : ℕ) :
    homologyMap (supportMap (restrictedProjection p D) V (K : Set D) (L : Set D) hKL) k ≫
      openExtensionClass p V D L k = openExtensionClass p V D K k := by
  unfold openExtensionClass
  rw [← Category.assoc,← openSupportIso_inv_natural p V D K L hKL k,Category.assoc]
  rw [compactClassMap_natural p V (openCompactImage D K) (openCompactImage D L) (Set.image_mono hKL) k]

/-- Actual extension from compact-support cohomology on an open subset, defined by genuine
excision on each compact support and the actual colimit universal property. -/
def openExtension (D : Opens B) (k : ℕ) :
    compactCohomology (restrictedProjection p D) V k ⟶ compactCohomology p V k :=
  compactCohomologyDesc (restrictedProjection p D) V k (compactCohomology p V k)
    (fun K => openExtensionClass p V D K k)
    (fun K L hKL => openExtensionClass_natural p V D K L hKL k)

/-- Actual open extension agrees with inverse excision on every genuine fixed-support class. -/
theorem openExtension_classMap (D : Opens B) (K : Compacts D) (k : ℕ) :
    compactClassMap (restrictedProjection p D) V K k ≫ openExtension p V D k =
      (openSupportIso p V D K k).inv ≫ compactClassMap p V (openCompactImage D K) k :=
  compactCohomologyDesc_ι _ _ _ _ _ _ _

/-- Restricting an ambient fixed-support class to its containing open set and extending it back
retains its original compact-support cohomology class. -/
theorem openExtension_restriction (D : Opens B) (K : Compacts D) (k : ℕ) :
    homologyMap (openRestrictionMap p V D K) k ≫
      compactClassMap (restrictedProjection p D) V K k ≫ openExtension p V D k =
        compactClassMap p V (openCompactImage D K) k := by
  rw [openExtension_classMap]
  change (openSupportIso p V D K k).hom ≫ (openSupportIso p V D K k).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]

end TernaryPoly.SingularLocalSupport
