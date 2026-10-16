module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.Excision
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Cohomology

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSupport
open CategoryTheory Limits HomologicalComplex TopologicalSpace SingularLocalCoefficient EquivariantSingularSmall

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- Equality of supports gives the literal transport map between their actual cochain kernels. -/
abbrev supportCongrMap (K L : Set B) (h : K = L) : supportCochains p V K ⟶ supportCochains p V L :=
  eqToHom (congrArg (supportCochains p V) h)

/-- Transport through equal supports retains the same ambient cochain. -/
theorem supportCongrMap_inclusion (K L : Set B) (h : K = L) :
    supportCongrMap p V K L h ≫ supportInclusion p V L = supportInclusion p V K := by
  subst L
  simp

/-- The ambient compact support underlying a compact subset of an open set. -/
abbrev openCompactImage (D : Opens B) (K : Compacts D) : Compacts B :=
  K.map (Subtype.val : D → B) continuous_subtype_val

/-- Pulling the actual compact image back to the open set recovers the original support. -/
theorem openCompactImage_preimage (D : Opens B) (K : Compacts D) :
    (Subtype.val ⁻¹' (openCompactImage D K : Set B) : Set D) = (K : Set D) :=
  Set.preimage_image_eq _ Subtype.val_injective

/-- The image compact support lies inside the actual open set. -/
theorem openCompactImage_subset (D : Opens B) (K : Compacts D) :
    (openCompactImage D K : Set B) ⊆ D := by
  rintro _ ⟨x,_,rfl⟩
  exact x.property

/-- Genuine cochain restriction from the image compact support in the ambient space to the
original support in the open subset. -/
def openRestrictionMap (D : Opens B) (K : Compacts D) :
    supportCochains p V (openCompactImage D K : Set B) ⟶
      supportCochains (restrictedProjection p D) V (K : Set D) :=
  supportToOpen p V D (openCompactImage D K : Set B) ≫
    supportCongrMap (restrictedProjection p D) V _ _ (openCompactImage_preimage D K)

/-- The genuine compact-support restriction retains the literal restriction of ambient cochains. -/
theorem openRestrictionMap_inclusion (D : Opens B) (K : Compacts D) :
    openRestrictionMap p V D K ≫ supportInclusion (restrictedProjection p D) V (K : Set D) =
      supportInclusion p V (openCompactImage D K : Set B) ≫ localRestriction p D V := by
  rw [openRestrictionMap,Category.assoc,supportCongrMap_inclusion,supportToOpen_inclusion]

/-- Actual compact-support restriction is natural under enlargement of compact support. -/
theorem openRestrictionMap_natural (D : Opens B) (K L : Compacts D) (hKL : (K : Set D) ⊆ L) :
    supportMap p V (openCompactImage D K : Set B) (openCompactImage D L : Set B)
      (Set.image_mono hKL) ≫ openRestrictionMap p V D L =
    openRestrictionMap p V D K ≫ supportMap (restrictedProjection p D) V (K : Set D) (L : Set D) hKL := by
  apply (cancel_mono (supportInclusion (restrictedProjection p D) V (L : Set D))).mp
  rw [Category.assoc,openRestrictionMap_inclusion p V D L,← Category.assoc,
    supportMap_inclusion p V (openCompactImage D K) (openCompactImage D L) (Set.image_mono hKL),
    Category.assoc,supportMap_inclusion,openRestrictionMap_inclusion]

variable [T2Space B]

/-- Restriction from an image compact support to its containing open subset is a genuine
quasi-isomorphism, without restrictions on the rational coefficient representation. -/
instance openRestrictionMap_quasiIso (D : Opens B) (K : Compacts D) :
    QuasiIso (openRestrictionMap p V D K) := by
  have := supportToOpen_quasiIso p V D (openCompactImage D K : Set B)
    (openCompactImage D K).isCompact.isClosed (openCompactImage_subset D K)
  unfold openRestrictionMap supportCongrMap
  infer_instance

/-- Actual compact-support excision for a compact subset of an open set. -/
def openSupportIso (D : Opens B) (K : Compacts D) (k : ℕ) :
    (supportCochains p V (openCompactImage D K : Set B)).homology k ≅
      (supportCochains (restrictedProjection p D) V (K : Set D)).homology k :=
  asIso (homologyMap (openRestrictionMap p V D K) k)

/-- Actual fixed-support excision retains the genuine support-enlargement maps. -/
theorem openSupportIso_natural (D : Opens B) (K L : Compacts D) (hKL : (K : Set D) ⊆ L) (k : ℕ) :
    homologyMap (supportMap p V (openCompactImage D K : Set B) (openCompactImage D L : Set B)
      (Set.image_mono hKL)) k ≫ (openSupportIso p V D L k).hom =
    (openSupportIso p V D K k).hom ≫ homologyMap
      (supportMap (restrictedProjection p D) V (K : Set D) (L : Set D) hKL) k := by
  change homologyMap _ k ≫ homologyMap _ k = homologyMap _ k ≫ homologyMap _ k
  rw [← homologyMap_comp,← homologyMap_comp,openRestrictionMap_natural]

end TernaryPoly.SingularLocalSupport
