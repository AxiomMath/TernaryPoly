module

public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundarySupportAdapter

@[expose] public section

noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCoefficient EquivariantSingularSmall
open SingularBoundaryRestriction SymmetricSpaceBordifiedQuotient IntegralGL3Congruence
open SymmetricSpaceBordifiedPrincipalSix

variable (V : Rep.{0} ℚ principalSix)

/-- The literal complement of the actual boundary, as an open set. -/
def boundaryComplementOpen : Opens (TopCat.of BordifiedOrbit) :=
  ⟨(boundary principalSix)ᶜ,by rw [← interior_eq_boundary_compl]; exact interiorOpen.isOpen⟩

/-- The literal boundary-complement open is the designated geometric interior. -/
theorem boundaryComplementOpen_eq : boundaryComplementOpen = interiorOpen :=
  SetLike.coe_injective interior_eq_boundary_compl.symm

/-- A compact class on any open inside the boundary complement maps to the whole-interior
support kernel by genuine inverse excision and literal support enlargement. -/
def openBoundarySupportClass (D : Opens (TopCat.of BordifiedOrbit)) (hD : (D : Set BordifiedOrbit) ⊆ (boundary principalSix)ᶜ)
    (K : Compacts D) (k : ℕ) :
    (supportCochains (restrictedProjection wholeProjection D) V K).homology k ⟶
      (supportCochains wholeProjection V (boundary principalSix)ᶜ).homology k :=
  (openSupportIso wholeProjection V D K k).inv ≫ homologyMap
    (supportMap wholeProjection V (openCompactImage D K) (boundary principalSix)ᶜ
      ((openCompactImage_subset D K).trans hD)) k

/-- The genuine fixed-support map respects every enlargement of compact supports. -/
theorem openBoundarySupportClass_natural (D : Opens (TopCat.of BordifiedOrbit))
    (hD : (D : Set BordifiedOrbit) ⊆ (boundary principalSix)ᶜ)
    (K L : Compacts D) (hKL : K ≤ L) (k : ℕ) :
    homologyMap (supportMap (restrictedProjection wholeProjection D) V K L hKL) k ≫
      openBoundarySupportClass V D hD L k = openBoundarySupportClass V D hD K k := by
  unfold openBoundarySupportClass
  erw [← Category.assoc,← openSupportIso_inv_natural wholeProjection V D K L hKL k,
    Category.assoc,← homologyMap_comp,supportMap_comp]

/-- The map from actual compact-support cohomology of an open to the whole-interior
support kernel is the literal colimit of inverse excision and support enlargement. -/
def openBoundarySupportMap (D : Opens (TopCat.of BordifiedOrbit))
    (hD : (D : Set BordifiedOrbit) ⊆ (boundary principalSix)ᶜ) (k : ℕ) :
    compactCohomology (restrictedProjection wholeProjection D) V k ⟶
      (supportCochains wholeProjection V (boundary principalSix)ᶜ).homology k :=
  compactCohomologyDesc (restrictedProjection wholeProjection D) V k _
    (fun K => openBoundarySupportClass V D hD K k)
    (fun K L hKL => openBoundarySupportClass_natural V D hD K L hKL k)

/-- The descended whole-interior support map retains its actual fixed-support formula. -/
theorem openBoundarySupportMap_classMap (D : Opens (TopCat.of BordifiedOrbit))
    (hD : (D : Set BordifiedOrbit) ⊆ (boundary principalSix)ᶜ) (K : Compacts D) (k : ℕ) :
    compactClassMap (restrictedProjection wholeProjection D) V K k ≫ openBoundarySupportMap V D hD k =
      openBoundarySupportClass V D hD K k := compactCohomologyDesc_ι _ _ _ _ _ _ _

/-- On the designated open interior, the direct support map is exactly the already-proved
literal compact/relative comparison followed by the identity-on-ambient support adapter. -/
theorem openBoundarySupportMap_eq (k : ℕ) :
    openBoundarySupportMap V interiorOpen interior_eq_boundary_compl.le k =
      compactToBoundary V k ≫ homologyMap (ambientBoundaryIso V).hom k ≫
        homologyMap (boundarySupportIso V).hom k := by
  apply compactCohomology_hom_ext
  intro K
  rw [openBoundarySupportMap_classMap,← Category.assoc,compactToBoundary_classMap]
  exact (fixedToBoundary_toSupport V K k).symm

/-- The direct whole-interior support map is an isomorphism on the designated interior. -/
theorem openBoundarySupportMap_isIso (k : ℕ) :
    IsIso (openBoundarySupportMap V interiorOpen interior_eq_boundary_compl.le k) := by
  rw [openBoundarySupportMap_eq]
  have := compactToBoundary_isIso V k
  infer_instance

/-- The literal compact-to-support map on the literal boundary-complement covering is an iso;
the equality of opens is used only to prove invertibility, not to define the map. -/
theorem boundarySupportMap_isIso (k : ℕ) :
    IsIso (openBoundarySupportMap V boundaryComplementOpen (Set.Subset.refl _) k) := by
  have h : ∀ (D : Opens (TopCat.of BordifiedOrbit))
      (hD : (D : Set BordifiedOrbit) ⊆ (boundary principalSix)ᶜ), D = interiorOpen →
        IsIso (openBoundarySupportMap V D hD k) := by
    intro D hD he
    subst D
    exact openBoundarySupportMap_isIso V k
  exact h boundaryComplementOpen (Set.Subset.refl _) boundaryComplementOpen_eq

/-- The actual compact cohomology of the literal boundary-complement covering equals the actual
whole-interior support kernel by genuine inverse excision and support enlargement. -/
def compactBoundarySupportIso (k : ℕ) :
    compactCohomology (restrictedProjection wholeProjection (boundary principalSix)ᶜ) V k ≅
      (supportCochains wholeProjection V (boundary principalSix)ᶜ).homology k := by
  change compactCohomology (restrictedProjection wholeProjection boundaryComplementOpen) V k ≅ _
  letI := boundarySupportMap_isIso V k
  exact asIso (openBoundarySupportMap V boundaryComplementOpen (Set.Subset.refl _) k)

/-- The literal boundary-complement compact/support iso retains the precise inverse-excision
and support-enlargement formula on every actual compact support. -/
theorem compactBoundarySupportIso_classMap (K : Compacts ((boundary principalSix)ᶜ : Set BordifiedOrbit)) (k : ℕ) :
    compactClassMap (restrictedProjection wholeProjection (boundary principalSix)ᶜ) V K k ≫
      (compactBoundarySupportIso V k).hom =
    (openSupportIso wholeProjection V boundaryComplementOpen K k).inv ≫ homologyMap
      (supportMap wholeProjection V (openCompactImage boundaryComplementOpen K) (boundary principalSix)ᶜ
        (openCompactImage_subset boundaryComplementOpen K)) k :=
  openBoundarySupportMap_classMap V boundaryComplementOpen (Set.Subset.refl _) K k

end TernaryPoly.CompactInteriorRelativeBoundary
