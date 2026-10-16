module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityHomeomorphSupport
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.ExtensionSupport

@[expose] public section

noncomputable section
namespace TernaryPoly.CompactInteriorRelativeBoundary
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCoefficient EquivariantSingularSmall
open SingularLocalCompactDuality

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- The actual compact-support-to-ordinary cohomology map, induced by literal support inclusions. -/
def compactForget (k : ℕ) : compactCohomology p V k ⟶ (localCochains p hp.out V).homology k :=
  compactCohomologyDesc p V k _ (fun K => homologyMap (supportInclusion p V K) k)
    (fun K L hKL => by erw [← homologyMap_comp,supportMap_inclusion])

/-- Forgetting support retains the actual ambient cochain of each fixed-support class. -/
theorem compactForget_classMap (K : Compacts B) (k : ℕ) :
    compactClassMap p V K k ≫ compactForget p V k = homologyMap (supportInclusion p V K) k :=
  compactCohomologyDesc_ι p V k _ _ _ K

variable [T2Space B]

/-- Genuine fixed-support excision preserves the actual map to ordinary cohomology. -/
theorem openSupportIso_forget (D : Opens B) (K : Compacts D) (k : ℕ) :
    (openSupportIso p V D K k).hom ≫ homologyMap (supportInclusion (restrictedProjection p D) V K) k =
      homologyMap (supportInclusion p V (openCompactImage D K)) k ≫
        homologyMap (localRestriction p D V) k := by
  change homologyMap _ k ≫ homologyMap _ k = homologyMap _ k ≫ homologyMap _ k
  erw [← homologyMap_comp,← homologyMap_comp,openRestrictionMap_inclusion]

/-- Inverse genuine support excision preserves the actual ordinary restriction map. -/
theorem openSupportIso_inv_forget (D : Opens B) (K : Compacts D) (k : ℕ) :
    (openSupportIso p V D K k).inv ≫ homologyMap (supportInclusion p V (openCompactImage D K)) k ≫
      homologyMap (localRestriction p D V) k =
        homologyMap (supportInclusion (restrictedProjection p D) V K) k := by
  erw [← openSupportIso_forget p V D K k,Iso.inv_hom_id_assoc]

/-- Actual extension from an open followed by ambient support-forgetting and restriction
is exactly support-forgetting on the open subset. -/
theorem openExtension_forget (D : Opens B) (k : ℕ) :
    openExtension p V D k ≫ compactForget p V k ≫ homologyMap (localRestriction p D V) k =
      compactForget (restrictedProjection p D) V k := by
  apply colimit.hom_ext
  intro K
  change compactClassMap (restrictedProjection p D) V K k ≫ _ =
    compactClassMap (restrictedProjection p D) V K k ≫ _
  erw [← Category.assoc,← Category.assoc,openExtension_classMap]
  simp only [Category.assoc]
  erw [← Category.assoc (compactClassMap p V (openCompactImage D K) k),
    compactForget_classMap,compactForget_classMap]
  exact openSupportIso_inv_forget p V D K k

variable {E' B' : TopCat.{0}} [MulAction G E'] [ContinuousConstSMul G E']
  (p' : E' ⟶ B') [hp' : Fact (IsQuotientCoveringMap p' G)]

omit [T2Space B] in
/-- Actual compact-support pullback along a genuine covering homeomorphism preserves
literal support-forgetting and the actual ordinary geometric cochain pullback. -/
theorem coveringCompactIso_forget (h : CoverHomeomorph (G := G) p p') (k : ℕ) :
    (coveringCompactIso h V k).hom ≫ compactForget p V k =
      compactForget p' V k ≫ homologyMap (coveringCochainMap h V) k := by
  apply colimit.hom_ext
  intro K
  change compactClassMap p' V K k ≫ _ = compactClassMap p' V K k ≫ _
  erw [← Category.assoc,coveringCompactIso_classMap,Category.assoc,
    compactForget_classMap,← Category.assoc,compactForget_classMap,
    ← homologyMap_comp,← homologyMap_comp,coveringSupportIso_inclusion]

end TernaryPoly.CompactInteriorRelativeBoundary
