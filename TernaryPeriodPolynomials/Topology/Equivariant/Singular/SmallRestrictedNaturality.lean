module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallRestrictedCover

@[expose] public section

noncomputable section
namespace TernaryPoly.EquivariantSingularSmall
open CategoryTheory HomologicalComplex SingularCoverNaturality SingularLocalCoefficient
open EquivariantSingularMayerVietoris

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (A D : Set B) (hAD : A ⊆ D)

/-- The genuine inclusion square between two actual restrictions of a quotient covering. -/
theorem nestedRestricted_square :
    subspaceInclusion E (p ⁻¹' A) (p ⁻¹' D) (Set.preimage_mono hAD) ≫ restrictedProjection p D =
      restrictedProjection p A ≫ subspaceInclusion B A D hAD := rfl

/-- Actual local-system restriction between nested base subsets. -/
def nestedLocalRestriction (W : Rep.{0} ℚ G) :
    localCochains (restrictedProjection p D) (restrictedQuotientCovering p D) W ⟶
      localCochains (restrictedProjection p A) (restrictedQuotientCovering p A) W :=
  localPullback (restrictedProjection p A) (restrictedProjection p D)
    (subspaceInclusion E (p ⁻¹' A) (p ⁻¹' D) (Set.preimage_mono hAD)) (subspaceInclusion B A D hAD)
    (nestedRestricted_square p A D hAD) (restrictedQuotientCovering p A)
    (restrictedQuotientCovering p D) (fun _ _ => rfl) W

/-- The actual subordinate-chain comparison preserves each geometric nested local restriction. -/
theorem subordinateLocalIso_naturality (W : Rep.{0} ℚ G) :
    homPullback (subordinateMap G E (p ⁻¹' A) (p ⁻¹' D)
      (preimage_invariant p A) (preimage_invariant p D) (Set.preimage_mono hAD)) W ≫
      (subordinateLocalIso p A W).hom =
    (subordinateLocalIso p D W).hom ≫ nestedLocalRestriction p A D hAD W := by
  rw [subordinateLocalIso, Iso.trans_hom, ← Category.assoc, subspaceCochainIso_naturality,
    Category.assoc]
  change (subspaceCochainIso G E (p ⁻¹' D) (preimage_invariant p D) (fun _ _ => rfl) W).hom ≫
    (cochainPullback _ _ W ≫ (cochainIso (restrictedProjection p A) (restrictedQuotientCovering p A) W).hom) = _
  rw [cochainIso_pullback (restrictedProjection p A) (restrictedProjection p D)
    (subspaceInclusion E (p ⁻¹' A) (p ⁻¹' D) (Set.preimage_mono hAD)) (subspaceInclusion B A D hAD)
    (nestedRestricted_square p A D hAD) (restrictedQuotientCovering p A)
    (restrictedQuotientCovering p D) (fun _ _ => rfl) W]
  rfl

end TernaryPoly.EquivariantSingularSmall
