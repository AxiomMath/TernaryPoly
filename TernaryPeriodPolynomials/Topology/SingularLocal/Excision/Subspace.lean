module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Excision.Algebra
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallRestrictedNaturality
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Embeddings

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalExcision
open CategoryTheory Limits HomologicalComplex
open EquivariantSingularSmall EquivariantSingularMayerVietoris
open SingularLocalHomology SphereOddDegree

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]

variable [IsCancelSMul G E]

/-- Actual geometric local chains on a literal restricted covering. -/
abbrev restrictedLocalChains (A : Set B) (W : Rep.{0} ℚ G) :=
  localChains (restrictedProjection p A) (restrictedQuotientCovering p A) W

/-- The actual covariant geometric local-chain map of a subset inclusion. -/
def localInclusion (A : Set B) (W : Rep.{0} ℚ G) :
    restrictedLocalChains p A W ⟶ localChains p hp.out W := by
  exact localSpaceMap (sInclusion (p ⁻¹' A)) (fun _ _ => rfl) W
    (restrictedProjection p A) p (restrictedQuotientCovering p A) hp.out

/-- The actual local-chain map for two nested subsets of the same base. -/
def nestedLocalInclusion (A D : Set B) (hAD : A ⊆ D) (W : Rep.{0} ℚ G) :
    restrictedLocalChains p A W ⟶ restrictedLocalChains p D W := by
  exact localSpaceMap (subspaceInclusion E (p ⁻¹' A) (p ⁻¹' D) (Set.preimage_mono hAD))
    (fun _ _ => rfl) W (restrictedProjection p A) (restrictedProjection p D)
    (restrictedQuotientCovering p A) (restrictedQuotientCovering p D)

/-- The genuine restricted local chains identify with the tensor of actual supported chains. -/
def localSupportedIso (A : Set B) (W : Rep.{0} ℚ G) :
    restrictedLocalChains p A W ≅
      (coefficients G W).obj (subordinateComplex G E (p ⁻¹' A) (preimage_invariant p A)) := by
  exact (chainIso (restrictedProjection p A) (restrictedQuotientCovering p A) W).symm ≪≫
    (coefficients G W).mapIso (subspaceIso G E (p ⁻¹' A) (preimage_invariant p A) (fun _ _ => rfl))

/-- The actual restricted-to-supported comparison commutes with the ambient geometric inclusion. -/
theorem localSupportedIso_inclusion (A : Set B) (W : Rep.{0} ℚ G) :
    (localSupportedIso p A W).hom ≫
      (coefficients G W).map (subordinateInclusion G E (p ⁻¹' A) (preimage_invariant p A)) =
    localInclusion p A W ≫ (chainIso p hp.out W).inv := by
  change ((chainIso (restrictedProjection p A) (restrictedQuotientCovering p A) W).inv ≫
    (coefficients G W).map (subspaceCorestrict G E (p ⁻¹' A) (preimage_invariant p A) (fun _ _ => rfl))) ≫ _ = _
  rw [Category.assoc, ← Functor.map_comp, subspaceCorestrict_inclusion]
  simp [localInclusion, localSpaceMap, coinvariantSpaceMap, Category.assoc]

/-- Actual nested inclusions commute with the literal supported-chain comparison. -/
theorem localSupportedIso_naturality (A D : Set B) (hAD : A ⊆ D) (W : Rep.{0} ℚ G) :
    (localSupportedIso p A W).hom ≫
      (coefficients G W).map (subordinateMap G E (p ⁻¹' A) (p ⁻¹' D)
        (preimage_invariant p A) (preimage_invariant p D) (Set.preimage_mono hAD)) =
    nestedLocalInclusion p A D hAD W ≫ (localSupportedIso p D W).hom := by
  change ((chainIso (restrictedProjection p A) (restrictedQuotientCovering p A) W).inv ≫
    (coefficients G W).map (subspaceCorestrict G E (p ⁻¹' A) (preimage_invariant p A) (fun _ _ => rfl))) ≫ _ = _
  rw [Category.assoc, ← Functor.map_comp,
    subspaceCorestrict_naturality G E (p ⁻¹' A) (p ⁻¹' D)
      (preimage_invariant p A) (preimage_invariant p D) (fun _ _ => rfl) (fun _ _ => rfl)
      (Set.preimage_mono hAD), Functor.map_comp]
  simp [nestedLocalInclusion, localSpaceMap, coinvariantSpaceMap, localSupportedIso, subspaceIso, Category.assoc]

/-- The actual geometric subset inclusion is monic for every coefficient representation. -/
instance localInclusion_mono (A : Set B) (W : Rep.{0} ℚ G) : Mono (localInclusion p A W) := by
  apply mono_of_mono_f
  intro n
  exact (ModuleCat.mono_iff_injective _).mpr
    (localSpaceMap_injective (restrictedProjection p A) p (sInclusion (p ⁻¹' A)) (sInclusion A)
      (restricted_square p A) (restrictedQuotientCovering p A) hp.out (fun _ _ => rfl) W
      Subtype.val_injective n)

/-- The genuine supported inclusion remains monic after taking tensor coinvariants. -/
instance supportedCoefficientInclusion_mono (A : Set B) (W : Rep.{0} ℚ G) :
    Mono ((coefficients G W).map (subordinateInclusion G E (p ⁻¹' A) (preimage_invariant p A))) := by
  have h := localSupportedIso_inclusion p A W
  have heq : (coefficients G W).map (subordinateInclusion G E (p ⁻¹' A) (preimage_invariant p A)) =
      (localSupportedIso p A W).inv ≫ localInclusion p A W ≫ (chainIso p hp.out W).inv := by
    rw [← h, Iso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

end TernaryPoly.SingularLocalExcision
