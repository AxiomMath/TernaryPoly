module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Excision.Subspace
public import TernaryPeriodPolynomials.Topology.SingularLocal.Excision.Small
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisLocalSequence

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalExcision
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open EquivariantSingularSmall EquivariantSingularMayerVietoris SingularLocalHomology

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] [IsCancelSMul G E]

omit [IsCancelSMul G E] in
/-- Supported-chain inclusions compose with their actual ambient inclusion. -/
theorem subordinateMap_inclusion (S T : Set E) (hS : InvariantSet G E S)
    (hT : InvariantSet G E T) (hST : S ⊆ T) :
    subordinateMap G E S T hS hT hST ≫ subordinateInclusion G E T hT =
      subordinateInclusion G E S hS := by
  ext n c
  rfl

/-- Geometric local-chain inclusions compose with the actual ambient inclusion. -/
theorem nestedLocalInclusion_inclusion (A D : Set B) (hAD : A ⊆ D) (W : Rep.{0} ℚ G) :
    nestedLocalInclusion p A D hAD W ≫ localInclusion p D W = localInclusion p A W := by
  apply (cancel_mono (chainIso p hp.out W).inv).mp
  rw [Category.assoc, ← localSupportedIso_inclusion, ← Category.assoc,
    ← localSupportedIso_naturality, Category.assoc, ← Functor.map_comp,
    subordinateMap_inclusion, localSupportedIso_inclusion]

/-- Actual geometric relative chains, as the literal cokernel of subset inclusion. -/
abbrev relativeLocalChains (A : Set B) (W : Rep.{0} ℚ G) := cokernel (localInclusion p A W)

/-- Actual geometric relative chains of the neighborhood/intersection pair. -/
abbrev neighborhoodRelativeChains (A D : Set B) (W : Rep.{0} ℚ G) :=
  cokernel (nestedLocalInclusion p (A ∩ D) D Set.inter_subset_right W)

/-- The actual geometric pair-inclusion square, before passing to relative chains. -/
theorem localExcision_square (A D : Set B) (W : Rep.{0} ℚ G) :
    nestedLocalInclusion p (A ∩ D) D Set.inter_subset_right W ≫ localInclusion p D W =
      nestedLocalInclusion p (A ∩ D) A Set.inter_subset_left W ≫ localInclusion p A W := by
  rw [nestedLocalInclusion_inclusion, nestedLocalInclusion_inclusion]

/-- The genuine local-coefficient excision map induced by the literal map of pairs. -/
def localExcisionMap (A D : Set B) (W : Rep.{0} ℚ G) :
    neighborhoodRelativeChains p A D W ⟶ relativeLocalChains p A W :=
  cokernel.map _ _ (nestedLocalInclusion p (A ∩ D) A Set.inter_subset_left W)
    (localInclusion p D W) (localExcision_square p A D W)

/-- The excision map retains the exact geometric chain projection square. -/
theorem localExcisionMap_projection (A D : Set B) (W : Rep.{0} ℚ G) :
    cokernel.π (nestedLocalInclusion p (A ∩ D) D Set.inter_subset_right W) ≫
      localExcisionMap p A D W = localInclusion p D W ≫ cokernel.π (localInclusion p A W) := by
  simp [localExcisionMap, cokernel.map]

/-- The literal relative local chains identify with the actual supported tensor quotient. -/
def relativeSupportedMap (A : Set B) (W : Rep.{0} ℚ G) :
    relativeLocalChains p A W ⟶
      cokernel ((coefficients G W).map
        (subordinateInclusion G E (p ⁻¹' A) (preimage_invariant p A))) :=
  cokernel.map _ _ (localSupportedIso p A W).hom (chainIso p hp.out W).inv
    (localSupportedIso_inclusion p A W).symm

instance relativeSupportedMap_isIso (A : Set B) (W : Rep.{0} ℚ G) :
    IsIso (relativeSupportedMap p A W) := by
  unfold relativeSupportedMap
  infer_instance

/-- The actual neighborhood pair identifies with the supported intersection quotient. -/
def neighborhoodSupportedMap (A D : Opens B) (W : Rep.{0} ℚ G) :
    neighborhoodRelativeChains p (A : Set B) D W ⟶
      cokernel ((coefficients G W).map (interToRight G E (preimageOpen p A) (preimageOpen p D)
        (preimage_invariant p A) (preimage_invariant p D))) :=
  cokernel.map _ _ (localSupportedIso p ((A : Set B) ∩ (D : Set B)) W).hom
    (localSupportedIso p D W).hom (localSupportedIso_naturality p _ _ Set.inter_subset_right W).symm

instance neighborhoodSupportedMap_isIso (A D : Opens B) (W : Rep.{0} ℚ G) :
    IsIso (neighborhoodSupportedMap p A D W) := by
  change IsIso ((cokernel.mapIso
    (nestedLocalInclusion p ((A : Set B) ∩ (D : Set B)) D Set.inter_subset_right W)
    ((coefficients G W).map (interToRight G E (preimageOpen p A) (preimageOpen p D)
      (preimage_invariant p A) (preimage_invariant p D)))
    (localSupportedIso p ((A : Set B) ∩ (D : Set B)) W) (localSupportedIso p D W)
    (localSupportedIso_naturality p _ _ Set.inter_subset_right W).symm).hom)
  infer_instance

end TernaryPoly.SingularLocalExcision
