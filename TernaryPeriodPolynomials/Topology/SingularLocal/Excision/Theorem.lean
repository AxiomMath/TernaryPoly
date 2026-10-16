module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Excision.Maps

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalExcision
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open EquivariantSingularSmall EquivariantSingularMayerVietoris SingularLocalHomology

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] [IsCancelSMul G E]
  (A D : Opens B) (hAD : A ⊔ D = ⊤) (W : Rep.{0} ℚ G)

/-- The supported/small-chain route equals the actual geometric pair map. -/
theorem localExcisionMap_factorization :
    localExcisionMap p (A : Set B) D W ≫ relativeSupportedMap p A W =
      neighborhoodSupportedMap p A D W ≫
        supportedSmallMap G E (preimageOpen p A) (preimageOpen p D)
          (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD) W ≫
        smallRelativeMap G E (preimageOpen p A) (preimageOpen p D)
          (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD) W := by
  apply (cancel_epi (cokernel.π
    (nestedLocalInclusion p ((A : Set B) ∩ (D : Set B)) D Set.inter_subset_right W))).mp
  simp only [localExcisionMap, relativeSupportedMap, neighborhoodSupportedMap,
    supportedSmallMap, smallRelativeMap, cokernel.map, Category.assoc,
    cokernel.π_desc_assoc, cokernel.π_desc]
  rw [← Category.assoc ((coefficients G W).map (rightToCover G E (preimageOpen p A)
    (preimageOpen p D) (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD))),
    ← Functor.map_comp]
  rw [rightToCover, subordinateToSmall_inclusion]
  rw [← Category.assoc (localSupportedIso p (D : Set B) W).hom]
  exact congrArg (fun f => f ≫ cokernel.π ((coefficients G W).map
    (subordinateInclusion G E (p ⁻¹' (A : Set B)) (preimage_invariant p A))))
      (localSupportedIso_inclusion p (D : Set B) W).symm

include hAD in
/-- The literal geometric pair inclusion is a quasi-isomorphism for every rational representation. -/
theorem localExcisionMap_quasiIso : QuasiIso (localExcisionMap p (A : Set B) D W) := by
  have : Mono ((coefficients G W).map (subordinateInclusion G E
      (preimageOpen p A : Set E) (preimage_invariant p A))) :=
    supportedCoefficientInclusion_mono p (A : Set B) W
  have : QuasiIso (smallRelativeMap G E (preimageOpen p A) (preimageOpen p D)
      (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD) W) :=
    smallRelativeMap_quasiIso G E (preimageOpen p A) (preimageOpen p D)
      (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD) W
  have hc : QuasiIso (localExcisionMap p (A : Set B) D W ≫ relativeSupportedMap p A W) := by
    rw [localExcisionMap_factorization p A D hAD W]
    infer_instance
  exact (quasiIso_iff_comp_right (localExcisionMap p (A : Set B) D W)
    (relativeSupportedMap p A W)).mp hc

/-- Actual geometric local-coefficient excision on homology, in every degree. -/
def localExcisionHomologyIso (n : ℕ) :
    (neighborhoodRelativeChains p (A : Set B) D W).homology n ≅
      (relativeLocalChains p A W).homology n := by
  have := localExcisionMap_quasiIso p A D hAD W
  exact asIso (homologyMap (localExcisionMap p (A : Set B) D W) n)

/-- The geometric homology isomorphism is induced by the actual pair map. -/
theorem localExcisionHomologyIso_hom (n : ℕ) :
    (localExcisionHomologyIso p A D hAD W n).hom =
      homologyMap (localExcisionMap p (A : Set B) D W) n := rfl

end TernaryPoly.SingularLocalExcision
