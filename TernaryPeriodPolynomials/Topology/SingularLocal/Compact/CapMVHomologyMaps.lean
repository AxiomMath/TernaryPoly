module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Excision.Maps
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVFixed

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalHomology SingularLocalExcision EquivariantSingularSmall EquivariantSingularMayerVietoris

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (W : Rep.{0} ℚ G)
  (U D : Opens B) (hUD : U ⊔ D = ⊤)

/-- The genuine signed coefficient chain sequence on the pulled-back open cover. -/
def coefficientSequence : ShortComplex (ChainComplex (ModuleCat.{0} ℚ) ℕ) :=
  ShortComplex.mk
    (biprod.lift ((coefficients G W).map (interToLeft G E (preimageOpen p U) (preimageOpen p D)
      (preimage_invariant p U) (preimage_invariant p D)))
      (-((coefficients G W).map (interToRight G E (preimageOpen p U) (preimageOpen p D)
        (preimage_invariant p U) (preimage_invariant p D)))))
    (biprod.desc ((coefficients G W).map (leftToCover G E (preimageOpen p U) (preimageOpen p D)
      (preimage_invariant p U) (preimage_invariant p D) (preimageOpen_cover p U D hUD)))
      ((coefficients G W).map (rightToCover G E (preimageOpen p U) (preimageOpen p D)
        (preimage_invariant p U) (preimage_invariant p D) (preimageOpen_cover p U D hUD))))
    (by rw [biprod.lift_desc,Preadditive.neg_comp,← Functor.map_comp,← Functor.map_comp,inclusion_square]; simp)

/-- Arbitrary rational coefficients preserve actual small-chain Mayer–Vietoris short exactness. -/
theorem coefficientSequence_shortExact : (coefficientSequence p W U D hUD).ShortExact :=
  coefficientSquare_shortExact G E (preimageOpen p U) (preimageOpen p D)
    (preimage_invariant p U) (preimage_invariant p D) (preimageOpen_cover p U D hUD) W

variable [IsCancelSMul G E]

/-- The actual geometric local-chain sequence, with genuine small coefficient chains at its last term. -/
def ordinarySequence : ShortComplex (ChainComplex (ModuleCat.{0} ℚ) ℕ) :=
  transportShortComplex (coefficientSequence p W U D hUD)
    (localSupportedIso p ((U : Set B) ∩ (D : Set B)) W).symm
    (biprod.mapIso (localSupportedIso p U W).symm (localSupportedIso p D W).symm) (Iso.refl _)

/-- Actual geometric small-chain Mayer–Vietoris is short exact for every rational representation. -/
theorem ordinarySequence_shortExact : (ordinarySequence p W U D hUD).ShortExact :=
  ShortComplex.shortExact_of_iso (transportShortComplexIso _ _ _ _) (coefficientSequence_shortExact p W U D hUD)

/-- The genuine small coefficient chains map to actual ambient geometric local chains. -/
def smallToLocal : (ordinarySequence p W U D hUD).X₃ ⟶ localChains p hp.out W :=
  (coefficients G W).map (smallInclusion G E
    (SphereOddDegree.twoSetCover (preimageOpen p U) (preimageOpen p D) (preimageOpen_cover p U D hUD))
    (twoSetCover_invariant G E _ _ (preimage_invariant p U) (preimage_invariant p D)
      (preimageOpen_cover p U D hUD))) ≫ (chainIso p hp.out W).hom

/-- The actual small-chain inclusion is a quasi-isomorphism with the given rational local coefficients. -/
instance smallToLocal_quasiIso : QuasiIso (smallToLocal p W U D hUD) := by
  have h := smallCoefficientInclusion_quasiIso G E W
    (SphereOddDegree.twoSetCover (preimageOpen p U) (preimageOpen p D) (preimageOpen_cover p U D hUD))
    (twoSetCover_invariant G E _ _ (preimage_invariant p U) (preimage_invariant p D)
      (preimageOpen_cover p U D hUD))
  unfold smallToLocal
  exact quasiIso_comp (hφ := h) _ _

/-- The first ordinary chain arrow is exactly the signed pair of actual nested local inclusions. -/
theorem ordinarySequence_f : (ordinarySequence p W U D hUD).f =
    biprod.lift (nestedLocalInclusion p ((U : Set B) ∩ (D : Set B)) U Set.inter_subset_left W)
      (-nestedLocalInclusion p ((U : Set B) ∩ (D : Set B)) D Set.inter_subset_right W) := by
  change (localSupportedIso p ((U : Set B) ∩ (D : Set B)) W).hom ≫
    biprod.lift ((coefficients G W).map (subordinateMap G E
      (p ⁻¹' ((U : Set B) ∩ (D : Set B))) (p ⁻¹' (U : Set B))
      (preimage_invariant p _) (preimage_invariant p _) (Set.preimage_mono Set.inter_subset_left)))
      (-((coefficients G W).map (subordinateMap G E
        (p ⁻¹' ((U : Set B) ∩ (D : Set B))) (p ⁻¹' (D : Set B))
        (preimage_invariant p _) (preimage_invariant p _) (Set.preimage_mono Set.inter_subset_right)))) ≫
      biprod.map (localSupportedIso p U W).inv (localSupportedIso p D W).inv = _
  apply biprod.hom_ext
  · simp only [Category.assoc,biprod.map_fst,biprod.lift_fst_assoc,biprod.lift_fst]
    rw [← Category.assoc,localSupportedIso_naturality,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  · simp only [Category.assoc,biprod.map_snd,biprod.lift_snd_assoc,biprod.lift_snd,
      Preadditive.neg_comp,Preadditive.comp_neg]
    rw [← Category.assoc,localSupportedIso_naturality,Category.assoc,Iso.hom_inv_id,Category.comp_id]

/-- The second ordinary chain arrow is the sum of actual geometric inclusions after the small-chain comparison. -/
theorem ordinarySequence_g : (ordinarySequence p W U D hUD).g ≫ smallToLocal p W U D hUD =
    biprod.desc (localInclusion p U W) (localInclusion p D W) := by
  change (biprod.map (localSupportedIso p U W).hom (localSupportedIso p D W).hom ≫
    biprod.desc ((coefficients G W).map (leftToCover G E (preimageOpen p U) (preimageOpen p D)
      (preimage_invariant p U) (preimage_invariant p D) (preimageOpen_cover p U D hUD)))
      ((coefficients G W).map (rightToCover G E (preimageOpen p U) (preimageOpen p D)
        (preimage_invariant p U) (preimage_invariant p D) (preimageOpen_cover p U D hUD))) ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id]
  change (biprod.map (localSupportedIso p U W).hom (localSupportedIso p D W).hom ≫
    biprod.desc _ _) ≫
      ((coefficients G W).map (smallInclusion G E
        (SphereOddDegree.twoSetCover (preimageOpen p U) (preimageOpen p D) (preimageOpen_cover p U D hUD))
        (twoSetCover_invariant G E _ _ (preimage_invariant p U) (preimage_invariant p D)
          (preimageOpen_cover p U D hUD))) ≫ (chainIso p hp.out W).hom) = _
  rw [Category.assoc]
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc,biprod.inl_desc_assoc,biprod.inl_desc]
    rw [← Category.assoc ((coefficients G W).map _),← Functor.map_comp]
    rw [leftToCover,subordinateToSmall_inclusion]
    change (localSupportedIso p U W).hom ≫
      ((coefficients G W).map (subordinateInclusion G E (p ⁻¹' (U : Set B))
        (preimage_invariant p U)) ≫ (chainIso p hp.out W).hom) = _
    rw [← Category.assoc,localSupportedIso_inclusion,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  · simp only [biprod.inr_map_assoc,biprod.inr_desc_assoc,biprod.inr_desc]
    rw [← Category.assoc ((coefficients G W).map _),← Functor.map_comp]
    rw [rightToCover,subordinateToSmall_inclusion]
    change (localSupportedIso p D W).hom ≫
      ((coefficients G W).map (subordinateInclusion G E (p ⁻¹' (D : Set B))
        (preimage_invariant p D)) ≫ (chainIso p hp.out W).hom) = _
    rw [← Category.assoc,localSupportedIso_inclusion,Category.assoc,Iso.inv_hom_id,Category.comp_id]

end TernaryPoly.SingularLocalCompactCapMV
