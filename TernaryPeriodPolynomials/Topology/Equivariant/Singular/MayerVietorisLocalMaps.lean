module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisLocalSequence
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisRestriction

@[expose] public section

noncomputable section
namespace TernaryPoly.EquivariantSingularMayerVietoris
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall TopologicalSpace
open SingularLocalCoefficient

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (A D : Opens B) (hAD : A ⊔ D = ⊤)
  (W : Rep.{0} ℚ G)

/-- The literal restriction of ambient geometric local cochains to the actual small-chain Hom complex. -/
def localToSmall : localCochains p hp.out W ⟶ homCochains (localCoverChains p A D hAD) W :=
  (cochainIso p hp.out W).inv ≫ smallRestriction G E
    (SphereOddDegree.twoSetCover (preimageOpen p A) (preimageOpen p D) (preimageOpen_cover p A D hAD))
    (twoSetCover_invariant G E _ _ (preimage_invariant p A) (preimage_invariant p D)
      (preimageOpen_cover p A D hAD)) W

/-- The actual ambient geometric comparison to small cochains is a quasi-isomorphism. -/
instance localToSmall_quasiIso : QuasiIso (localToSmall p A D hAD W) := by
  have : IsCancelSMul G E := hp.out.isCancelSMul
  unfold localToSmall
  infer_instance

/-- The first map in geometric Mayer–Vietoris is exactly the pair of actual local restrictions. -/
theorem localSmallSequence_f :
    localToSmall p A D hAD W ≫ (localSmallSequence p A D hAD W).f =
      biprod.lift (localRestriction p A W) (localRestriction p D W) := by
  change ((cochainIso p hp.out W).inv ≫ smallRestriction G E (SphereOddDegree.twoSetCover (preimageOpen p A) (preimageOpen p D) (preimageOpen_cover p A D hAD)) (twoSetCover_invariant G E (preimageOpen p A) (preimageOpen p D) (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD)) W) ≫
    (𝟙 _ ≫ (separatedShortComplex G E (preimageOpen p A) (preimageOpen p D) (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD) W).f ≫
      (biprod.mapIso (subordinateLocalIso p A W) (subordinateLocalIso p D W)).hom) = _
  rw [Category.id_comp, separated_f G E (preimageOpen p A) (preimageOpen p D) (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD) W]
  change ((cochainIso p hp.out W).inv ≫ smallRestriction G E (SphereOddDegree.twoSetCover (preimageOpen p A) (preimageOpen p D) (preimageOpen_cover p A D hAD)) (twoSetCover_invariant G E (preimageOpen p A) (preimageOpen p D) (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD)) W) ≫
    (biprod.lift (homPullback (leftToCover G E (preimageOpen p A) (preimageOpen p D) (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD)) W) (homPullback (rightToCover G E (preimageOpen p A) (preimageOpen p D) (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD)) W) ≫
      biprod.map (subordinateLocalIso p A W).hom (subordinateLocalIso p D W).hom) = _
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst]
    rw [← Category.assoc (smallRestriction G E (SphereOddDegree.twoSetCover (preimageOpen p A) (preimageOpen p D) (preimageOpen_cover p A D hAD)) (twoSetCover_invariant G E (preimageOpen p A) (preimageOpen p D) (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD)) W), leftToCover, subordinateToSmall_restriction]
    change (cochainIso p hp.out W).inv ≫
      (homPullback (subordinateInclusion G E (p ⁻¹' (↑A : Set B)) (preimage_invariant p A)) W ≫
        (subordinateLocalIso p A W).hom) = _
    rw [subordinateLocalIso_restriction p A W, Iso.inv_hom_id_assoc]
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd]
    rw [← Category.assoc (smallRestriction G E (SphereOddDegree.twoSetCover (preimageOpen p A) (preimageOpen p D) (preimageOpen_cover p A D hAD)) (twoSetCover_invariant G E (preimageOpen p A) (preimageOpen p D) (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD)) W), rightToCover, subordinateToSmall_restriction]
    change (cochainIso p hp.out W).inv ≫
      (homPullback (subordinateInclusion G E (p ⁻¹' (↑D : Set B)) (preimage_invariant p D)) W ≫
        (subordinateLocalIso p D W).hom) = _
    rw [subordinateLocalIso_restriction p D W, Iso.inv_hom_id_assoc]

/-- The second map in geometric Mayer–Vietoris is exactly left restriction minus right restriction. -/
theorem localSmallSequence_g : (localSmallSequence p A D hAD W).g =
    biprod.desc (nestedLocalRestriction p ((A : Set B) ∩ (D : Set B)) A Set.inter_subset_left W)
      (-nestedLocalRestriction p ((A : Set B) ∩ (D : Set B)) D Set.inter_subset_right W) := by
  change (biprod.mapIso (subordinateLocalIso p A W) (subordinateLocalIso p D W)).inv ≫
    (separatedShortComplex G E (preimageOpen p A) (preimageOpen p D) (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD) W).g ≫
      (subordinateLocalIso p ((A : Set B) ∩ (D : Set B)) W).hom = _
  rw [separated_g G E (preimageOpen p A) (preimageOpen p D) (preimage_invariant p A) (preimage_invariant p D) (preimageOpen_cover p A D hAD) W]
  change biprod.map (subordinateLocalIso p A W).inv (subordinateLocalIso p D W).inv ≫
    biprod.desc (homPullback (subordinateMap G E (p ⁻¹' ((A : Set B) ∩ (D : Set B))) (p ⁻¹' (↑A : Set B)) (preimage_invariant p ((A : Set B) ∩ (D : Set B))) (preimage_invariant p A) (Set.preimage_mono Set.inter_subset_left)) W) (-homPullback (subordinateMap G E (p ⁻¹' ((A : Set B) ∩ (D : Set B))) (p ⁻¹' (↑D : Set B)) (preimage_invariant p ((A : Set B) ∩ (D : Set B))) (preimage_invariant p D) (Set.preimage_mono Set.inter_subset_right)) W) ≫
      (subordinateLocalIso p ((A : Set B) ∩ (D : Set B)) W).hom = _
  apply biprod.hom_ext'
  · simp only [ biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
    rw [subordinateLocalIso_naturality, Iso.inv_hom_id_assoc]
  · simp only [ biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc,
      Preadditive.neg_comp, Preadditive.comp_neg]
    rw [subordinateLocalIso_naturality, Iso.inv_hom_id_assoc]

end TernaryPoly.EquivariantSingularMayerVietoris
