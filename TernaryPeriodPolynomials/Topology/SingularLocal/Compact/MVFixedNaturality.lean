module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVFixed

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits HomologicalComplex SingularLocalSupport

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  (K L K' L' : Set B) (hK : IsClosed K) (hL : IsClosed L) (hK' : IsClosed K') (hL' : IsClosed L')
  (hKK' : K ⊆ K') (hLL' : L ⊆ L')

/-- The actual intersection cohomology comparison is natural under support enlargement. -/
theorem intersectionCohomologyIso_natural (n : ℕ) :
    homologyMap (supportMap p V (K ∩ L) (K' ∩ L') (Set.inter_subset_inter hKK' hLL')) n ≫
        (intersectionCohomologyIso p V K' L' hK' hL' n).hom =
      (intersectionCohomologyIso p V K L hK hL n).hom ≫
        homologyMap (fixedKernelMap p V K L K' L' hKK' hLL').τ₁ n := by
  change homologyMap _ n ≫ homologyMap _ n = homologyMap _ n ≫ homologyMap _ n
  erw [← homologyMap_comp, ← homologyMap_comp, intersectionComparison_natural p V K L K' L' hKK' hLL']
  rfl

/-- The inverse actual intersection comparison is natural under support enlargement. -/
theorem intersectionCohomologyIso_inv_natural (n : ℕ) :
    (intersectionCohomologyIso p V K L hK hL n).inv ≫
        homologyMap (supportMap p V (K ∩ L) (K' ∩ L') (Set.inter_subset_inter hKK' hLL')) n =
      homologyMap (fixedKernelMap p V K L K' L' hKK' hLL').τ₁ n ≫
        (intersectionCohomologyIso p V K' L' hK' hL' n).inv := by
  apply (cancel_mono (intersectionCohomologyIso p V K' L' hK' hL' n).hom).mp
  erw [Category.assoc, intersectionCohomologyIso_natural p V K L K' L' hK hL hK' hL' hKK' hLL' n,
    Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The genuine connecting morphism is natural for simultaneous enlargement of the two supports. -/
theorem fixedConnecting_natural (n : ℕ) :
    fixedConnecting p V K L hK hL n ≫
        homologyMap (supportMap p V (K ∩ L) (K' ∩ L') (Set.inter_subset_inter hKK' hLL')) (n+1) =
      homologyMap (supportMap p V (K ∪ L) (K' ∪ L') (Set.union_subset_union hKK' hLL')) n ≫
        fixedConnecting p V K' L' hK' hL' n := by
  unfold fixedConnecting
  erw [Category.assoc, intersectionCohomologyIso_inv_natural p V K L K' L' hK hL hK' hL' hKK' hLL' (n+1),
    ← Category.assoc]
  erw [HomologySequence.δ_naturality (fixedKernelMap p V K L K' L' hKK' hLL')
    (fixedKernelSequence_shortExact p V K L) (fixedKernelSequence_shortExact p V K' L') n (n+1) rfl]
  rfl

/-- The actual signed diagonal on support cohomology is natural for support enlargement. -/
theorem fixedDiagonal_natural (n : ℕ) :
    homologyMap (supportMap p V (K ∩ L) (K' ∩ L') (Set.inter_subset_inter hKK' hLL')) n ≫
        fixedDiagonal p V K' L' n =
      fixedDiagonal p V K L n ≫
        biprod.map (homologyMap (supportMap p V K K' hKK') n) (homologyMap (supportMap p V L L' hLL') n) := by
  apply biprod.hom_ext
  · simp only [fixedDiagonal, Category.assoc, biprod.lift_fst, biprod.map_fst,
      biprod.lift_fst_assoc, ← homologyMap_comp, supportMap_comp]
  · simp only [fixedDiagonal, Category.assoc, biprod.lift_snd, biprod.map_snd,
      biprod.lift_snd_assoc, Preadditive.comp_neg, Preadditive.neg_comp, ← homologyMap_comp, supportMap_comp]

/-- The actual sum on support cohomology is natural for support enlargement. -/
theorem fixedSum_natural (n : ℕ) :
    fixedSum p V K L n ≫ homologyMap (supportMap p V (K ∪ L) (K' ∪ L') (Set.union_subset_union hKK' hLL')) n =
      biprod.map (homologyMap (supportMap p V K K' hKK') n) (homologyMap (supportMap p V L L' hLL') n) ≫
        fixedSum p V K' L' n := by
  apply biprod.hom_ext'
  · simp only [fixedSum, biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc,
      ← homologyMap_comp, supportMap_comp]
  · simp only [fixedSum, biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc,
      ← homologyMap_comp, supportMap_comp]

end TernaryPoly.SingularLocalCompactMV
