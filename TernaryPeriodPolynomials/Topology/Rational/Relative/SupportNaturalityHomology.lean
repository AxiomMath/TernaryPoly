module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportLES
public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportNaturalityComparison

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalRelativeSupport
open CategoryTheory Limits HomologicalComplex ContractibleSingularHomology
open RationalRelativeSingular TopologicalSpace

variable {X : Type} [TopologicalSpace X]

/-- The first literal homology comparison is natural under support inclusions. -/
theorem firstHomology_natural (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') (k : ℕ) :
    homologyMap (quotientChainMap U V U' V' hU hV).τ₁ k ≫ (firstHomologyIso U' V' k).hom =
      (firstHomologyIso U V k).hom ≫ homologyMap
        (relativeInclusion (U ∩ V) (U' ∩ V') (Set.inter_subset_inter hU hV)) k := by
  change homologyMap _ _ ≫ homologyMap _ _ = homologyMap _ _ ≫ homologyMap _ _
  rw [← homologyMap_comp, ← homologyMap_comp, firstComparison_natural]

/-- The actual excision comparison on homology is natural under inclusions of open exclusions. -/
theorem thirdHomology_natural (U V U' V' : Opens X) (hU : (U : Set X) ⊆ U')
    (hV : (V : Set X) ⊆ V') (k : ℕ) :
    homologyMap (quotientChainMap (U : Set X) (V : Set X) (U' : Set X) (V' : Set X) hU hV).τ₃ k ≫
      (thirdHomologyIso U' V' k).hom = (thirdHomologyIso U V k).hom ≫ homologyMap
        (relativeInclusion ((U : Set X) ∪ V) ((U' : Set X) ∪ V') (Set.union_subset_union hU hV)) k := by
  change homologyMap _ _ ≫ homologyMap _ _ = homologyMap _ _ ≫ homologyMap _ _
  erw [← homologyMap_comp, ← homologyMap_comp, thirdComparison_natural (U : Set X) (V : Set X) (U' : Set X) (V' : Set X) hU hV]
  rfl

/-- The literal unsigned restriction pair is natural under inclusions of exclusions. -/
theorem restrictionPair_natural (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') (k : ℕ) :
    homologyRestrictionPair U V k ≫ biprod.map (homologyMap (relativeInclusion U U' hU) k)
      (homologyMap (relativeInclusion V V' hV) k) =
    homologyMap (relativeInclusion (U ∩ V) (U' ∩ V') (Set.inter_subset_inter hU hV)) k ≫
      homologyRestrictionPair U' V' k := by
  apply biprod.hom_ext <;>
    simp only [homologyRestrictionPair, Category.assoc, biprod.map_fst, biprod.map_snd,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_fst, biprod.lift_snd,
      ← homologyMap_comp, relativeInclusion_comp]

/-- The literal difference map is natural under inclusions of exclusions. -/
theorem restrictionDifference_natural (U V U' V' : Set X) (hU : U ⊆ U') (hV : V ⊆ V') (k : ℕ) :
    biprod.map (homologyMap (relativeInclusion U U' hU) k) (homologyMap (relativeInclusion V V' hV) k) ≫
      homologyRestrictionDifference U' V' k =
    homologyRestrictionDifference U V k ≫
      homologyMap (relativeInclusion (U ∪ V) (U' ∪ V') (Set.union_subset_union hU hV)) k := by
  apply biprod.hom_ext' <;>
    simp only [homologyRestrictionDifference, biprod.inl_map_assoc, biprod.inr_map_assoc,
      biprod.inl_desc_assoc, biprod.inr_desc_assoc, biprod.inl_desc, biprod.inr_desc,
      Preadditive.comp_neg, Preadditive.neg_comp, ← homologyMap_comp, relativeInclusion_comp]

/-- The genuine relative-support connecting map is natural under inclusions of both closed supports. -/
theorem supportConnecting_natural (U V U' V' : Opens X) (hU : (U : Set X) ⊆ U')
    (hV : (V : Set X) ⊆ V') (k : ℕ) :
    supportConnecting U V k ≫ homologyMap
      (relativeInclusion ((U : Set X) ∩ V) ((U' : Set X) ∩ V') (Set.inter_subset_inter hU hV)) k =
    homologyMap (relativeInclusion ((U : Set X) ∪ V) ((U' : Set X) ∪ V')
      (Set.union_subset_union hU hV)) (k+1) ≫ supportConnecting U' V' k := by
  apply (cancel_epi (thirdHomologyIso U V (k+1)).hom).mp
  rw [← Category.assoc, ← supportConnecting_comm, Category.assoc, ← firstHomology_natural (U : Set X) (V : Set X) (U' : Set X) (V' : Set X) hU hV k,
    ← Category.assoc]
  erw [HomologicalComplex.HomologySequence.δ_naturality
    (quotientChainMap (U : Set X) (V : Set X) (U' : Set X) (V' : Set X) hU hV)
    (quotientChainRow_shortExact (U : Set X) (V : Set X))
    (quotientChainRow_shortExact (U' : Set X) (V' : Set X)) (k+1) k rfl]
  rw [Category.assoc, supportConnecting_comm, ← Category.assoc, thirdHomology_natural U V U' V' hU hV (k+1), Category.assoc]

end TernaryPoly.RationalRelativeSupport
