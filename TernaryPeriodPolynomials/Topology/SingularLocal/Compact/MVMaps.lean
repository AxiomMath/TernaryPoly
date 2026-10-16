module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.Cochains
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits HomologicalComplex SingularLocalSupport

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- The genuine signed fixed-support cochain map from intersection support to the two supports. -/
def supportDiagonal (K L : Set B) :
    supportCochains p V (K ∩ L) ⟶ supportCochains p V K ⊞ supportCochains p V L :=
  biprod.lift (supportMap p V (K ∩ L) K Set.inter_subset_left)
    (-supportMap p V (K ∩ L) L Set.inter_subset_right)

/-- The genuine sum of support enlargement maps into union support. -/
def supportSum (K L : Set B) :
    supportCochains p V K ⊞ supportCochains p V L ⟶ supportCochains p V (K ∪ L) :=
  biprod.desc (supportMap p V K (K ∪ L) Set.subset_union_left)
    (supportMap p V L (K ∪ L) Set.subset_union_right)

/-- The fixed-support signed diagonal and sum compose to zero as actual cochain maps. -/
theorem supportDiagonal_sum (K L : Set B) : supportDiagonal p V K L ≫ supportSum p V K L = 0 := by
  rw [supportDiagonal,supportSum,biprod.lift_desc,Preadditive.neg_comp,
    supportMap_comp,supportMap_comp,add_neg_cancel]

/-- The exact kernel short complex of the actual fixed-support sum. -/
def fixedKernelSequence (K L : Set B) : ShortComplex (CochainComplex (ModuleCat.{0} ℚ) ℕ) :=
  ShortComplex.kernelSequence (supportSum p V K L)

/-- Exactness at the two actual support-cochain complexes is a genuine kernel property. -/
theorem fixedKernelSequence_exact (K L : Set B) : (fixedKernelSequence p V K L).Exact :=
  ShortComplex.kernelSequence_exact _

/-- Actual intersection-support cochains map into the kernel by the prescribed signed diagonal. -/
def intersectionComparison (K L : Set B) :
    supportCochains p V (K ∩ L) ⟶ kernel (supportSum p V K L) :=
  kernel.lift (supportSum p V K L) (supportDiagonal p V K L) (supportDiagonal_sum p V K L)

/-- The comparison retains the literal signed support-enlargement maps. -/
theorem intersectionComparison_inclusion (K L : Set B) :
    intersectionComparison p V K L ≫ kernel.ι (supportSum p V K L) = supportDiagonal p V K L :=
  kernel.lift_ι _ _ _

/-- The two genuine support enlargements form the middle map of the fixed-support ladder. -/
def supportPairMap (K L K' L' : Set B) (hK : K ⊆ K') (hL : L ⊆ L') :
    supportCochains p V K ⊞ supportCochains p V L ⟶ supportCochains p V K' ⊞ supportCochains p V L' :=
  biprod.map (supportMap p V K K' hK) (supportMap p V L L' hL)

/-- Actual support enlargement commutes with the actual sum map. -/
theorem supportSum_natural (K L K' L' : Set B) (hK : K ⊆ K') (hL : L ⊆ L') :
    supportSum p V K L ≫ supportMap p V (K ∪ L) (K' ∪ L') (Set.union_subset_union hK hL) =
      supportPairMap p V K L K' L' hK hL ≫ supportSum p V K' L' := by
  apply biprod.hom_ext'
  · simp only [supportSum,supportPairMap,biprod.inl_desc_assoc,biprod.inl_map_assoc,
      biprod.inl_desc]
    rw [supportMap_comp,supportMap_comp]
  · simp only [supportSum,supportPairMap,biprod.inr_desc_assoc,biprod.inr_map_assoc,
      biprod.inr_desc]
    rw [supportMap_comp,supportMap_comp]

/-- Actual support enlargement commutes with the prescribed signed intersection map. -/
theorem supportDiagonal_natural (K L K' L' : Set B) (hK : K ⊆ K') (hL : L ⊆ L') :
    supportMap p V (K ∩ L) (K' ∩ L') (Set.inter_subset_inter hK hL) ≫ supportDiagonal p V K' L' =
      supportDiagonal p V K L ≫ supportPairMap p V K L K' L' hK hL := by
  apply biprod.hom_ext
  · simp only [supportDiagonal,supportPairMap,Category.assoc,biprod.lift_fst]
    rw [biprod.map_fst,← Category.assoc,biprod.lift_fst,supportMap_comp,supportMap_comp]
  · simp only [supportDiagonal,supportPairMap,Category.assoc,biprod.lift_snd]
    rw [biprod.map_snd,← Category.assoc,biprod.lift_snd,Preadditive.comp_neg,
      Preadditive.neg_comp,supportMap_comp,supportMap_comp]

/-- The genuine map of fixed-support kernel sequences. -/
def fixedKernelMap (K L K' L' : Set B) (hK : K ⊆ K') (hL : L ⊆ L') :
    fixedKernelSequence p V K L ⟶ fixedKernelSequence p V K' L' where
  τ₁ := kernel.map (supportSum p V K L) (supportSum p V K' L')
    (supportPairMap p V K L K' L' hK hL)
    (supportMap p V (K ∪ L) (K' ∪ L') (Set.union_subset_union hK hL))
    (supportSum_natural p V K L K' L' hK hL)
  τ₂ := supportPairMap p V K L K' L' hK hL
  τ₃ := supportMap p V (K ∪ L) (K' ∪ L') (Set.union_subset_union hK hL)
  comm₁₂ := kernel.lift_ι _ _ _
  comm₂₃ := (supportSum_natural p V K L K' L' hK hL).symm

/-- The genuine intersection comparison is natural under enlargement of the two supports. -/
theorem intersectionComparison_natural (K L K' L' : Set B) (hK : K ⊆ K') (hL : L ⊆ L') :
    supportMap p V (K ∩ L) (K' ∩ L') (Set.inter_subset_inter hK hL) ≫ intersectionComparison p V K' L' =
      intersectionComparison p V K L ≫ (fixedKernelMap p V K L K' L' hK hL).τ₁ := by
  change supportMap p V (K ∩ L) (K' ∩ L') (Set.inter_subset_inter hK hL) ≫ intersectionComparison p V K' L' =
    intersectionComparison p V K L ≫ kernel.map (supportSum p V K L) (supportSum p V K' L')
      (supportPairMap p V K L K' L' hK hL)
      (supportMap p V (K ∪ L) (K' ∪ L') (Set.union_subset_union hK hL))
      (supportSum_natural p V K L K' L' hK hL)
  apply (cancel_mono (kernel.ι (supportSum p V K' L'))).mp
  simp only [Category.assoc,kernel.map,kernel.lift_ι,intersectionComparison_inclusion]
  rw [← Category.assoc,intersectionComparison_inclusion]
  exact supportDiagonal_natural p V K L K' L' hK hL

end TernaryPoly.SingularLocalCompactMV
