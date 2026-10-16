module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactMaps

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalManifoldCompact
open CategoryTheory Limits HomologicalComplex RationalLocalOrientation RationalRelativeSingular

variable {X : Type} [TopologicalSpace X] [T2Space X]

/-- Compatible actual classes on two compact supports admit a union-supported class
whose two literal restrictions are the prescribed classes. -/
theorem glue_classes (A B : Set X) (hA : IsCompact A) (hB : IsCompact B) (k : ℕ)
    (a : (supportChains A).homology k) (b : (supportChains B).homology k)
    (hab : homologyMap (supportRestriction A (A ∩ B) Set.inter_subset_left) k a =
      homologyMap (supportRestriction B (A ∩ B) Set.inter_subset_right) k b) :
    ∃ c : (supportChains (A ∪ B)).homology k,
      homologyMap (supportRestriction (A ∪ B) A Set.subset_union_left) k c = a ∧
      homologyMap (supportRestriction (A ∪ B) B Set.subset_union_right) k c = b := by
  let M := RationalRelativeSupport.supportHomology A k
  let N := RationalRelativeSupport.supportHomology B k
  let z : (M ⊞ N : ModuleCat ℚ) := (biprod.inl : M ⟶ M ⊞ N) a + (biprod.inr : N ⟶ M ⊞ N) b
  have hz : RationalRelativeSupport.closedDifference A B k z = 0 := by
    dsimp only [z]
    erw [map_add]
    change (biprod.inl ≫ RationalRelativeSupport.closedDifference A B k) a +
      (biprod.inr ≫ RationalRelativeSupport.closedDifference A B k) b = 0
    erw [RationalRelativeSupport.closedDifference, biprod.inl_desc, biprod.inr_desc,
      mv_restriction, mv_restriction]
    change _ + -_ = 0
    erw [hab]
    exact add_neg_cancel _
  obtain ⟨c, hc⟩ := (RationalRelativeSupport.closed_compatible_iff_glues A B hA.isClosed hB.isClosed k z).mp hz
  refine ⟨c, ?_, ?_⟩
  · have he := congrArg (fun v => (biprod.fst : M ⊞ N ⟶ M) v) hc
    change (RationalRelativeSupport.closedPair A B k ≫ biprod.fst) c = _ at he
    rw [closedPair_fst] at he
    refine he.trans ?_
    dsimp only [z]
    erw [map_add]
    change (biprod.inl ≫ biprod.fst : M ⟶ M) a + (biprod.inr ≫ biprod.fst : N ⟶ M) b = a
    rw [biprod.inl_fst, biprod.inr_fst]
    change a + 0 = a
    exact add_zero a
  · have he := congrArg (fun v => (biprod.snd : M ⊞ N ⟶ N) v) hc
    change (RationalRelativeSupport.closedPair A B k ≫ biprod.snd) c = _ at he
    rw [closedPair_snd] at he
    refine he.trans ?_
    dsimp only [z]
    erw [map_add]
    change (biprod.inl ≫ biprod.snd : M ⟶ N) a + (biprod.inr ≫ biprod.snd : N ⟶ N) b = b
    rw [biprod.inl_snd, biprod.inr_snd]
    change 0 + b = b
    exact zero_add b

/-- Upper-degree vanishing passes to a compact union when the two piece groups and
the preceding intersection group vanish. -/
theorem union_isZero (A B : Set X) (hA : IsCompact A) (hB : IsCompact B) (k : ℕ)
    (ha : IsZero ((supportChains A).homology k)) (hb : IsZero ((supportChains B).homology k))
    (hab : IsZero ((supportChains (A ∩ B)).homology (k+1))) :
    IsZero ((supportChains (A ∪ B)).homology k) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun c e => union_restrictions_injective A B hA hB k hab c e ?_ ?_⟩
  · exact (ModuleCat.subsingleton_of_isZero ha).elim _ _
  · exact (ModuleCat.subsingleton_of_isZero hb).elim _ _

end TernaryPoly.RationalManifoldCompact
