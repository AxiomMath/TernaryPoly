module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactEmpty

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalManifoldCompact
open CategoryTheory Limits HomologicalComplex RationalLocalOrientation RationalLocalChartHomology
variable {X : Type} [TopologicalSpace X]

/-- The actual compact-support conclusions to be established simultaneously. The local family is data, and all class statements concern literal support-to-point maps. -/
structure LocalFundamentalData (d : ℕ) (g : ∀ x : X, (localChains x).homology d) (K : Set X) : Prop where
  compact : IsCompact K
  above : ∀ k, d < k → IsZero ((supportChains K).homology k)
  detect : ∀ c e : (supportChains K).homology d,
    (∀ (x : X) (hx : x ∈ K), homologyMap (supportPointMap K x hx) d c =
      homologyMap (supportPointMap K x hx) d e) → c = e
  exists_class : ∃ c : (supportChains K).homology d,
    ∀ (x : X) (hx : x ∈ K), homologyMap (supportPointMap K x hx) d c = g x

/-- Empty support satisfies all compact-support conclusions with its zero class. -/
theorem empty_data (d : ℕ) (g : ∀ x : X, (localChains x).homology d) :
    LocalFundamentalData d g (∅ : Set X) where
  compact := isCompact_empty
  above k _ := empty_support_homology_isZero k
  detect c e _ := (ModuleCat.subsingleton_of_isZero (empty_support_homology_isZero d)).elim c e
  exists_class := ⟨0, fun _ hx => False.elim hx⟩

variable [T2Space X]

/-- The simultaneous conclusions pass to a compact union whenever both pieces and their intersection have them. -/
theorem union_data (d : ℕ) (g : ∀ x : X, (localChains x).homology d) (A B : Set X)
    (hA : LocalFundamentalData d g A) (hB : LocalFundamentalData d g B)
    (hAB : LocalFundamentalData d g (A ∩ B)) : LocalFundamentalData d g (A ∪ B) := by
  refine ⟨hA.compact.union hB.compact, ?_, ?_, ?_⟩
  · intro k hk
    exact union_isZero A B hA.compact hB.compact k (hA.above k hk) (hB.above k hk)
      (hAB.above (k+1) (by omega))
  · intro c e hce
    apply union_restrictions_injective A B hA.compact hB.compact d
      (hAB.above (d+1) (by omega)) c e
    · apply hA.detect
      intro x hx
      rw [restriction_point_apply, restriction_point_apply]
      exact hce x (Set.mem_union_left B hx)
    · apply hB.detect
      intro x hx
      rw [restriction_point_apply, restriction_point_apply]
      exact hce x (Set.mem_union_right A hx)
  · obtain ⟨a, ha⟩ := hA.exists_class
    obtain ⟨b, hb⟩ := hB.exists_class
    have hab : homologyMap (supportRestriction A (A ∩ B) Set.inter_subset_left) d a =
        homologyMap (supportRestriction B (A ∩ B) Set.inter_subset_right) d b := by
      apply hAB.detect
      intro x hx
      rw [restriction_point_apply, restriction_point_apply, ha x hx.1, hb x hx.2]
    obtain ⟨c, hcA, hcB⟩ := glue_classes A B hA.compact hB.compact d a b hab
    refine ⟨c, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · rw [← restriction_point_apply (A ∪ B) A Set.subset_union_left x hx d c, hcA]
      exact ha x hx
    · rw [← restriction_point_apply (A ∪ B) B Set.subset_union_right x hx d c, hcB]
      exact hb x hx

end TernaryPoly.RationalManifoldCompact
