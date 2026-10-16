module

public import TernaryPeriodPolynomials.Topology.Euclidean.Finite.ConvexGluing

@[expose] public section

noncomputable section
namespace TernaryPoly.EuclideanFiniteConvex
open CategoryTheory Limits HomologicalComplex EuclideanConvexLocal EuclideanLocalHomology

variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))

/-- The three simultaneous finite-union conclusions, with compactness retained for
Mayer–Vietoris. No lower-degree vanishing is asserted. -/
structure LocalFundamentalData (K : Set E) : Prop where
  compact : IsCompact K
  above : ∀ k, n+2 < k → IsZero ((supportChains K).homology k)
  detect : ∀ (c e : (supportChains K).homology (n+2)),
    (∀ (x : E) (hx : x ∈ K), homologyMap (pointMap K x hx) (n+2) c =
      homologyMap (pointMap K x hx) (n+2) e) → c = e
  exists_class : ∃ c : (supportChains K).homology (n+2),
    ∀ (x : E) (hx : x ∈ K), homologyMap (pointMap K x hx) (n+2) c = localGenerator n x

/-- Empty support has the unique zero class, and every supported homology group vanishes. -/
theorem empty_data : LocalFundamentalData n (∅ : Set E) where
  compact := isCompact_empty
  above k _ := emptySupportHomology_isZero k
  detect c e _ := (ModuleCat.subsingleton_of_isZero (emptySupportHomology_isZero (d := n+2) (n+2))).elim c e
  exists_class := ⟨0, fun _ hx => False.elim hx⟩

/-- A single compact convex support satisfies all simultaneous conclusions, including
empty, singleton, and lower-dimensional convex supports. -/
theorem convex_data (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K) :
    LocalFundamentalData n K := by
  rcases Set.eq_empty_or_nonempty K with rfl | hne
  · exact empty_data n
  refine ⟨hK, fun k hk => supportHomology_isZero_of_ne n k K hK hconv (by omega), ?_, ?_⟩
  · intro c e hce
    apply (ModuleCat.mono_iff_injective (pointHomologyIso K hK hconv hne.some hne.some_mem (n+2)).hom).mp
      inferInstance
    exact hce hne.some hne.some_mem
  · exact ⟨convexGenerator n K hK hconv hne, convexGenerator_at_point n K hK hconv hne⟩

/-- The simultaneous conclusions pass to a compact union when they hold on both pieces
and their intersection. -/
theorem union_data (A B : Set E) (hA : LocalFundamentalData n A)
    (hB : LocalFundamentalData n B) (hAB : LocalFundamentalData n (A ∩ B)) :
    LocalFundamentalData n (A ∪ B) := by
  refine ⟨hA.compact.union hB.compact, ?_, ?_, ?_⟩
  · intro k hk
    exact union_isZero A B hA.compact hB.compact k (hA.above k hk) (hB.above k hk)
      (hAB.above (k+1) (by omega))
  · intro c e hce
    apply union_restrictions_injective A B hA.compact hB.compact (n+2)
      (hAB.above (n+2+1) (by omega)) c e
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
    have hab : homologyMap (supportRestriction A (A ∩ B) Set.inter_subset_left) (n+2) a =
        homologyMap (supportRestriction B (A ∩ B) Set.inter_subset_right) (n+2) b := by
      apply hAB.detect
      intro x hx
      rw [restriction_point_apply, restriction_point_apply, ha x hx.1, hb x hx.2]
    obtain ⟨c, hcA, hcB⟩ := glue_classes A B hA.compact hB.compact (n+2) a b hab
    refine ⟨c, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · rw [← restriction_point_apply (A ∪ B) A Set.subset_union_left x hx (n+2) c, hcA]
      exact ha x hx
    · rw [← restriction_point_apply (A ∪ B) B Set.subset_union_right x hx (n+2) c, hcB]
      exact hb x hx

end TernaryPoly.EuclideanFiniteConvex
