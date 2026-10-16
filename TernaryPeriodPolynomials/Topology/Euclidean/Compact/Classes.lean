module

public import TernaryPeriodPolynomials.Topology.Euclidean.Compact.ClassesDetection

@[expose] public section


noncomputable section
namespace TernaryPoly.EuclideanCompactClasses
open CategoryTheory Limits HomologicalComplex Set
open EuclideanFiniteConvex EuclideanConvexLocal EuclideanLocalHomology

variable (n : ℕ)
local notation "E" => EuclideanSpace ℝ (Fin (n+2))

/-- Every compact Euclidean support has a unique actual relative class with the prescribed
canonical local generator at all of its points. -/
theorem existsUnique_compact_fundamental_class (K : Set E) (hK : IsCompact K) :
    ∃! c : (supportChains K).homology (n+2), ∀ (x : E) (hx : x ∈ K),
      homologyMap (pointMap K x hx) (n+2) c = localGenerator n x := by
  obtain ⟨c,hc⟩ := exists_compact_fundamental_class n K hK
  refine ⟨c,hc,?_⟩
  intro e he
  apply compact_class_detect n K hK e c
  intro x hx
  rw [he x hx,hc x hx]

/-- The actual canonical relative fundamental class of an arbitrary compact Euclidean subset. -/
def compactGenerator (K : Set E) (hK : IsCompact K) : (supportChains K).homology (n+2) :=
  (existsUnique_compact_fundamental_class n K hK).choose

/-- Its literal restriction to every support point is the fixed Euclidean generator. -/
theorem compactGenerator_at_point (K : Set E) (hK : IsCompact K) (x : E) (hx : x ∈ K) :
    homologyMap (pointMap K x hx) (n+2) (compactGenerator n K hK) = localGenerator n x :=
  (existsUnique_compact_fundamental_class n K hK).choose_spec.1 x hx

/-- The point values characterize the compact-subset fundamental class uniquely. -/
theorem compactGenerator_unique (K : Set E) (hK : IsCompact K)
    (c : (supportChains K).homology (n+2))
    (hc : ∀ (x : E) (hx : x ∈ K), homologyMap (pointMap K x hx) (n+2) c = localGenerator n x) :
    c = compactGenerator n K hK :=
  (existsUnique_compact_fundamental_class n K hK).choose_spec.2 c hc

/-- Actual support restriction preserves canonical classes for any compact inclusion. -/
theorem compactGenerator_restriction (K L : Set E) (hK : IsCompact K) (hL : IsCompact L)
    (hLK : L ⊆ K) : homologyMap (supportRestriction K L hLK) (n+2) (compactGenerator n K hK) =
      compactGenerator n L hL := by
  apply compactGenerator_unique n L hL
  intro x hx
  rw [restriction_point_apply]
  exact compactGenerator_at_point n K hK x (hLK hx)

/-- The compact-subset fundamental class is nonzero whenever the support is nonempty. -/
theorem compactGenerator_ne_zero (K : Set E) (hK : IsCompact K) (hne : K.Nonempty) :
    compactGenerator n K hK ≠ 0 := by
  obtain ⟨x,hx⟩ := hne
  intro h
  have hh := compactGenerator_at_point n K hK x hx
  rw [h,map_zero] at hh
  exact localGenerator_ne_zero n x hh.symm

/-- Empty support has the zero compact-subset fundamental class. -/
theorem compactGenerator_empty : compactGenerator n ∅ isCompact_empty = 0 := by
  exact (ModuleCat.subsingleton_of_isZero (emptySupportHomology_isZero (d := n+2) (n+2))).elim _ _

end TernaryPoly.EuclideanCompactClasses
