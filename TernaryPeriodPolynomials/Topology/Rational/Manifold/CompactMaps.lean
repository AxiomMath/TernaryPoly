module

public import TernaryPeriodPolynomials.Topology.Rational.Relative.SupportCompactGluing
public import TernaryPeriodPolynomials.Topology.Rational.Local.OrientationSupport

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalManifoldCompact
open CategoryTheory Limits HomologicalComplex RationalLocalOrientation RationalRelativeSingular

variable {X : Type} [TopologicalSpace X]

/-- Actual chains relative to the complement of a support. -/
abbrev supportChains (K : Set X) := relativeChains Kᶜ

/-- The support Mayer–Vietoris restriction is the existing literal ambient pair map. -/
theorem mv_restriction (K L : Set X) (h : L ⊆ K) (k : ℕ) :
    RationalRelativeSupport.supportRestriction L K h k =
      homologyMap (supportRestriction K L h) k := rfl

/-- The first component of the genuine Mayer–Vietoris pair is literal restriction. -/
theorem closedPair_fst (A B : Set X) (k : ℕ) :
    RationalRelativeSupport.closedPair A B k ≫ biprod.fst =
      homologyMap (supportRestriction (A ∪ B) A Set.subset_union_left) k := by
  unfold RationalRelativeSupport.closedPair
  erw [biprod.lift_fst]
  rfl

/-- The second component of the genuine Mayer–Vietoris pair is literal restriction. -/
theorem closedPair_snd (A B : Set X) (k : ℕ) :
    RationalRelativeSupport.closedPair A B k ≫ biprod.snd =
      homologyMap (supportRestriction (A ∪ B) B Set.subset_union_right) k := by
  unfold RationalRelativeSupport.closedPair
  erw [biprod.lift_snd]
  rfl

/-- Actual restriction to a point factors through every intermediate support containing it. -/
theorem restriction_point_apply (K L : Set X) (h : L ⊆ K) (x : X) (hx : x ∈ L)
    (k : ℕ) (c : (supportChains K).homology k) :
    homologyMap (supportPointMap L x hx) k (homologyMap (supportRestriction K L h) k c) =
      homologyMap (supportPointMap K x (h hx)) k c := by
  change (homologyMap (supportRestriction K L h) k ≫ homologyMap (supportPointMap L x hx) k) c = _
  rw [← homologyMap_comp, supportRestriction_point]

variable [T2Space X]

/-- If the preceding intersection group vanishes, the two actual support restrictions
jointly detect every union-supported class. -/
theorem union_restrictions_injective (A B : Set X) (hA : IsCompact A) (hB : IsCompact B)
    (k : ℕ) (hnext : IsZero ((supportChains (A ∩ B)).homology (k+1)))
    (c e : (supportChains (A ∪ B)).homology k)
    (hleft : homologyMap (supportRestriction (A ∪ B) A Set.subset_union_left) k c =
      homologyMap (supportRestriction (A ∪ B) A Set.subset_union_left) k e)
    (hright : homologyMap (supportRestriction (A ∪ B) B Set.subset_union_right) k c =
      homologyMap (supportRestriction (A ∪ B) B Set.subset_union_right) k e) : c = e := by
  apply (RationalRelativeSupport.closed_injective_iff_connecting_zero A B hA.isClosed hB.isClosed k).mpr
    (hnext.eq_of_src _ _)
  apply RationalRelativeSupport.module_biprod_element_ext
  · change (RationalRelativeSupport.closedPair A B k ≫ biprod.fst) c =
      (RationalRelativeSupport.closedPair A B k ≫ biprod.fst) e
    erw [closedPair_fst]
    exact hleft
  · change (RationalRelativeSupport.closedPair A B k ≫ biprod.snd) c =
      (RationalRelativeSupport.closedPair A B k ≫ biprod.snd) e
    erw [closedPair_snd]
    exact hright

end TernaryPoly.RationalManifoldCompact
