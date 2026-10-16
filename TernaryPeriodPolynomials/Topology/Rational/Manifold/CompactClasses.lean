module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactHomology

@[expose] public section


noncomputable section
namespace TernaryPoly.RationalManifoldCompact
open CategoryTheory Limits HomologicalComplex RationalLocalOrientation RationalLocalChartHomology
variable {X H : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace H] [ChartedSpace H X]

/-- An actual locally represented homological orientation gives a unique fundamental class supported on each compact subset. -/
theorem manifold_compact_existsUnique (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (o : Orientation (n+2) X) (K : Set X) (hK : IsCompact K) :
    ∃! c : (supportChains K).homology (n+2), ∀ (x : X) (hx : x ∈ K),
      homologyMap (supportPointMap K x hx) (n+2) c = o.generator x := by
  obtain ⟨c, hc⟩ := (manifold_compact_data n e o.generator o.locallyRepresented K hK).exists_class
  refine ⟨c, hc, ?_⟩
  intro a ha
  apply manifold_compact_detect n e K hK a c
  intro x hx
  rw [ha x hx, hc x hx]

/-- The genuine compact-subset fundamental class selected by the given homological orientation. -/
def compactFundamentalClass (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (o : Orientation (n+2) X) (K : Set X) (hK : IsCompact K) : (supportChains K).homology (n+2) :=
  (manifold_compact_existsUnique n e o K hK).choose

/-- Every point restriction of the actual compact-subset class is exactly the supplied orientation generator. -/
theorem compactFundamentalClass_at_point (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (o : Orientation (n+2) X) (K : Set X) (hK : IsCompact K) (x : X) (hx : x ∈ K) :
    homologyMap (supportPointMap K x hx) (n+2) (compactFundamentalClass n e o K hK) = o.generator x :=
  (manifold_compact_existsUnique n e o K hK).choose_spec.1 x hx

/-- The literal point restrictions uniquely characterize the compact-subset fundamental class. -/
theorem compactFundamentalClass_unique (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (o : Orientation (n+2) X) (K : Set X) (hK : IsCompact K) (c : (supportChains K).homology (n+2))
    (hc : ∀ (x : X) (hx : x ∈ K), homologyMap (supportPointMap K x hx) (n+2) c = o.generator x) :
    c = compactFundamentalClass n e o K hK :=
  (manifold_compact_existsUnique n e o K hK).choose_spec.2 c hc

/-- Literal restriction to a smaller compact support preserves the actual fundamental class. -/
theorem compactFundamentalClass_restriction (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (o : Orientation (n+2) X) (K L : Set X) (hK : IsCompact K) (hL : IsCompact L) (hLK : L ⊆ K) :
    homologyMap (supportRestriction K L hLK) (n+2) (compactFundamentalClass n e o K hK) =
      compactFundamentalClass n e o L hL := by
  apply compactFundamentalClass_unique n e o L hL
  intro x hx
  rw [restriction_point_apply]
  exact compactFundamentalClass_at_point n e o K hK x (hLK hx)

/-- The actual fundamental class of a nonempty compact support is nonzero. -/
theorem compactFundamentalClass_ne_zero (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (o : Orientation (n+2) X) (K : Set X) (hK : IsCompact K) (hne : K.Nonempty) :
    compactFundamentalClass n e o K hK ≠ 0 := by
  obtain ⟨x,hx⟩ := hne
  intro h
  have hh := compactFundamentalClass_at_point n e o K hK x hx
  rw [h, map_zero] at hh
  exact o.nonzero x hh.symm

/-- The actual fundamental class of the empty support is zero. -/
theorem compactFundamentalClass_empty (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (o : Orientation (n+2) X) : compactFundamentalClass n e o ∅ isCompact_empty = 0 :=
  (ModuleCat.subsingleton_of_isZero (empty_support_homology_isZero (X := X) (n+2))).elim _ _

end TernaryPoly.RationalManifoldCompact
