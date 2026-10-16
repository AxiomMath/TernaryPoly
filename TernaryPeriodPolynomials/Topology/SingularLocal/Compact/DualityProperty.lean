module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityNested
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityEmpty
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVGluing
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVVanishing

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactDuality
open CategoryTheory Limits TopologicalSpace
open SingularLocalSupport SingularLocalCompactCap RationalLocalOrientation

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))

/-- The induction conclusion includes literal compact-cap duality for every genuine orientation
and the upper-degree compact-cohomology vanishing required at homological degree zero. -/
def Duality : Prop :=
  (∀ (o : Orientation (n+2) B) (a b : ℕ) (hab : a+b = n+2),
    IsIso (compactCapMap p V n e o a b hab)) ∧
  (∀ a : ℕ, n+2 < a → IsZero (compactCohomology p V a))

/-- The actual empty-base duality property has no orientation or coefficient restriction. -/
theorem duality_empty [IsEmpty B] : Duality p V n e :=
  ⟨fun o a b hab => empty_compactCap_isIso p V n e o a b hab,
    fun a _ => empty_compactCohomology_isZero p V a⟩

variable {E' B' : TopCat.{0}} [MulAction G E'] [ContinuousConstSMul G E']
  (p' : E' ⟶ B') [hp' : Fact (IsQuotientCoveringMap p' G)]
  [T2Space B'] {H' : Type} [TopologicalSpace H'] [ChartedSpace H' B']
  (e' : H' ≃ₜ EuclideanSpace ℝ (Fin (n+2)))

/-- Genuine equivariant covering homeomorphisms preserve the complete induction property.
The source orientation is the actual pullback of each desired target orientation. -/
theorem duality_homeomorph (h : CoverHomeomorph (G := G) p p')
    (hd : Duality p V n e) : Duality p' V n e' := by
  let : IsCancelSMul G E := hp.out.isCancelSMul
  let : IsCancelSMul G E' := hp'.out.isCancelSMul
  constructor
  · intro o a b hab
    have := hd.1 (Orientation.pullback h.base (n+2) o) a b hab
    exact coveringCompactCapMap_isIso h V n e e' _ o
      (SingularLocalCapHomeomorph.pullbackOrientation_compatible h.base n o) a b hab
  · intro a ha
    exact (hd.2 a ha).of_iso (coveringCompactIso h V a)

end TernaryPoly.SingularLocalCompactDuality
