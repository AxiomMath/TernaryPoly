module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityLocal

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactDuality
open CategoryTheory Limits TopologicalSpace
open SingularLocalSupport SingularLocalCompactCap RationalLocalOrientation

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [SecondCountableTopology B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))

/-- Every actual open subset of the manifold has the complete local-coefficient duality
property, obtained from genuine covering sections, Euclidean models, Mayer–Vietoris,
and increasing-open continuity. -/
theorem manifold_openDuality (s : Set B) (hs : IsOpen s) : OpenDuality p V n e s := by
  apply OpenBasisGluing.open_induction_of_cover (OpenDuality p V n e)
    (fun x : B => (CoveringEuclideanCharts.coverOpen (G := G) p n e x : Set B))
    (fun x => (CoveringEuclideanCharts.coverOpen (G := G) p n e x).isOpen)
    (CoveringEuclideanCharts.cover_iUnion (G := G) p n e) ?_
    (openDuality_empty p V n e) (openDuality_union p V n e) (openDuality_iUnion p V n e) s hs
  intro x D hD hDU
  exact openDuality_in_chart p V n e (CoveringEuclideanCharts.coverOpen (G := G) p n e x)
    (CoveringEuclideanCharts.coverHomeomorph (G := G) p n e x)
    (CoveringEuclideanCharts.coverSection (G := G) p n e x) D hD hDU

/-- Actual local-coefficient compact-cap duality and upper compact-cohomology vanishing
on Hausdorff second-countable Euclidean-charted manifolds. -/
theorem manifold_duality : Duality p V n e :=
  duality_of_openDuality_univ p V n e (manifold_openDuality p V n e Set.univ isOpen_univ)

/-- The literal compactCapMap is an isomorphism for every genuine orientation, quotient
covering, arbitrary rational representation, and complementary pair of degrees. -/
theorem manifold_compactCap_isIso (o : Orientation (n+2) B) (a b : ℕ) (hab : a+b = n+2) :
    IsIso (compactCapMap p V n e o a b hab) :=
  (manifold_duality p V n e).1 o a b hab

include e in
/-- Actual compact-support cohomology vanishes strictly above the manifold dimension. -/
theorem manifold_compactCohomology_above_isZero (a : ℕ) (ha : n+2 < a) :
    IsZero (compactCohomology p V a) := (manifold_duality p V n e).2 a ha

/-- The resulting duality isomorphism has exactly the genuine given-orientation cap map. -/
def manifold_compactCapIso (o : Orientation (n+2) B) (a b : ℕ) (hab : a+b = n+2) :
    compactCohomology p V a ≅ (coveringLocalChains p V).homology b := by
  have := manifold_compactCap_isIso p V n e o a b hab
  exact asIso (compactCapMap p V n e o a b hab)

/-- The final isomorphism retains the literal compact cap map as its forward morphism. -/
theorem manifold_compactCapIso_hom (o : Orientation (n+2) B) (a b : ℕ) (hab : a+b = n+2) :
    (manifold_compactCapIso p V n e o a b hab).hom = compactCapMap p V n e o a b hab := rfl

end TernaryPoly.SingularLocalCompactDuality
