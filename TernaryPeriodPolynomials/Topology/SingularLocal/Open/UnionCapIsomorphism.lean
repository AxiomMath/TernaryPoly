module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Open.UnionCapDiagram

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalOpenUnion
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalHomology EquivariantSingularSmall SingularLocalSupport
open SingularLocalCompactCap RationalLocalOrientation RationalManifoldCompact
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)
  (U : ℕ → Opens B) [∀ i, ChartedSpace H (U i)] (hU : Monotone U)
  (hcover : (⋃ i, (U i : Set B)) = Set.univ)
include hU hcover

/-- Actual compact cap duality passes from every stage of an increasing open cover
to its union, using actual extension/inclusion continuity and canonical orientations. -/
theorem increasing_union_compactCap_isIso (a b : ℕ) (hab : a+b = n+2)
    (hcap : ∀ i, IsIso (compactCapMap (restrictedProjection p (U i)) V n e
      (openOrientation n e o (U i)) a b hab)) : IsIso (compactCapMap p V n e o a b hab) := by
  have := compactColimitMap_isIso p V U hU hcover a
  have := homologyColimitMap_isIso p V U hU hcover b
  exact isIso_of_colimit_square (capTransformation p V n e o U hU a b hab) hcap
    (compactColimitMap p V U hU a) (homologyColimitMap p V U hU b)
    (compactCapMap p V n e o a b hab) (capColimit_square p V n e o U hU a b hab)

/-- The resulting union duality isomorphism has exactly the actual ambient compact cap
map as its forward map. -/
def increasing_union_compactCapIso (a b : ℕ) (hab : a+b = n+2)
    (hcap : ∀ i, IsIso (compactCapMap (restrictedProjection p (U i)) V n e
      (openOrientation n e o (U i)) a b hab)) :
    compactCohomology p V a ≅ (coveringLocalChains p V).homology b := by
  have := increasing_union_compactCap_isIso p V n e o U hU hcover a b hab hcap
  exact asIso (compactCapMap p V n e o a b hab)

/-- Literal forward-map identity for the increasing-union compact cap isomorphism. -/
theorem increasing_union_compactCapIso_hom (a b : ℕ) (hab : a+b = n+2)
    (hcap : ∀ i, IsIso (compactCapMap (restrictedProjection p (U i)) V n e
      (openOrientation n e o (U i)) a b hab)) :
    (increasing_union_compactCapIso p V n e o U hU hcover a b hab hcap).hom =
      compactCapMap p V n e o a b hab := rfl

end TernaryPoly.SingularLocalOpenUnion
