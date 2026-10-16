module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Open.UnionCapIsomorphism

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalOpenUnion
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalHomology SingularLocalExcision EquivariantSingularSmall SingularLocalSupport
open SingularLocalCompactCap RationalLocalOrientation RationalManifoldCompact
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  [T2Space B] (U : ℕ → Opens B) (hU : Monotone U)
  (hcover : (⋃ i, (U i : Set B)) = Set.univ)

omit [IsCancelSMul G E] in
/-- The proved compact-support continuity isomorphism has actual open extension as
its literal map on each stage of the increasing cover. -/
theorem compactContinuity_stage (a i : ℕ) :
    colimit.ι (compactDiagram p V U hU a) i ≫ (compactColimitIso p V U hU hcover a).hom =
      openExtension p V (U i) a := compactColimitMap_ι p V U hU a i

omit [T2Space B] in
/-- The proved local-homology continuity isomorphism has the literal restricted-cover
localSpaceMap inclusion as its map on each stage. -/
theorem homologyContinuity_stage (b i : ℕ) :
    colimit.ι (homologyDiagram p V U hU b) i ≫ (homologyColimitIso p V U hU hcover b).hom =
      homologyMap (openLocalChainMap p V (U i)) b := homologyColimitMap_ι p V U hU b i

variable {H : Type} [TopologicalSpace H] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)
  [∀ i, ChartedSpace H (U i)]
include hU hcover

omit [IsCancelSMul G E] in
/-- Downstream union-duality consumer for every quotient covering and arbitrary rational
representation. Cancellation is derived from the covering, and the resulting forward
map is exactly the actual ambient compactCapMap. -/
theorem increasing_union_consumer (a b : ℕ) (hab : a+b = n+2)
    (hcap : ∀ i, IsIso (compactCapMap (restrictedProjection p (U i)) V n e
      (openOrientation n e o (U i)) a b hab)) :
    ∃ I : compactCohomology p V a ≅ (coveringLocalChains p V).homology b,
      I.hom = compactCapMap p V n e o a b hab := by
  let : IsCancelSMul G E := hp.out.isCancelSMul
  exact ⟨increasing_union_compactCapIso p V n e o U hU hcover a b hab hcap,
    increasing_union_compactCapIso_hom p V n e o U hU hcover a b hab hcap⟩

end TernaryPoly.SingularLocalOpenUnion
