module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Open.UnionColimitAlgebra
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapBetween

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalOpenUnion
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalHomology SingularLocalExcision EquivariantSingularSmall SingularLocalSupport
open SingularLocalCompactCap RationalLocalOrientation RationalManifoldCompact
variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  {H : Type} [TopologicalSpace H] [T2Space B] [ChartedSpace H B]
  (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)
  (U : ℕ → Opens B) [∀ i, ChartedSpace H (U i)] (hU : Monotone U)

/-- The actual compact cap maps with the canonical restricted orientations form a
natural transformation between the two genuine increasing-open diagrams. -/
def capTransformation (a b : ℕ) (hab : a+b = n+2) :
    compactDiagram p V U hU a ⟶ homologyDiagram p V U hU b where
  app i := compactCapMap (restrictedProjection p (U i)) V n e (openOrientation n e o (U i)) a b hab
  naturality i j f := by
    change openExtensionBetween p V (U i) (U j) (hU (leOfHom f)) a ≫
      compactCapMap (restrictedProjection p (U j)) V n e (openOrientation n e o (U j)) a b hab =
      compactCapMap (restrictedProjection p (U i)) V n e (openOrientation n e o (U i)) a b hab ≫
        homologyMap (nestedLocalInclusion p (U i) (U j) (hU (leOfHom f)) V) b
    exact compactCapMap_between p V n e o (U i) (U j) (hU (leOfHom f)) a b hab

/-- The actual cap natural transformation and actual continuity comparisons commute
with the actual ambient compact cap map, by canonical open-inclusion naturality. -/
theorem capColimit_square (a b : ℕ) (hab : a+b = n+2) :
    compactColimitMap p V U hU a ≫ compactCapMap p V n e o a b hab =
      colim.map (capTransformation p V n e o U hU a b hab) ≫ homologyColimitMap p V U hU b := by
  apply colimit.hom_ext
  intro i
  rw [← Category.assoc,compactColimitMap_ι]
  rw [colim_map,ι_colimMap_assoc]
  change openExtension p V (U i) a ≫ compactCapMap p V n e o a b hab =
    compactCapMap (restrictedProjection p (U i)) V n e (openOrientation n e o (U i)) a b hab ≫
      colimit.ι (homologyDiagram p V U hU b) i ≫ homologyColimitMap p V U hU b
  exact (compactCapMap_open_canonical p V n e o (U i) a b hab).trans
    (congrArg (fun f => compactCapMap (restrictedProjection p (U i)) V n e
      (openOrientation n e o (U i)) a b hab ≫ f) (homologyColimitMap_ι p V U hU b i)).symm

end TernaryPoly.SingularLocalOpenUnion
