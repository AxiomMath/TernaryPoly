module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Section.Compact
public import TernaryPeriodPolynomials.Topology.SingularLocal.Section.SupportCapHomology
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMap

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSection
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalConstant SingularLocalSupport SingularLocalCompactCap SingularLocalHomology
open RationalLocalOrientation

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
    (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)]
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) (V : Rep.{0} ℚ G)
local instance : Fact (IsQuotientCoveringMap (𝟙 B) Unit) := ⟨identityCover B⟩

/-- Actual local-homology trivialization, with cancellation supplied by the covering. -/
def homologyIso (b : ℕ) : (coveringLocalChains p V).homology b ≅
    (coveringLocalChains (𝟙 B) (constantRep (ModuleCat.of ℚ V))).homology b := by
  letI : IsCancelSMul G E := hp.out.isCancelSMul
  exact (homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ) b).mapIso
    (chainIso p hp.out s hs V)

variable [T2Space B] {H : Type} [TopologicalSpace H] [ChartedSpace H B]
    (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) B)

/-- At a fixed compact support, actual section trivialization preserves cap against the
same genuine manifold fundamental class. -/
theorem compactCapAt_natural (K : Compacts B) (a b : ℕ) (hab : a+b = n+2)
    [IsCancelSMul G E] :
    compactCapAt p V n e o K a b hab ≫ (homologyIso p s hs V b).hom =
      homologyMap (supportIso p s hs V K).hom a ≫
        compactCapAt (𝟙 B) (constantRep (ModuleCat.of ℚ V)) n e o K a b hab := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact supportCapHomology_natural p s hs V K a b x (capFundamentalClass n e o K a b hab)

/-- The actual compact cap square for a genuine continuous section. -/
theorem compactCapMap_natural (a b : ℕ) (hab : a+b = n+2) :
    compactCapMap p V n e o a b hab ≫ (homologyIso p s hs V b).hom =
      (compactCohomologyIso p s hs V a).hom ≫
        compactCapMap (𝟙 B) (constantRep (ModuleCat.of ℚ V)) n e o a b hab := by
  let : IsCancelSMul G E := hp.out.isCancelSMul
  apply colimit.hom_ext
  intro K
  change compactClassMap p V K a ≫ _ = compactClassMap p V K a ≫ _
  rw [← Category.assoc,compactCapMap_classMap,← Category.assoc,compactCohomologyIso_classMap,
    Category.assoc,compactCapMap_classMap]
  exact compactCapAt_natural p s hs V n e o K a b hab

include s hs in
/-- Actual compact cap duality for constant coefficients implies actual local-coefficient
cap duality whenever the quotient covering admits a continuous global section. -/
theorem section_compactCap_isIso (a b : ℕ) (hab : a+b = n+2)
    [IsIso (compactCapMap (𝟙 B) (constantRep (ModuleCat.of ℚ V)) n e o a b hab)] :
    IsIso (compactCapMap p V n e o a b hab) := by
  have h : compactCapMap p V n e o a b hab =
      (compactCohomologyIso p s hs V a).hom ≫
        compactCapMap (𝟙 B) (constantRep (ModuleCat.of ℚ V)) n e o a b hab ≫
          (homologyIso p s hs V b).inv := by
    apply (cancel_mono (homologyIso p s hs V b).hom).mp
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    exact compactCapMap_natural p s hs V n e o a b hab
  rw [h]
  infer_instance

end TernaryPoly.SingularLocalSection
