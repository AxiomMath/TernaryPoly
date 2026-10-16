module

public import TernaryPeriodPolynomials.Analysis.Compact.OrdinaryCapComparison
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.Duality

@[expose] public section


noncomputable section
namespace TernaryPoly.CompactOrdinaryCap
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCoefficient SingularLocalCompactCap RationalLocalOrientation

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  {H : Type} [TopologicalSpace H] [T2Space B] [SecondCountableTopology B]
  [ChartedSpace H B] [CompactSpace B] (n : ℕ) (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
  (o : Orientation (n+2) B)

/-- Ordinary cap on a compact manifold, transported by the canonical actual compact-support
comparison and retaining the supplied genuine orientation as an explicit argument. -/
def ordinaryCapMap (a b : ℕ) (hab : a+b = n+2) :
    (localCochains p hp.out V).homology a ⟶ (coveringLocalChains p V).homology b :=
  (compactOrdinaryIso p V a).inv ≫ compactCapMap p V n e o a b hab

omit [SecondCountableTopology B] in
/-- The ordinary cap map agrees exactly with the genuine compact cap after support forgetting. -/
theorem compactToOrdinary_cap (a b : ℕ) (hab : a+b = n+2) :
    compactToOrdinary p V a ≫ ordinaryCapMap p V n e o a b hab =
      compactCapMap p V n e o a b hab := by
  change (compactOrdinaryIso p V a).hom ≫ ((compactOrdinaryIso p V a).inv ≫ _) = _
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- Genuine compact-cap duality proves ordinary-cap duality on each compact manifold. -/
instance ordinaryCapMap_isIso (a b : ℕ) (hab : a+b = n+2) :
    IsIso (ordinaryCapMap p V n e o a b hab) := by
  have := SingularLocalCompactDuality.manifold_compactCap_isIso p V n e o a b hab
  unfold ordinaryCapMap
  infer_instance

/-- The ordinary local-cohomology/chain-homology isomorphism with its literal ordinary cap map. -/
def ordinaryCapIso (a b : ℕ) (hab : a+b = n+2) :
    (localCochains p hp.out V).homology a ≅ (coveringLocalChains p V).homology b :=
  asIso (ordinaryCapMap p V n e o a b hab)

@[simp] theorem ordinaryCapIso_hom (a b : ℕ) (hab : a+b = n+2) :
    (ordinaryCapIso p V n e o a b hab).hom = ordinaryCapMap p V n e o a b hab := rfl

omit [SecondCountableTopology B] in
/-- Every actual compact-support representative gives the same ordinary cap result. -/
theorem ordinaryCap_classMap [IsCancelSMul G E] (K : Compacts B)
    (a b : ℕ) (hab : a+b = n+2) :
    homologyMap (supportInclusion p V (K : Set B)) a ≫ ordinaryCapMap p V n e o a b hab =
      compactCapAt p V n e o K a b hab := by
  rw [← compactToOrdinary_classMap p V K a, Category.assoc, compactToOrdinary_cap]
  exact compactCapMap_classMap p V n e o K a b hab

omit [SecondCountableTopology B] in
/-- In particular ordinary cap is the genuine top-support cap on the same representative. -/
theorem ordinaryCap_top [IsCancelSMul G E] (a b : ℕ) (hab : a+b = n+2) :
    ordinaryCapMap p V n e o a b hab =
      (topSupportHomologyIso p V a).inv ≫ compactCapAt p V n e o (⊤ : Compacts B) a b hab := by
  rw [ordinaryCapMap, compactOrdinaryIso_inv_top, Category.assoc, compactCapMap_classMap]

end TernaryPoly.CompactOrdinaryCap
