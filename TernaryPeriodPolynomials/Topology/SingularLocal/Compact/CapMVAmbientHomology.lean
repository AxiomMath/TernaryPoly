module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVFixedPairing

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory HomologicalComplex TopologicalSpace
open SingularLocalCap SingularLocalSupport SingularLocalCompactCap

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  (K L : Set B) (hK : IsClosed K) (hL : IsClosed L) (U D : Opens B) (hKU : K ⊆ U) (hLD : L ⊆ D)

/-- The actual ambient pairing is the pullback of the genuine supported cap on homology. -/
theorem ambientPairing_homology (a b : ℕ) (x : (supportCochains p V (K ∪ L)).homology a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).homology (a+b)) :
    Descent.homology _ _ _ (ambientPairing p V K L hK hL U D hKU hLD)
      (ambientPairing_leibniz p V K L hK hL U D hKU hLD) a b x c =
    supportCapHomology p V (K ∪ L) a b x
      (homologyMap (relativeSmallMap (K ∪ L)ᶜ (supportRefinement K L hK hL U D hKU hLD)) (a+b) c) := by
  have h := pullPairing_homology (𝟙 (supportCochains p V (K ∪ L)))
    (relativeSmallMap (K ∪ L)ᶜ (supportRefinement K L hK hL U D hKU hLD))
    (supportCap p V (K ∪ L)) (supportCap_leibniz p V (K ∪ L)) a b x c
  rw [homologyMap_id,ModuleCat.id_apply] at h
  exact h

end TernaryPoly.SingularLocalCompactCapMV
