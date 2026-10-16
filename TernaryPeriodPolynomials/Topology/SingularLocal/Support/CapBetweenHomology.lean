module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.CapBetween

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCap
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalCoefficient SingularLocalHomology SingularLocalCap
open SingularLocalSupport EquivariantSingularSmall RationalManifoldCompact

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]

/-- Genuine support-cap naturality under nested open restriction holds for every actual
cohomology and homology class, with the actual inclusion maps on local chains. -/
theorem supportCapHomology_between (D U : Opens B) (hDU : D ≤ U) (K : Set B) (a b : ℕ)
    (x : (supportCochains (restrictedProjection p U) V ((Subtype.val : U → B) ⁻¹' K)).homology a)
    (c : (supportChains ((Subtype.val : D → B) ⁻¹' K)).homology (a+b)) :
    homologyMap (openLocalChainMapBetween p V D U hDU) b
      (supportCapHomology (restrictedProjection p D) V ((Subtype.val : D → B) ⁻¹' K) a b
        (homologyMap (supportBetweenRestriction p V D U hDU K) a x) c) =
      supportCapHomology (restrictedProjection p U) V ((Subtype.val : U → B) ⁻¹' K) a b x
        (homologyMap (openSupportMap D U hDU K) (a+b) c) := by
  obtain ⟨x,rfl⟩ := Algebra.cochainClass_surjective (supportCochains (restrictedProjection p U) V ((Subtype.val : U → B) ⁻¹' K)) a x
  obtain ⟨c,rfl⟩ := Algebra.chainClass_surjective (supportChains ((Subtype.val : D → B) ⁻¹' K)) (a+b) c
  let y : Homology.Cycles ((supportCochains (restrictedProjection p D) V
      ((Subtype.val : D → B) ⁻¹' K)).sc' (a-1) a (a+1)) :=
    ⟨(supportBetweenRestriction p V D U hDU K).f a x.val,by
      change (supportCochains (restrictedProjection p D) V ((Subtype.val : D → B) ⁻¹' K)).d a (a+1) _ = 0
      erw [complexMap_d]
      have hx : (supportCochains (restrictedProjection p U) V ((Subtype.val : U → B) ⁻¹' K)).d a (a+1) x.val = 0 := x.property
      erw [hx,map_zero]⟩
  let d : Homology.Cycles ((supportChains ((Subtype.val : U → B) ⁻¹' K)).sc' (a+b+1) (a+b) (a+b-1)) :=
    ⟨(openSupportMap D U hDU K).f (a+b) c.val,by
      change (supportChains ((Subtype.val : U → B) ⁻¹' K)).d (a+b) (a+b-1) _ = 0
      erw [complexMap_d]
      have hc : (supportChains ((Subtype.val : D → B) ⁻¹' K)).d (a+b) (a+b-1) c.val = 0 := c.property
      rw [hc,map_zero]⟩
  erw [Algebra.cochainClass_natural (supportBetweenRestriction p V D U hDU K) a x y rfl,
    Algebra.chainClass_natural (openSupportMap D U hDU K) (a+b) c d rfl,
    supportCapHomology_representatives,supportCapHomology_representatives]
  apply Algebra.chainClass_natural
  exact (supportCap_between p V D U hDU K a b x.val c.val).symm

end TernaryPoly.SingularLocalCompactCap
