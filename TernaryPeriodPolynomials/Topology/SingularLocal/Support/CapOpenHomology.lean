module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.CapOpen

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCap
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalCoefficient SingularLocalHomology SingularLocalCap
open SingularLocalSupport EquivariantSingularSmall RationalManifoldCompact

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]

/-- Genuine support-cap naturality under neighborhood restriction holds for every actual
cohomology and homology class, with the actual inclusion maps on local chains. -/
theorem supportCapHomology_toOpen (D K : Set B) (a b : ℕ)
    (x : (supportCochains p V K).homology a)
    (c : (supportChains ((Subtype.val : D → B) ⁻¹' K)).homology (a+b)) :
    homologyMap (openLocalChainMap p V D) b
      (supportCapHomology (restrictedProjection p D) V ((Subtype.val : D → B) ⁻¹' K) a b
        (homologyMap (supportToOpen p V D K) a x) c) =
      supportCapHomology p V K a b x
        (homologyMap (RationalLocalOrientation.supportExcisionMap K D) (a+b) c) := by
  obtain ⟨x,rfl⟩ := Algebra.cochainClass_surjective (supportCochains p V K) a x
  obtain ⟨c,rfl⟩ := Algebra.chainClass_surjective (supportChains ((Subtype.val : D → B) ⁻¹' K)) (a+b) c
  let y : Homology.Cycles ((supportCochains (restrictedProjection p D) V
      ((Subtype.val : D → B) ⁻¹' K)).sc' (a-1) a (a+1)) :=
    ⟨(supportToOpen p V D K).f a x.val,by
      change (supportCochains (restrictedProjection p D) V ((Subtype.val : D → B) ⁻¹' K)).d a (a+1) _ = 0
      erw [complexMap_d]
      have hx : (supportCochains p V K).d a (a+1) x.val = 0 := x.property
      rw [hx,map_zero]⟩
  let d : Homology.Cycles ((supportChains K).sc' (a+b+1) (a+b) (a+b-1)) :=
    ⟨(RationalLocalOrientation.supportExcisionMap K D).f (a+b) c.val,by
      change (supportChains K).d (a+b) (a+b-1) _ = 0
      erw [complexMap_d]
      have hc : (supportChains ((Subtype.val : D → B) ⁻¹' K)).d (a+b) (a+b-1) c.val = 0 := c.property
      rw [hc,map_zero]⟩
  rw [Algebra.cochainClass_natural (supportToOpen p V D K) a x y rfl,
    Algebra.chainClass_natural (RationalLocalOrientation.supportExcisionMap K D) (a+b) c d rfl,
    supportCapHomology_representatives,supportCapHomology_representatives]
  apply Algebra.chainClass_natural
  exact (supportCap_toOpen p V D K a b x.val c.val).symm

end TernaryPoly.SingularLocalCompactCap
