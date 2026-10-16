module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Section.SupportCap
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalSection
open CategoryTheory Limits HomologicalComplex
open SingularLocalConstant SingularLocalSupport SingularLocalCompactCap
open SingularLocalCoefficient SingularLocalHomology SingularLocalCap
open RationalManifoldCompact

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
    (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] [IsCancelSMul G E]
    (s : B ⟶ E) (hs : s ≫ p = 𝟙 B) (V : Rep.{0} ℚ G)
local instance : Fact (IsQuotientCoveringMap (𝟙 B) Unit) := ⟨identityCover B⟩

/-- Genuine section trivialization commutes with actual relative cap on homology. -/
theorem supportCapHomology_natural (K : Set B) (a b : ℕ)
    (x : (supportCochains p V K).homology a) (c : (supportChains K).homology (a+b)) :
    homologyMap (chainIso p hp.out s hs V).hom b (supportCapHomology p V K a b x c) =
      supportCapHomology (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K a b
        (homologyMap (supportIso p s hs V K).hom a x) c := by
  obtain ⟨x,rfl⟩ := Algebra.cochainClass_surjective (supportCochains p V K) a x
  obtain ⟨c,rfl⟩ := Algebra.chainClass_surjective (supportChains K) (a+b) c
  let y : Homology.Cycles ((supportCochains (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K).sc'
      (a-1) a (a+1)) :=
    ⟨(supportIso p s hs V K).hom.f a x.val,by
      change (supportCochains (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K).d a (a+1) _ = 0
      erw [complexMap_d]
      have hx : (supportCochains p V K).d a (a+1) x.val = 0 := x.property
      erw [hx,map_zero]⟩
  erw [Algebra.cochainClass_natural (supportIso p s hs V K).hom a x y rfl,
    supportCapHomology_representatives,supportCapHomology_representatives]
  apply Algebra.chainClass_natural
  exact (supportCap_natural p s hs V K a b x.val c.val).symm

end TernaryPoly.SingularLocalSection
