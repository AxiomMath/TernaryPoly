module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapRelative
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapAlgebra

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCap
open CategoryTheory Limits HomologicalComplex
open SingularLocalCoefficient SingularLocalHomology SingularLocalCap
open SingularLocalSupport RationalManifoldCompact RationalLocalOrientation

/-- Actual support restriction keeps the underlying scalar chain representative. -/
theorem supportRestriction_projection {X : Type} [TopologicalSpace X]
    (K L : Set X) (hKL : K ⊆ L) :
    cokernel.π (RationalRelativeSingular.inclusion Lᶜ) ≫ supportRestriction L K hKL =
      cokernel.π (RationalRelativeSingular.inclusion Kᶜ) := by
  simp only [supportRestriction,RationalRelativeSingular.relativeMap,cokernel.map,
    cokernel.π_desc,RationalSingularAugmentation.chainMap_id,Category.id_comp]

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]

/-- The genuine support cap commutes with enlargement of cochain support and restriction of scalar support. -/
theorem supportCap_enlargement (K L : Set B) (hKL : K ⊆ L) (a b : ℕ)
    (x : (supportCochains p V K).X a) (c : (supportChains L).X (a+b)) :
    supportCap p V L a b ((supportMap p V K L hKL).f a x) c =
      supportCap p V K a b x ((supportRestriction L K hKL).f (a+b) c) := by
  obtain ⟨c,rfl⟩ := RelativeAlgebra.projection_surjective (RationalRelativeSingular.inclusion Lᶜ) (a+b) c
  have hc := congrArg (fun f => f c)
    (HomologicalComplex.congr_hom (supportRestriction_projection K L hKL) (a+b))
  change (supportRestriction L K hKL).f (a+b)
    ((cokernel.π (RationalRelativeSingular.inclusion Lᶜ)).f (a+b) c) =
      (cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).f (a+b) c at hc
  rw [hc,supportCap_projection,supportCap_projection]
  have hx := congrArg (fun f => f x)
    (HomologicalComplex.congr_hom (supportMap_inclusion p V K L hKL) a)
  change (supportInclusion p V L).f a ((supportMap p V K L hKL).f a x) =
    (supportInclusion p V K).f a x at hx
  rw [hx]

/-- Enlargement naturality descends to the actual relative homology pairing. -/
theorem supportCapHomology_enlargement (K L : Set B) (hKL : K ⊆ L) (a b : ℕ)
    (x : (supportCochains p V K).homology a) (c : (supportChains L).homology (a+b)) :
    supportCapHomology p V L a b (homologyMap (supportMap p V K L hKL) a x) c =
      supportCapHomology p V K a b x (homologyMap (supportRestriction L K hKL) (a+b) c) := by
  obtain ⟨x,rfl⟩ := Algebra.cochainClass_surjective (supportCochains p V K) a x
  obtain ⟨c,rfl⟩ := Algebra.chainClass_surjective (supportChains L) (a+b) c
  let y : Homology.Cycles ((supportCochains p V L).sc' (a-1) a (a+1)) :=
    ⟨(supportMap p V K L hKL).f a x.val,by
      change (supportCochains p V L).d a (a+1) _ = 0
      erw [complexMap_d]
      have hx : (supportCochains p V K).d a (a+1) x.val = 0 := x.property
      rw [hx,map_zero]⟩
  let d : Homology.Cycles ((supportChains K).sc' (a+b+1) (a+b) (a+b-1)) :=
    ⟨(supportRestriction L K hKL).f (a+b) c.val,by
      change (supportChains K).d (a+b) (a+b-1) _ = 0
      erw [complexMap_d]
      have hc : (supportChains L).d (a+b) (a+b-1) c.val = 0 := c.property
      rw [hc,map_zero]⟩
  rw [Algebra.cochainClass_natural (supportMap p V K L hKL) a x y rfl,
    Algebra.chainClass_natural (supportRestriction L K hKL) (a+b) c d rfl,
    supportCapHomology_representatives,supportCapHomology_representatives]
  congr 1
  apply Subtype.ext
  exact supportCap_enlargement p V K L hKL a b x.val c.val

end TernaryPoly.SingularLocalCompactCap
