module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapNaturality
public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.Excision
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Naturality

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCap
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalCoefficient SingularLocalHomology SingularLocalCap SingularCoverNaturality
open SingularLocalSupport EquivariantSingularSmall SphereOddDegree RationalManifoldCompact

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- The actual local-chain pushforward from a restricted covering to its ambient covering. -/
abbrev openLocalChainMap (D : Set B) :
    letI : IsCancelSMul G E := hp.out.isCancelSMul
    letI : IsCancelSMul G (TopCat.of (p ⁻¹' D)) := (restrictedQuotientCovering p D).isCancelSMul
    localChains (restrictedProjection p D) (restrictedQuotientCovering p D) V ⟶
      localChains p hp.out V := by
  letI : IsCancelSMul G E := hp.out.isCancelSMul
  letI : IsCancelSMul G (TopCat.of (p ⁻¹' D)) := (restrictedQuotientCovering p D).isCancelSMul
  exact localSpaceMap (sInclusion (p ⁻¹' D)) (fun _ _ => rfl) V
    (restrictedProjection p D) p (restrictedQuotientCovering p D) hp.out

/-- Literal support excision retains the ambient scalar chain representative. -/
theorem supportExcision_projection (D K : Set B) :
    cokernel.π (RationalRelativeSingular.inclusion ((Subtype.val : D → B) ⁻¹' K)ᶜ) ≫
      RationalLocalOrientation.supportExcisionMap K D =
    RationalSingularAugmentation.chainMap ⟨Subtype.val,continuous_subtype_val⟩ ≫
      cokernel.π (RationalRelativeSingular.inclusion Kᶜ) := by
  simp only [RationalLocalOrientation.supportExcisionMap,RationalRelativeExcision.excisionMap,
    RationalRelativeSingular.relativeMap,cokernel.map]
  erw [cokernel.π_desc]

variable [IsCancelSMul G E]

/-- Actual support cap commutes with restriction of cochains to an open neighborhood and
pushforward of its relative scalar chains. -/
theorem supportCap_toOpen (D K : Set B) (a b : ℕ)
    (x : (supportCochains p V K).X a)
    (c : (supportChains ((Subtype.val : D → B) ⁻¹' K)).X (a+b)) :
    (openLocalChainMap p V D).f b
      (supportCap (restrictedProjection p D) V ((Subtype.val : D → B) ⁻¹' K) a b
        ((supportToOpen p V D K).f a x) c) =
      supportCap p V K a b x ((RationalLocalOrientation.supportExcisionMap K D).f (a+b) c) := by
  obtain ⟨c,rfl⟩ := RelativeAlgebra.projection_surjective
    (RationalRelativeSingular.inclusion ((Subtype.val : D → B) ⁻¹' K)ᶜ) (a+b) c
  have hc := congrArg (fun f => f c)
    (HomologicalComplex.congr_hom (supportExcision_projection (B := B) D K) (a+b))
  change (RationalLocalOrientation.supportExcisionMap K D).f (a+b)
    ((cokernel.π (RationalRelativeSingular.inclusion ((Subtype.val : D → B) ⁻¹' K)ᶜ)).f (a+b) c) =
      (cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).f (a+b)
        ((RationalSingularAugmentation.chainMap ⟨Subtype.val,continuous_subtype_val⟩).f (a+b) c) at hc
  erw [hc,supportCap_projection,supportCap_projection]
  have hx := congrArg (fun f => f x)
    (HomologicalComplex.congr_hom (supportToOpen_inclusion p V D K) a)
  change (supportInclusion (restrictedProjection p D) V ((Subtype.val : D → B) ⁻¹' K)).f a
    ((supportToOpen p V D K).f a x) = (localRestriction p D V).f a ((supportInclusion p V K).f a x) at hx
  erw [hx]
  exact cap_natural (restrictedProjection p D) p (sInclusion (p ⁻¹' D)) (sInclusion D)
    (restricted_square p D) (restrictedQuotientCovering p D) hp.out (fun _ _ => rfl) V a b _ c

end TernaryPoly.SingularLocalCompactCap
