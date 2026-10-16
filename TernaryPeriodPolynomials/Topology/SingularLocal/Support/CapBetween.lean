module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.CapOpenHomology
public import TernaryPeriodPolynomials.Topology.SingularLocal.Support.Between
public import TernaryPeriodPolynomials.Topology.Rational.Compact.SupportBetween

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCap
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalCoefficient SingularLocalHomology SingularLocalCap SingularCoverNaturality
open SingularLocalSupport EquivariantSingularSmall EquivariantSingularMayerVietoris
open RationalManifoldCompact

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- The actual local-chain inclusion between restrictions to nested opens of a common base. -/
abbrev openLocalChainMapBetween (D U : Opens B) (hDU : D ≤ U) :
    letI : IsCancelSMul G (TopCat.of (p ⁻¹' (D : Set B))) := (restrictedQuotientCovering p D).isCancelSMul
    letI : IsCancelSMul G (TopCat.of (p ⁻¹' (U : Set B))) := (restrictedQuotientCovering p U).isCancelSMul
    localChains (restrictedProjection p D) (restrictedQuotientCovering p D) V ⟶
      localChains (restrictedProjection p U) (restrictedQuotientCovering p U) V := by
  letI : IsCancelSMul G (TopCat.of (p ⁻¹' (D : Set B))) := (restrictedQuotientCovering p D).isCancelSMul
  letI : IsCancelSMul G (TopCat.of (p ⁻¹' (U : Set B))) := (restrictedQuotientCovering p U).isCancelSMul
  exact localSpaceMap (subspaceInclusion E (p ⁻¹' (D : Set B)) (p ⁻¹' (U : Set B)) (Set.preimage_mono hDU))
    (fun _ _ => rfl) V (restrictedProjection p D) (restrictedProjection p U)
    (restrictedQuotientCovering p D) (restrictedQuotientCovering p U)

variable [IsCancelSMul G E]

/-- The genuine support cap respects actual restriction and inclusion between nested opens. -/
theorem supportCap_between (D U : Opens B) (hDU : D ≤ U) (K : Set B) (a b : ℕ)
    (x : (supportCochains (restrictedProjection p U) V ((Subtype.val : U → B) ⁻¹' K)).X a)
    (c : (supportChains ((Subtype.val : D → B) ⁻¹' K)).X (a+b)) :
    (openLocalChainMapBetween p V D U hDU).f b
      (supportCap (restrictedProjection p D) V ((Subtype.val : D → B) ⁻¹' K) a b
        ((supportBetweenRestriction p V D U hDU K).f a x) c) =
    supportCap (restrictedProjection p U) V ((Subtype.val : U → B) ⁻¹' K) a b x
      ((openSupportMap D U hDU K).f (a+b) c) := by
  obtain ⟨c,rfl⟩ := RelativeAlgebra.projection_surjective
    (RationalRelativeSingular.inclusion ((Subtype.val : D → B) ⁻¹' K)ᶜ) (a+b) c
  have hc := congrArg (fun f => f c)
    (HomologicalComplex.congr_hom (openSupportMap_projection D U hDU K) (a+b))
  change (openSupportMap D U hDU K).f (a+b)
    ((cokernel.π (RationalRelativeSingular.inclusion ((Subtype.val : D → B) ⁻¹' K)ᶜ)).f (a+b) c) =
      (cokernel.π (RationalRelativeSingular.inclusion ((Subtype.val : U → B) ⁻¹' K)ᶜ)).f (a+b)
        ((RationalSingularAugmentation.chainMap (openInclusion D U hDU)).f (a+b) c) at hc
  erw [hc,supportCap_projection,supportCap_projection]
  have hx := congrArg (fun f => f x)
    (HomologicalComplex.congr_hom (supportBetweenRestriction_inclusion p V D U hDU K) a)
  change (supportInclusion (restrictedProjection p D) V ((Subtype.val : D → B) ⁻¹' K)).f a
    ((supportBetweenRestriction p V D U hDU K).f a x) =
      (nestedLocalRestriction p D U hDU V).f a
        ((supportInclusion (restrictedProjection p U) V ((Subtype.val : U → B) ⁻¹' K)).f a x) at hx
  erw [hx]
  exact cap_natural (restrictedProjection p D) (restrictedProjection p U)
    (subspaceInclusion E (p ⁻¹' (D : Set B)) (p ⁻¹' (U : Set B)) (Set.preimage_mono hDU))
    (subspaceInclusion B D U hDU) (nestedRestricted_square p D U hDU)
    (restrictedQuotientCovering p D) (restrictedQuotientCovering p U) (fun _ _ => rfl) V a b _ c

end TernaryPoly.SingularLocalCompactCap
