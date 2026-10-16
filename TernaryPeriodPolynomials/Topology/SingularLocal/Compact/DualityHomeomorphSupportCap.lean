module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityHomeomorphSupport
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.DualityHomeomorphChains
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMap

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactDuality
open CategoryTheory Limits HomologicalComplex
open SingularLocalConstant SingularLocalCap SingularLocalCompactCap SingularLocalSupport
open RationalLocalOrientation RationalManifoldCompact RationalHomologyCoefficients
open SingularLocalCapHomeomorph SingularLocalHomology

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E] [MulAction G E'] [ContinuousConstSMul G E']
  {p : E ⟶ B} {p' : E' ⟶ B'}
  [hp : Fact (IsQuotientCoveringMap p G)] [hp' : Fact (IsQuotientCoveringMap p' G)]
  (h : CoverHomeomorph (G := G) p p') (V : Rep.{0} ℚ G)
variable [IsCancelSMul G E] [IsCancelSMul G E']

/-- The actual support cap commutes with genuine homeomorphism pullback and pushforward. -/
theorem coveringSupportCap_natural (K : Set B') (a b : ℕ)
    (φ : (supportCochains p' V K).X a)
    (c : (supportChains (h.base ⁻¹' K)).X (a+b)) :
    (coveringChainMap h V).f b
      (supportCap p V (h.base ⁻¹' K) a b ((coveringSupportIso h V K).hom.f a φ) c) =
      supportCap p' V K a b φ ((supportPullbackIso h.base K).hom.f (a+b) c) := by
  obtain ⟨c,rfl⟩ := RelativeAlgebra.projection_surjective
    (RationalRelativeSingular.inclusion (h.base ⁻¹' K)ᶜ) (a+b) c
  have hc := congrArg (fun f => f.f (a+b) c) (supportPullback_projection h.base K)
  change (supportPullbackIso h.base K).hom.f (a+b)
    ((cokernel.π (RationalRelativeSingular.inclusion (h.base ⁻¹' K)ᶜ)).f (a+b) c) =
      (cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).f (a+b)
        ((RationalRelativeSingular.chainHomeomorphIso h.base).hom.f (a+b) c) at hc
  rw [hc,supportCap_projection,supportCap_projection]
  have hφ := congrArg (fun f => f.f a φ) (coveringSupportIso_inclusion h V K)
  change (supportInclusion p V (h.base ⁻¹' K)).f a
    ((coveringSupportIso h V K).hom.f a φ) =
      (coveringCochainMap h V).f a ((supportInclusion p' V K).f a φ) at hφ
  rw [hφ]
  exact cap_natural p p' (TopCat.isoOfHomeo h.total).hom (TopCat.isoOfHomeo h.base).hom
    h.square hp.out hp'.out h.equivariant V a b _ c

/-- Homeomorphism naturality descends to actual support cohomology and support homology classes. -/
theorem coveringSupportCapHomology_natural (K : Set B') (a b : ℕ)
    (φ : (supportCochains p' V K).homology a)
    (c : (supportChains (h.base ⁻¹' K)).homology (a+b)) :
    homologyMap (coveringChainMap h V) b
      (supportCapHomology p V (h.base ⁻¹' K) a b
        (homologyMap (coveringSupportIso h V K).hom a φ) c) =
      supportCapHomology p' V K a b φ
        (homologyMap (supportPullbackIso h.base K).hom (a+b) c) := by
  obtain ⟨φ,rfl⟩ := Algebra.cochainClass_surjective _ a φ
  obtain ⟨c,rfl⟩ := Algebra.chainClass_surjective _ (a+b) c
  rw [Algebra.cochainClass_natural (coveringSupportIso h V K).hom a φ
    (mapComplexCycle (coveringSupportIso h V K).hom (a-1) a (a+1) φ) rfl,
    Algebra.chainClass_natural (supportPullbackIso h.base K).hom (a+b) c
    (mapComplexCycle (supportPullbackIso h.base K).hom (a+b+1) (a+b) (a+b-1) c) rfl,
    supportCapHomology_representatives,supportCapHomology_representatives]
  apply Algebra.chainClass_natural
  exact (coveringSupportCap_natural h V K a b φ.val c.val).symm

end TernaryPoly.SingularLocalCompactDuality
