module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Section.Cap
public import TernaryPeriodPolynomials.Topology.SingularLocal.Section.Support
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapRelative

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

/-- The actual section comparisons commute with fixed-support cap on genuine relative scalar chains. -/
theorem supportCap_natural (K : Set B) (a b : ℕ) (φ : (supportCochains p V K).X a)
    (c : (supportChains K).X (a+b)) :
    (chainIso p hp.out s hs V).hom.f b (supportCap p V K a b φ c) =
      supportCap (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K a b
        ((supportIso p s hs V K).hom.f a φ) c := by
  obtain ⟨c,rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cokernel.π (RationalRelativeSingular.inclusion Kᶜ)).f (a+b))).mp inferInstance c
  rw [supportCap_projection,supportCap_projection]
  have hφ := congrArg (fun f => f.f a φ) (supportHom_inclusion p s hs V K)
  change (supportInclusion (𝟙 B) (constantRep (ModuleCat.of ℚ V)) K).f a
      ((supportIso p s hs V K).hom.f a φ) =
    (cochainIso p hp.out s hs V).hom.f a ((supportInclusion p V K).f a φ) at hφ
  erw [hφ]
  exact cap_natural p hp.out s hs V a b _ c

end TernaryPoly.SingularLocalSection
