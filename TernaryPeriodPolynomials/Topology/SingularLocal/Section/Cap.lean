module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Section.Chains
public import TernaryPeriodPolynomials.Topology.SingularLocal.Section.Cochains
public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Product

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalSection
open CategoryTheory CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SingularLocalConstant SingularLocalCap FreeActionLinearization
open SphereOddDegree.AffineBarycentricSubdivision

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E]
    (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (s : B ⟶ E) (hs : s ≫ p = 𝟙 B)
    (V : Rep.{0} ℚ G)

/-- Section evaluation intertwines the two actual cap products after the literal ordinary-chain comparison. -/
theorem cap_ordinary (a b : ℕ) (φ : VertexCochain p hp V a)
    (c : singularChainGroup ℚ B (a+b)) :
    ordinaryDegreeEquiv p hp s hs V b (cap p hp V a b φ c) =
      SingularLocalConstant.chainDegreeEquiv B (ModuleCat.of ℚ V) b
        (cap (𝟙 B) (identityCover B) (constantRep (ModuleCat.of ℚ V)) a b
          (cochainDegreeEquiv p hp s hs V a φ) c) := by
  have h : (ordinaryDegreeEquiv p hp s hs V b).toLinearMap.comp (cap p hp V a b φ) =
      (SingularLocalConstant.chainDegreeEquiv B (ModuleCat.of ℚ V) b).toLinearMap.comp
        (cap (𝟙 B) (identityCover B) (constantRep (ModuleCat.of ℚ V)) a b
          (cochainDegreeEquiv p hp s hs V a φ)) := by
    apply scalarChain_ext
    intro σ
    change ordinaryDegreeEquiv p hp s hs V b (cap p hp V a b φ _) =
      SingularLocalConstant.chainDegreeEquiv B (ModuleCat.of ℚ V) b
        (cap (𝟙 B) (identityCover B) (constantRep (ModuleCat.of ℚ V)) a b
          (cochainDegreeEquiv p hp s hs V a φ) _)
    erw [cap_generator,cap_generator,capSimplex_apply,capSimplex_apply]
    erw [ordinaryDegreeEquiv_single,SingularLocalConstant.chainDegreeEquiv_single]
    erw [sectionEvaluation_transport,sectionEvaluation_transport,
      fiberEquiv_transport,fiberEquiv_transport]
    congr 1
  exact LinearMap.congr_fun h c

variable [ContinuousConstSMul G E] [IsCancelSMul G E]

/-- The section-induced actual chain and cochain isomorphisms commute with genuine cap. -/
theorem cap_natural (a b : ℕ) (φ : VertexCochain p hp V a)
    (c : singularChainGroup ℚ B (a+b)) :
    (chainIso p hp s hs V).hom.f b (cap p hp V a b φ c) =
      cap (𝟙 B) (identityCover B) (constantRep (ModuleCat.of ℚ V)) a b
        ((cochainIso p hp s hs V).hom.f a φ) c := by
  apply (SingularLocalConstant.chainDegreeEquiv B (ModuleCat.of ℚ V) b).injective
  erw [chainIso_hom_ordinary_apply]
  exact cap_ordinary p hp s hs V a b φ c

end TernaryPoly.SingularLocalSection
