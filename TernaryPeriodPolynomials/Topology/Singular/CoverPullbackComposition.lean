module

public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityCochains
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallCochains

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularCoverNaturality
open CategoryTheory HomologicalComplex SingularLocalCoefficient EquivariantSingularResolution

variable {G : Type} [Group G] {E E' E'' B B' B'' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  [MulAction G E''] [ContinuousConstSMul G E'']

/-- Actual equivariant singular-chain maps preserve composition. -/
theorem chainMap_comp (F : E ⟶ E') (H : E' ⟶ E'')
    (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
    (hH : ∀ (g : G) (x : E'), H (g • x) = g • H x) :
    chainMap (F ≫ H) (fun g x => by change H (F (g • x)) = g • H (F x); rw [hF,hH]) =
      chainMap F hF ≫ chainMap H hH := by
  ext n c
  exact congrArg (fun f => (f.f n).hom c)
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map_comp F H)

/-- Actual equivariant singular-chain pullback preserves identity maps. -/
theorem chainMap_id : chainMap (𝟙 E) (fun _ _ => rfl) = 𝟙 (equivariantChains G E) := by
  ext n c
  exact congrArg (fun f => (f.f n).hom c)
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map_id E)

/-- Actual Hom-cochain pullback preserves contravariant composition. -/
theorem cochainPullback_comp (F : E ⟶ E') (H : E' ⟶ E'')
    (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
    (hH : ∀ (g : G) (x : E'), H (g • x) = g • H x) (V : Rep.{0} ℚ G) :
    cochainPullback (F ≫ H) (fun g x => by change H (F (g • x)) = g • H (F x); rw [hF,hH]) V =
      cochainPullback H hH V ≫ cochainPullback F hF V := by
  change EquivariantSingularSmall.homPullback (chainMap (F ≫ H) _) V = _
  rw [chainMap_comp,EquivariantSingularSmall.homPullback_comp]
  rfl

/-- Actual Hom-cochain pullback preserves identity maps. -/
theorem cochainPullback_id (V : Rep.{0} ℚ G) :
    cochainPullback (𝟙 E) (fun _ _ => rfl) V = 𝟙 _ := by
  change EquivariantSingularSmall.homPullback (chainMap (𝟙 E) _) V = _
  rw [chainMap_id]
  ext n c
  exact Category.id_comp c

/-- Actual geometric local-cochain pullbacks compose, including their coefficient transports. -/
theorem localPullback_comp (p : E ⟶ B) (p' : E' ⟶ B') (p'' : E'' ⟶ B'')
    (F : E ⟶ E') (H : E' ⟶ E'') (f : B ⟶ B') (h : B' ⟶ B'')
    (hs : F ≫ p' = p ≫ f) (ht : H ≫ p'' = p' ≫ h)
    (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
    (hp'' : IsQuotientCoveringMap p'' G)
    (hF : ∀ (g : G) (x : E), F (g • x) = g • F x)
    (hH : ∀ (g : G) (x : E'), H (g • x) = g • H x) (V : Rep.{0} ℚ G) :
    localPullback p p'' (F ≫ H) (f ≫ h) (by rw [Category.assoc,ht,← Category.assoc,hs,Category.assoc])
      hp hp'' (fun g x => by change H (F (g • x)) = g • H (F x); rw [hF,hH]) V =
    localPullback p' p'' H h ht hp' hp'' hH V ≫ localPullback p p' F f hs hp hp' hF V := by
  apply (cancel_epi (cochainIso p'' hp'' V).hom).mp
  rw [← cochainIso_pullback,← Category.assoc,← cochainIso_pullback,Category.assoc,
    ← cochainIso_pullback,← Category.assoc,← cochainPullback_comp]

/-- The actual geometric identity pullback is the identity cochain map. -/
theorem localPullback_id (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (V : Rep.{0} ℚ G) :
    localPullback p p (𝟙 E) (𝟙 B) (by simp) hp hp (fun _ _ => rfl) V = 𝟙 _ := by
  apply (cancel_epi (cochainIso p hp V).hom).mp
  erw [← cochainIso_pullback,cochainPullback_id,Category.id_comp]

end TernaryPoly.SingularCoverNaturality
