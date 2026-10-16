module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Cap.Leibniz
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.SpaceChains
public import TernaryPeriodPolynomials.Topology.SingularHomology.BarycentricSubdivisionHomotopyOperator

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCap
open CategoryTheory
open FreeActionLinearization CoveringSingularOrbits SingularLocalCoefficient SingularLocalHomology
open SingularCoverNaturality
open SphereOddDegree.AlexanderWhitney SphereOddDegree.AffineBarycentricSubdivision
open scoped Classical

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [ContinuousConstSMul G E]
  [MulAction G E'] [ContinuousConstSMul G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p' = p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
  (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (V : Rep.{0} ℚ G)

omit [ContinuousConstSMul G E] [ContinuousConstSMul G E'] in
/-- Literal cochain pullback evaluates on the actual image lift. -/
theorem vertexToFunction_pullback (n : ℕ) (φ : VertexCochain p' hp' V n)
    (τ : SingularSimplex E n) :
    vertexToFunction p hp (vertexPullback p p' F f hsquare hp hp' hF V n φ) τ =
      vertexToFunction p' hp' φ (projection F n τ) :=
  (vertexToFunction_lift p' hp' φ
    (liftMap p p' F f hsquare (⟨τ,rfl⟩ : Lifts p (projection p n τ)))).symm

variable [IsCancelSMul G E] [IsCancelSMul G E']

/-- Under the actual degree identifications, geometric chain pushforward is the genuine
coinvariant pushforward of lifted simplices. -/
theorem localSpaceMap_degreeEquiv (n : ℕ) (c : VertexChain p hp V n) :
    (degreeEquiv p' hp' V n).symm ((localSpaceMap F hF V p p' hp hp').f n c) =
      (coinvariantSpaceMap F hF V).f n ((degreeEquiv p hp V n).symm c) := by
  change (degreeEquiv p' hp' V n).symm
    ((degreeEquiv p' hp' V n) ((coinvariantSpaceMap F hF V).f n
      ((degreeEquiv p hp V n).symm c))) = _
  exact LinearEquiv.symm_apply_apply _ _

/-- Cap is natural for a genuine equivariant square of actual quotient covering spaces. -/
theorem cap_natural (a b : ℕ) (φ : VertexCochain p' hp' V a)
    (c : singularChainGroup ℚ B (a+b)) :
    (localSpaceMap F hF V p p' hp hp').f b
      (cap p hp V a b (vertexPullback p p' F f hsquare hp hp' hF V a φ) c) =
    cap p' hp' V a b φ ((singularChainMap ℚ f (a+b)).hom c) := by
  have hh : ((localSpaceMap F hF V p p' hp hp').f b).hom.comp
      (cap p hp V a b (vertexPullback p p' F f hsquare hp hp' hF V a φ)) =
      (cap p' hp' V a b φ).comp (singularChainMap ℚ f (a+b)).hom := by
    apply scalarChain_ext
    intro σ
    change (localSpaceMap F hF V p p' hp hp').f b
      (cap p hp V a b (vertexPullback p p' F f hsquare hp hp' hF V a φ)
        (chainGenerator ℚ B (a+b) σ)) =
      cap p' hp' V a b φ ((singularChainMap ℚ f (a+b)).hom (chainGenerator ℚ B (a+b) σ))
    rw [cap_generator, singularChainMap_generator, cap_generator]
    obtain ⟨τ,hτ⟩ := chosenLift p hp (a+b) σ
    cases hτ
    apply (degreeEquiv p' hp' V b).symm.injective
    rw [localSpaceMap_degreeEquiv, capSimplex_lift p hp V a b _ ⟨τ,rfl⟩,
      coinvariantSpaceMap_generator]
    have hr := capSimplex_lift p' hp' V a b φ
      (liftMap p p' F f hsquare (⟨τ,rfl⟩ : Lifts p (projection p (a+b) τ)))
    change _ = (degreeEquiv p' hp' V b).symm
      (capSimplex p' hp' V a b (projection f (a+b) (projection p (a+b) τ)) φ)
    rw [hr, projection_back, vertexToFunction_pullback, projection_front]
    rfl
  exact LinearMap.congr_fun hh c

end TernaryPoly.SingularLocalCap
