module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Coefficients
public import TernaryPeriodPolynomials.Topology.Singular.CoverNaturalityCochains

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalHomology
open CategoryTheory FreeActionLinearization CoveringSingularOrbits SingularCoverNaturality
open scoped Classical

variable {G : Type} [Group G] {E E' B B' : TopCat.{0}}
  [MulAction G E] [MulAction G E']
  (p : E ⟶ B) (p' : E' ⟶ B') (F : E ⟶ E') (f : B ⟶ B')
  (hsquare : F ≫ p' = p ≫ f)
  (hp : IsQuotientCoveringMap p G) (hp' : IsQuotientCoveringMap p' G)
  (hF : ∀ (g : G) (x : E), F (g • x) = g • F x) (V : Rep.{0} ℚ G)

/-- For a square of quotient covers with the same group, actual fiber-coefficient pullback is bijective. -/
theorem coefficientPullback_bijective (b : B) :
    Function.Bijective (coefficientPullback p p' F f hsquare hp hp' hF V b) := by
  obtain ⟨e, he⟩ := hp.surjective b
  let e₀ : Fiber p b := ⟨e, he⟩
  let e₁ := fiberMap p p' F f hsquare e₀
  constructor
  · intro c d h
    apply (coefficientEvaluationLinearEquiv p' hp' e₁).injective
    exact congrArg (fun z : FiberCoefficient p hp V b => z.val e₀) h
  · intro c
    refine ⟨(coefficientEvaluationLinearEquiv p' hp' e₁).symm (c.val e₀), ?_⟩
    apply (coefficientEvaluationLinearEquiv p hp e₀).injective
    change (coefficientEvaluationLinearEquiv p' hp' e₁)
      ((coefficientEvaluationLinearEquiv p' hp' e₁).symm (c.val e₀)) = c.val e₀
    exact LinearEquiv.apply_symm_apply _ _

/-- Covariant coefficient transport through the actual fiber map, as the inverse of literal pullback. -/
def coefficientPushforward (b : B) :
    FiberCoefficient p hp V b ≃ₗ[ℚ] FiberCoefficient p' hp' V (f b) :=
  (LinearEquiv.ofBijective (coefficientPullback p p' F f hsquare hp hp' hF V b)
    (coefficientPullback_bijective p p' F f hsquare hp hp' hF V b)).symm

/-- The pushed coefficient has the original value at each actual mapped fiber point. -/
theorem coefficientPushforward_apply (b : B) (c : FiberCoefficient p hp V b) (e : Fiber p b) :
    (coefficientPushforward p p' F f hsquare hp hp' hF V b c).val
      (fiberMap p p' F f hsquare e) = c.val e :=
  congrArg (fun z : FiberCoefficient p hp V b => z.val e)
    ((coefficientPushforward p p' F f hsquare hp hp' hF V b).symm_apply_apply c)

/-- Actual coefficient pushforward is compatible with genuine parallel transport. -/
theorem coefficientPushforward_transport {x y : B} (γ : Path.Homotopic.Quotient x y)
    (c : FiberCoefficient p hp V x) :
    coefficientPushforward p p' F f hsquare hp hp' hF V y (coefficientTransportLinear p hp γ c) =
      coefficientTransportLinear p' hp' (γ.map f.hom)
        (coefficientPushforward p p' F f hsquare hp hp' hF V x c) := by
  apply (coefficientPushforward p p' F f hsquare hp hp' hF V y).symm.injective
  change coefficientPullback p p' F f hsquare hp hp' hF V y
      (coefficientPushforward p p' F f hsquare hp hp' hF V y (coefficientTransportLinear p hp γ c)) =
    coefficientPullback p p' F f hsquare hp hp' hF V y
      (coefficientTransportLinear p' hp' (γ.map f.hom)
        (coefficientPushforward p p' F f hsquare hp hp' hF V x c))
  rw [coefficientPullback_transport p p' F f hsquare hp hp' hF V γ]
  change (coefficientPushforward p p' F f hsquare hp hp' hF V y).symm
      (coefficientPushforward p p' F f hsquare hp hp' hF V y (coefficientTransportLinear p hp γ c)) =
    coefficientTransportLinear p hp γ ((coefficientPushforward p p' F f hsquare hp hp' hF V x).symm
      (coefficientPushforward p p' F f hsquare hp hp' hF V x c))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

end TernaryPoly.SingularLocalHomology
