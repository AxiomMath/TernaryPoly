module

public import TernaryPeriodPolynomials.Topology.Covering.CoefficientEvaluation
public import Mathlib.LinearAlgebra.BilinearMap

@[expose] public section


noncomputable section
namespace TernaryPoly.CoveringSingularOrbits
open CategoryTheory
variable {G : Type} [Group G] {E B : TopCat} [MulAction G E]
variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [DistribMulAction G V]
    [SMulCommClass G ℚ V] [AddCommGroup W] [Module ℚ W] [DistribMulAction G W]
    [SMulCommClass G ℚ W]

/-- A chosen point of the actual, nonempty covering fiber. -/
def chosenFiberPoint (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (b : B) : Fiber p b :=
  ⟨(hp.surjective b).choose,(hp.surjective b).choose_spec⟩

/-- The actual rational fiber pairing, evaluated at a chosen lift. -/
def coefficientPairing (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    (β : V →ₗ[ℚ] W →ₗ[ℚ] ℚ) (b : B) :
    FiberCoefficient p hp V b →ₗ[ℚ] FiberCoefficient p hp W b →ₗ[ℚ] ℚ :=
  β.compl₁₂ (coefficientEvaluationLinearEquiv p hp (chosenFiberPoint p hp b)).toLinearMap
    (coefficientEvaluationLinearEquiv p hp (chosenFiberPoint p hp b)).toLinearMap

omit [SMulCommClass G ℚ V] [SMulCommClass G ℚ W] in
/-- An invariant coefficient pairing is independent of the chosen actual lift. -/
theorem coefficientPairing_at (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    (β : V →ₗ[ℚ] W →ₗ[ℚ] ℚ)
    (hβ : ∀ (g : G) v w,β (g • v) (g • w)=β v w)
    {b : B} (c : FiberCoefficient p hp V b) (d : FiberCoefficient p hp W b) (e : Fiber p b) :
    coefficientPairing p hp β b c d=β (c.val e) (d.val e) := by
  let e₀ := chosenFiberPoint p hp b
  let g := fiberCoordinate p hp e₀ e
  have he : fiberSmul p hp g e₀=e := Subtype.ext (hp.fiberEquivGroup_smul_self e₀)
  change β (c.val e₀) (d.val e₀)=β (c.val e) (d.val e)
  calc
    β (c.val e₀) (d.val e₀)=β (g • c.val e₀) (g • d.val e₀) := (hβ g _ _).symm
    _ = β (c.val (fiberSmul p hp g e₀)) (d.val (fiberSmul p hp g e₀)) :=
      congrArg₂ (fun v w => β v w) (c.property g e₀).symm (d.property g e₀).symm
    _ = β (c.val e) (d.val e) := congrArg (fun u : Fiber p b => β (c.val u) (d.val u)) he

omit [SMulCommClass G ℚ V] [SMulCommClass G ℚ W] in
/-- The pairing is parallel for the actual path-lift local-system transports. -/
theorem coefficientPairing_transport (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    (β : V →ₗ[ℚ] W →ₗ[ℚ] ℚ)
    (hβ : ∀ (g : G) v w,β (g • v) (g • w)=β v w)
    {x y : B} (γ : Path.Homotopic.Quotient x y)
    (c : FiberCoefficient p hp V x) (d : FiberCoefficient p hp W x) :
    coefficientPairing p hp β y (coefficientTransport p hp γ c) (coefficientTransport p hp γ d)=
      coefficientPairing p hp β x c d := by
  rw [coefficientPairing_at p hp β hβ _ _
    (fiberTransport p hp γ (chosenFiberPoint p hp x)),
    coefficientTransport_apply_transport,coefficientTransport_apply_transport]
  rfl

omit [SMulCommClass G ℚ V] [SMulCommClass G ℚ W] in
/-- Left nondegeneracy of the coefficient pairing passes to every actual fiber. -/
theorem coefficientPairing_nondegenerate_left (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    (β : V →ₗ[ℚ] W →ₗ[ℚ] ℚ) (hβ : ∀ v, (∀ w,β v w=0) → v=0)
    (b : B) (c : FiberCoefficient p hp V b)
    (hc : ∀ d : FiberCoefficient p hp W b,coefficientPairing p hp β b c d=0) : c=0 := by
  apply (coefficientEvaluationLinearEquiv p hp (chosenFiberPoint p hp b)).injective
  change c.val (chosenFiberPoint p hp b)=0
  apply hβ
  intro w
  obtain ⟨d,hd⟩ := (coefficientEvaluationLinearEquiv (V := W) p hp
    (chosenFiberPoint p hp b)).surjective w
  exact (congrArg (β (c.val (chosenFiberPoint p hp b))) hd).symm.trans (hc d)

end TernaryPoly.CoveringSingularOrbits
