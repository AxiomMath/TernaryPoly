module

public import TernaryPeriodPolynomials.Topology.Covering.CoefficientPairing
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

noncomputable section
namespace TernaryPoly.CoveringSingularOrbits
open CategoryTheory
variable {G : Type} [Group G] {E B : TopCat} [MulAction G E]
variable {V : Type*} [AddCommGroup V] [Module ℚ V] [DistribMulAction G V]
    [SMulCommClass G ℚ V]

/-- The literal contragredient action on the rational algebraic dual. -/
@[instance_reducible] def contragredientAction : DistribMulAction G (Module.Dual ℚ V) where
  smul g φ := φ.comp (DistribMulAction.toLinearEquiv ℚ V g⁻¹).toLinearMap
  one_smul φ := by
    ext v
    change φ ((1 : G)⁻¹ • v)=φ v
    rw [inv_one,one_smul]
  mul_smul g h φ := by
    ext v
    change φ ((g*h)⁻¹ • v)=φ (h⁻¹ • (g⁻¹ • v))
    rw [mul_inv_rev,mul_smul]
  smul_zero g := by ext v; rfl
  smul_add g φ ψ := by ext v; rfl

attribute [local instance] contragredientAction

theorem contragredientSMulComm : SMulCommClass G ℚ (Module.Dual ℚ V) where
  smul_comm _ _ _ := rfl

attribute [local instance] contragredientSMulComm

/-- The dual action evaluates by precomposition with the inverse actual coefficient action. -/
@[simp] theorem contragredient_apply (g : G) (φ : Module.Dual ℚ V) (v : V) :
    (g • φ) v=φ (g⁻¹ • v) := rfl

/-- Evaluation is an invariant pairing for the literal contragredient action. -/
theorem dualEvaluation_invariant (g : G) (φ : Module.Dual ℚ V) (v : V) :
    (g • φ) (g • v)=φ v := by simp

/-- The actual local system with contragredient rational coefficients. -/
def dualCoefficientLocalSystem (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) :
    FundamentalGroupoid B ⥤ ModuleCat ℚ :=
  coefficientLocalSystem (V := Module.Dual ℚ V) p hp

/-- Literal dual-fiber coefficients identify with the full algebraic dual of the original fiber. -/
def dualCoefficientFiberEquiv (p : E ⟶ B) (hp : IsQuotientCoveringMap p G) (b : B) :
    FiberCoefficient p hp (Module.Dual ℚ V) b ≃ₗ[ℚ] Module.Dual ℚ (FiberCoefficient p hp V b) :=
  (coefficientEvaluationLinearEquiv p hp (chosenFiberPoint p hp b)).trans
    (coefficientEvaluationLinearEquiv p hp (chosenFiberPoint p hp b)).dualMap

/-- This full duality is the actual pointwise evaluation pairing at any chosen lift. -/
theorem dualCoefficientFiberEquiv_apply (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {b : B} (φ : FiberCoefficient p hp (Module.Dual ℚ V) b)
    (c : FiberCoefficient p hp V b) (e : Fiber p b) :
    dualCoefficientFiberEquiv p hp b φ c=(φ.val e) (c.val e) :=
  coefficientPairing_at p hp (LinearMap.id : Module.Dual ℚ V →ₗ[ℚ] Module.Dual ℚ V)
    dualEvaluation_invariant φ c e

/-- The exact algebraic duality is parallel for actual path lifting, with no invariance premise. -/
theorem dualCoefficientFiberEquiv_transport (p : E ⟶ B) (hp : IsQuotientCoveringMap p G)
    {x y : B} (γ : Path.Homotopic.Quotient x y)
    (φ : FiberCoefficient p hp (Module.Dual ℚ V) x) (c : FiberCoefficient p hp V x) :
    dualCoefficientFiberEquiv p hp y (coefficientTransport p hp γ φ)
      (coefficientTransport p hp γ c)=dualCoefficientFiberEquiv p hp x φ c :=
  coefficientPairing_transport p hp (LinearMap.id : Module.Dual ℚ V →ₗ[ℚ] Module.Dual ℚ V)
    dualEvaluation_invariant γ φ c

end TernaryPoly.CoveringSingularOrbits
