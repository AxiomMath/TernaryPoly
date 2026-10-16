module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Weak.OneReduction
public import Mathlib.Tactic.Abel

@[expose] public section

/-! Genuine inductive Poincare exactness for actual weak one-forms on product boxes. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open scoped Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Actual weak one-form exactness on a base domain implies exactness on its genuine cylinder. -/
theorem scalarWeakOneExact_cylinder (Ω : TopologicalSpace.Opens E)
    (hΩ : ScalarWeakOneExact Ω) : ScalarWeakOneExact (testCylinder Ω) := by
  intro w hw
  obtain ⟨S, hS⟩ := hΩ (weakOneBase Ω w) (weakOneBase_closed Ω w hw)
  let T := weakFiberPrimitive Ω (w (0, 1)) + weakFiberLift Ω S
  have hh (v : E) : scalarWeakGradient (testCylinder Ω) T (v, 0) = w (v, 0) := by
    have hv : scalarWeakDerivative Ω v S = weakOneBase Ω w v :=
      congrArg (fun z : ScalarWeakOne Ω => z v) hS
    change scalarWeakDerivative (testCylinder Ω) (v, 0)
      (weakFiberPrimitive Ω (w (0, 1)) + weakFiberLift Ω S) = w (v, 0)
    rw [map_add, weakFiberLift_horizontal_derivative, hv,
      ← weakOneHorizontalResidual_lift Ω w hw v, weakOneHorizontalResidual_apply]
    abel
  have hv : scalarWeakGradient (testCylinder Ω) T (0, 1) = w (0, 1) := by
    change scalarWeakDerivative (testCylinder Ω) (0, 1)
      (weakFiberPrimitive Ω (w (0, 1)) + weakFiberLift Ω S) = w (0, 1)
    rw [map_add, weakFiberPrimitive_derivative, weakFiberLift_last_derivative, add_zero]
  refine ⟨T, ?_⟩
  apply LinearMap.ext
  intro p
  have hp : p = (p.1, 0) + p.2 • ((0 : E), (1 : ℝ)) := by ext <;> simp
  rw [hp, map_add, map_smul, hh, hv, map_add, map_smul]

omit [FiniteDimensional ℝ E] in
/-- The actual zero-dimensional base has no nonzero tangent directions. -/
theorem scalarWeakOneExact_of_subsingleton [Subsingleton E] (Ω : TopologicalSpace.Opens E) :
    ScalarWeakOneExact Ω := by
  intro w _
  refine ⟨0, ?_⟩
  apply LinearMap.ext
  intro v
  have hv : v = 0 := Subsingleton.elim _ _
  rw [hv, map_zero, map_zero]

end TernaryPoly.PolynomialFormWeakSmooth
