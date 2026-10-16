module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Weak.One
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Weak.FiberTransport

@[expose] public section


/-! Actual reduction of a closed weak one-form on a cylinder to the base domain. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open scoped Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Subtract the actual weak primitive of the vertical component and retain horizontal directions. -/
def weakOneHorizontalResidual (Ω : TopologicalSpace.Opens E)
    (w : ScalarWeakOne (testCylinder Ω)) : E →ₗ[ℝ] ScalarWeak (testCylinder Ω) :=
  w.comp (LinearMap.inl ℝ E ℝ) -
    (scalarWeakGradient (testCylinder Ω) (weakFiberPrimitive Ω (w (0, 1)))).comp
      (LinearMap.inl ℝ E ℝ)

@[simp] theorem weakOneHorizontalResidual_apply (Ω : TopologicalSpace.Opens E)
    (w : ScalarWeakOne (testCylinder Ω)) (v : E) :
    weakOneHorizontalResidual Ω w v = w (v, 0) -
      scalarWeakDerivative (testCylinder Ω) (v, 0) (weakFiberPrimitive Ω (w (0, 1))) := rfl

/-- Restrict the actual horizontal residual to an actual base weak one-form. -/
def weakOneBase (Ω : TopologicalSpace.Opens E)
    (w : ScalarWeakOne (testCylinder Ω)) : ScalarWeakOne Ω :=
  (weakFiberRestriction Ω).comp (weakOneHorizontalResidual Ω w)

@[simp] theorem weakOneBase_apply (Ω : TopologicalSpace.Opens E)
    (w : ScalarWeakOne (testCylinder Ω)) (v : E) :
    weakOneBase Ω w v = weakFiberRestriction Ω (weakOneHorizontalResidual Ω w v) := rfl

/-- Closedness makes every horizontal residual independent of the last coordinate. -/
theorem weakOneHorizontalResidual_last_zero (Ω : TopologicalSpace.Opens E)
    (w : ScalarWeakOne (testCylinder Ω)) (hw : IsClosedScalarWeakOne (testCylinder Ω) w)
    (v : E) :
    scalarWeakDerivative (testCylinder Ω) (0, 1) (weakOneHorizontalResidual Ω w v) = 0 := by
  rw [weakOneHorizontalResidual_apply, map_sub, hw (0, 1) (v, 0),
    scalarWeakDerivative_commute (testCylinder Ω) (weakFiberPrimitive Ω (w (0, 1))) (0, 1) (v, 0),
    weakFiberPrimitive_derivative, sub_self]

/-- The actual horizontal residual is exactly the lift of the actual base one-form. -/
theorem weakOneHorizontalResidual_lift (Ω : TopologicalSpace.Opens E)
    (w : ScalarWeakOne (testCylinder Ω)) (hw : IsClosedScalarWeakOne (testCylinder Ω) w)
    (v : E) : weakOneHorizontalResidual Ω w v = weakFiberLift Ω (weakOneBase Ω w v) :=
  weakFiberLift_of_last_derivative_zero Ω (weakOneHorizontalResidual Ω w v)
    (weakOneHorizontalResidual_last_zero Ω w hw v)

/-- The literal residual remains closed in every pair of horizontal directions. -/
theorem weakOneHorizontalResidual_closed (Ω : TopologicalSpace.Opens E)
    (w : ScalarWeakOne (testCylinder Ω)) (hw : IsClosedScalarWeakOne (testCylinder Ω) w)
    (u v : E) :
    scalarWeakDerivative (testCylinder Ω) (u, 0) (weakOneHorizontalResidual Ω w v) =
      scalarWeakDerivative (testCylinder Ω) (v, 0) (weakOneHorizontalResidual Ω w u) := by
  rw [weakOneHorizontalResidual_apply, weakOneHorizontalResidual_apply, map_sub, map_sub,
    hw (u, 0) (v, 0), scalarWeakDerivative_commute (testCylinder Ω)
      (weakFiberPrimitive Ω (w (0, 1))) (u, 0) (v, 0)]

/-- The actual reduced base one-form is closed. -/
theorem weakOneBase_closed (Ω : TopologicalSpace.Opens E)
    (w : ScalarWeakOne (testCylinder Ω)) (hw : IsClosedScalarWeakOne (testCylinder Ω) w) :
    IsClosedScalarWeakOne Ω (weakOneBase Ω w) := by
  intro u v
  rw [weakOneBase_apply, weakOneBase_apply, ← weakFiberRestriction_horizontal_derivative,
    ← weakFiberRestriction_horizontal_derivative, weakOneHorizontalResidual_closed Ω w hw]

end TernaryPoly.PolynomialFormWeakSmooth
