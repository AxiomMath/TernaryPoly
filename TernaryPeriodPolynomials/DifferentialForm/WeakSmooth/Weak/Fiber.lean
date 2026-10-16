module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Fiber.HomotopyCommutation
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.ScalarWeak

@[expose] public section

/-! Literal transpose fiber homotopies on actual algebraic test currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open scoped Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Lift a current constantly in the last coordinate, by literal fiber integration on tests. -/
def weakFiberLift (Ω : TopologicalSpace.Opens E) :
    ScalarWeak Ω →ₗ[ℝ] ScalarWeak (testCylinder Ω) := (fiberTestIntegral Ω).dualMap

/-- The current restriction determined by the actual normalized bump insertion. -/
def weakFiberRestriction (Ω : TopologicalSpace.Opens E) :
    ScalarWeak (testCylinder Ω) →ₗ[ℝ] ScalarWeak Ω := (fiberTestSection Ω).dualMap

/-- The negative transpose of the genuine compact-test homotopy. -/
def weakFiberPrimitive (Ω : TopologicalSpace.Opens E) :
    ScalarWeak (testCylinder Ω) →ₗ[ℝ] ScalarWeak (testCylinder Ω) := -(fiberTestHomotopy Ω).dualMap

@[simp] theorem weakFiberLift_apply (Ω : TopologicalSpace.Opens E) (T : ScalarWeak Ω)
    (f : 𝓓(testCylinder Ω, ℝ)) : weakFiberLift Ω T f = T (fiberTestIntegral Ω f) := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem weakFiberRestriction_apply (Ω : TopologicalSpace.Opens E)
    (T : ScalarWeak (testCylinder Ω)) (f : 𝓓(Ω, ℝ)) :
    weakFiberRestriction Ω T f = T (fiberTestSection Ω f) := rfl

@[simp] theorem weakFiberPrimitive_apply (Ω : TopologicalSpace.Opens E)
    (T : ScalarWeak (testCylinder Ω)) (f : 𝓓(testCylinder Ω, ℝ)) :
    weakFiberPrimitive Ω T f = -T (fiberTestHomotopy Ω f) := rfl

/-- Constant current lifting has an actual left inverse and hence loses no information. -/
theorem weakFiberRestriction_lift (Ω : TopologicalSpace.Opens E) (T : ScalarWeak Ω) :
    weakFiberRestriction Ω (weakFiberLift Ω T) = T := by
  apply LinearMap.ext
  intro f
  change T (fiberTestIntegral Ω (fiberTestSection Ω f)) = T f
  rw [fiberTestIntegral_section]

theorem weakFiberLift_injective (Ω : TopologicalSpace.Opens E) :
    Function.Injective (weakFiberLift Ω) :=
  Function.LeftInverse.injective (weakFiberRestriction_lift Ω)

/-- Every algebraic current has an actual weak primitive in the final coordinate. -/
theorem weakFiberPrimitive_derivative (Ω : TopologicalSpace.Opens E)
    (T : ScalarWeak (testCylinder Ω)) :
    scalarWeakDerivative (testCylinder Ω) (0, 1) (weakFiberPrimitive Ω T) = T := by
  apply LinearMap.ext
  intro f
  change -(-T (fiberTestHomotopy Ω (TestFunction.lineDerivCLM ℝ (0, 1) f))) = T f
  rw [neg_neg, fiberTestHomotopy_last_derivative]

/-- The genuine weak homotopy identity includes the constant-fiber projection. -/
theorem weakFiberPrimitive_after_derivative (Ω : TopologicalSpace.Opens E)
    (T : ScalarWeak (testCylinder Ω)) :
    weakFiberPrimitive Ω (scalarWeakDerivative (testCylinder Ω) (0, 1) T) =
      T - weakFiberLift Ω (weakFiberRestriction Ω T) := by
  apply LinearMap.ext
  intro f
  change -(-T (TestFunction.lineDerivCLM ℝ (0, 1) (fiberTestHomotopy Ω f))) =
    T f - T (fiberTestSection Ω (fiberTestIntegral Ω f))
  rw [neg_neg, fiberTestHomotopy_derivative, map_sub]

end TernaryPoly.PolynomialFormWeakSmooth
