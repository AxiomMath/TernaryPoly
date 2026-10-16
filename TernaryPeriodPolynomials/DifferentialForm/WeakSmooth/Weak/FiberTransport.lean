module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Weak.Fiber

@[expose] public section


/-! Exact horizontal transport and last-coordinate rigidity of the actual weak fiber maps. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open scoped Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Constant-fiber current lifting commutes with actual horizontal weak derivatives. -/
theorem weakFiberLift_horizontal_derivative (Ω : TopologicalSpace.Opens E)
    (T : ScalarWeak Ω) (v : E) :
    scalarWeakDerivative (testCylinder Ω) (v, 0) (weakFiberLift Ω T) =
      weakFiberLift Ω (scalarWeakDerivative Ω v T) := by
  apply LinearMap.ext
  intro f
  change -T (fiberTestIntegral Ω (TestFunction.lineDerivCLM ℝ (v, 0) f)) =
    -T (TestFunction.lineDerivCLM ℝ v (fiberTestIntegral Ω f))
  rw [fiberTestIntegral_horizontal_derivative]

omit [FiniteDimensional ℝ E] in
/-- The actual bump restriction commutes with horizontal weak differentiation. -/
theorem weakFiberRestriction_horizontal_derivative (Ω : TopologicalSpace.Opens E)
    (T : ScalarWeak (testCylinder Ω)) (v : E) :
    weakFiberRestriction Ω (scalarWeakDerivative (testCylinder Ω) (v, 0) T) =
      scalarWeakDerivative Ω v (weakFiberRestriction Ω T) := by
  apply LinearMap.ext
  intro f
  change -T (TestFunction.lineDerivCLM ℝ (v, 0) (fiberTestSection Ω f)) =
    -T (fiberTestSection Ω (TestFunction.lineDerivCLM ℝ v f))
  rw [fiberTestSection_horizontal_derivative]

/-- The genuine weak primitive operator commutes with each horizontal weak derivative. -/
theorem weakFiberPrimitive_horizontal_derivative (Ω : TopologicalSpace.Opens E)
    (T : ScalarWeak (testCylinder Ω)) (v : E) :
    scalarWeakDerivative (testCylinder Ω) (v, 0) (weakFiberPrimitive Ω T) =
      weakFiberPrimitive Ω (scalarWeakDerivative (testCylinder Ω) (v, 0) T) := by
  apply LinearMap.ext
  intro f
  change -(-T (fiberTestHomotopy Ω (TestFunction.lineDerivCLM ℝ (v, 0) f))) =
    -(-T (TestFunction.lineDerivCLM ℝ (v, 0) (fiberTestHomotopy Ω f)))
  rw [fiberTestHomotopy_horizontal_derivative]

/-- Currents lifted constantly in the final coordinate have zero derivative there. -/
theorem weakFiberLift_last_derivative (Ω : TopologicalSpace.Opens E) (T : ScalarWeak Ω) :
    scalarWeakDerivative (testCylinder Ω) (0, 1) (weakFiberLift Ω T) = 0 := by
  apply LinearMap.ext
  intro f
  change -T (fiberTestIntegral Ω (TestFunction.lineDerivCLM ℝ (0, 1) f)) = 0
  rw [fiberTestIntegral_last_derivative, map_zero, neg_zero]

/-- Every current with vanishing final derivative is literally lifted from a unique base current. -/
theorem weakFiberLift_of_last_derivative_zero (Ω : TopologicalSpace.Opens E)
    (T : ScalarWeak (testCylinder Ω))
    (hT : scalarWeakDerivative (testCylinder Ω) (0, 1) T = 0) :
    T = weakFiberLift Ω (weakFiberRestriction Ω T) := by
  have h := weakFiberPrimitive_after_derivative Ω T
  rw [hT, map_zero] at h
  exact sub_eq_zero.mp h.symm

end TernaryPoly.PolynomialFormWeakSmooth
