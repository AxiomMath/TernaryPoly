module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Fiber.Derivative
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Fiber.Section

@[expose] public section


/-! An actual compact-test homotopy for the final coordinate of a product chart. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory
open scoped Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Subtract the actual normalized bump times the actual fiber integral. -/
def fiberTestReduction (Ω : TopologicalSpace.Opens E) :
    𝓓(testCylinder Ω, ℝ) →ₗ[ℝ] LinearMap.ker (fiberTestIntegral Ω) :=
  LinearMap.codRestrict (LinearMap.ker (fiberTestIntegral Ω))
    (LinearMap.id - (fiberTestSection Ω).comp (fiberTestIntegral Ω)) (by
      intro f
      change fiberTestIntegral Ω (f - fiberTestSection Ω (fiberTestIntegral Ω f)) = 0
      rw [map_sub, fiberTestIntegral_section, sub_self])

@[simp] theorem fiberTestReduction_val (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(testCylinder Ω, ℝ)) :
    (fiberTestReduction Ω f).val = f - fiberTestSection Ω (fiberTestIntegral Ω f) := rfl

/-- The genuine compact antiderivative of the zero-mass test reduction. -/
def fiberTestHomotopy (Ω : TopologicalSpace.Opens E) :
    𝓓(testCylinder Ω, ℝ) →ₗ[ℝ] 𝓓(testCylinder Ω, ℝ) :=
  (fiberTestPrimitive Ω).comp (fiberTestReduction Ω)

/-- Differentiating this actual test homotopy is identity minus the actual fiber projection. -/
theorem fiberTestHomotopy_derivative (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(testCylinder Ω, ℝ)) :
    TestFunction.lineDerivCLM ℝ (0, 1) (fiberTestHomotopy Ω f) =
      f - fiberTestSection Ω (fiberTestIntegral Ω f) :=
  fiberTestPrimitive_derivative Ω (fiberTestReduction Ω f)

/-- Applying the actual test homotopy to a derivative recovers every original compact test. -/
theorem fiberTestHomotopy_last_derivative (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(testCylinder Ω, ℝ)) :
    fiberTestHomotopy Ω (TestFunction.lineDerivCLM ℝ (0, 1) f) = f := by
  have hr : fiberTestReduction Ω (TestFunction.lineDerivCLM ℝ (0, 1) f) =
      ⟨TestFunction.lineDerivCLM ℝ (0, 1) f, fiberTestIntegral_last_derivative Ω f⟩ := by
    apply Subtype.ext
    change TestFunction.lineDerivCLM ℝ (0, 1) f -
      fiberTestSection Ω (fiberTestIntegral Ω (TestFunction.lineDerivCLM ℝ (0, 1) f)) = _
    rw [fiberTestIntegral_last_derivative, map_zero, sub_zero]
  change fiberTestPrimitive Ω (fiberTestReduction Ω (TestFunction.lineDerivCLM ℝ (0, 1) f)) = f
  rw [hr]
  exact fiberTestPrimitive_last_derivative Ω f

end TernaryPoly.PolynomialFormWeakSmooth
