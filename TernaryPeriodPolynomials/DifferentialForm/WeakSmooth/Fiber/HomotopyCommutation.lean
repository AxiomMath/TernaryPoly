module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Fiber.Horizontal
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Test.Derivatives

@[expose] public section


/-! The actual compact-test fiber homotopy commutes with all horizontal derivatives. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open scoped Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The last-coordinate derivative of actual compact tests is injective. -/
theorem lastTestDerivative_injective (Ω : TopologicalSpace.Opens E) :
    Function.Injective (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ ((0 : E), 1)
      (Ω := testCylinder Ω) (F := ℝ)) :=
  Function.LeftInverse.injective (fiberTestHomotopy_last_derivative Ω)

/-- Horizontal differentiation commutes with the genuine compact-test antiderivative homotopy. -/
theorem fiberTestHomotopy_horizontal_derivative (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(testCylinder Ω, ℝ)) (v : E) :
    TestFunction.lineDerivCLM ℝ (v, 0) (fiberTestHomotopy Ω f) =
      fiberTestHomotopy Ω (TestFunction.lineDerivCLM ℝ (v, 0) f) := by
  apply lastTestDerivative_injective Ω
  rw [testDerivative_commute (testCylinder Ω) (fiberTestHomotopy Ω f) ((0 : E), 1) (v, 0)]
  rw [fiberTestHomotopy_derivative, fiberTestHomotopy_derivative]
  rw [map_sub, fiberTestSection_horizontal_derivative, fiberTestIntegral_horizontal_derivative]

end TernaryPoly.PolynomialFormWeakSmooth
