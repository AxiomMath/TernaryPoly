module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Test.Derivatives
public import Mathlib.LinearAlgebra.Dual.Defs

@[expose] public section


/-! Actual algebraic scalar currents on the Mathlib compact smooth test spaces. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open scoped Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Algebraic scalar functionals on actual compact smooth tests. Continuity is not assumed. -/
abbrev ScalarWeak (Ω : TopologicalSpace.Opens E) := Module.Dual ℝ 𝓓(Ω, ℝ)

/-- The literal weak derivative, with its integration-by-parts minus sign. -/
def scalarWeakDerivative (Ω : TopologicalSpace.Opens E) (v : E) :
    ScalarWeak Ω →ₗ[ℝ] ScalarWeak Ω :=
  - (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v (Ω := Ω) (F := ℝ)).toLinearMap.dualMap

@[simp] theorem scalarWeakDerivative_apply (Ω : TopologicalSpace.Opens E)
    (v : E) (T : ScalarWeak Ω) (f : 𝓓(Ω, ℝ)) :
    scalarWeakDerivative Ω v T f = -T (TestFunction.lineDerivCLM ℝ v f) := rfl

/-- Genuine constant-direction weak derivatives commute. -/
theorem scalarWeakDerivative_commute (Ω : TopologicalSpace.Opens E)
    (T : ScalarWeak Ω) (u v : E) :
    scalarWeakDerivative Ω u (scalarWeakDerivative Ω v T) =
      scalarWeakDerivative Ω v (scalarWeakDerivative Ω u T) := by
  apply LinearMap.ext
  intro f
  simp only [scalarWeakDerivative_apply, neg_neg]
  rw [testDerivative_commute Ω f v u]

end TernaryPoly.PolynomialFormWeakSmooth
