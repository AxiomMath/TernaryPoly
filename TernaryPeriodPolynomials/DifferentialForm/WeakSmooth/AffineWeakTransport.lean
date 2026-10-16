module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.AffineTestTransport
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Weak.One

@[expose] public section


/-! Exact algebraic-current transport under actual invertible affine coordinate maps. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open scoped Distributions
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Transpose inverse test transport. The geometric density normalization is a separate identity. -/
def scalarWeakAffineEquiv (e : E ≃L[ℝ] F) (a : F) (Ω : TopologicalSpace.Opens E) :
    ScalarWeak Ω ≃ₗ[ℝ] ScalarWeak (transportedTestDomain (affineTestHomeomorph e a) Ω) :=
  (affineTestEquiv e a Ω).symm.dualMap

@[simp] theorem scalarWeakAffineEquiv_apply (e : E ≃L[ℝ] F) (a : F)
    (Ω : TopologicalSpace.Opens E) (T : ScalarWeak Ω)
    (f : 𝓓(transportedTestDomain (affineTestHomeomorph e a) Ω, ℝ)) :
    scalarWeakAffineEquiv e a Ω T f = T ((affineTestEquiv e a Ω).symm f) := rfl

/-- Weak directional derivatives transform by the actual linear coordinate map. -/
theorem scalarWeakAffineEquiv_derivative (e : E ≃L[ℝ] F) (a : F)
    (Ω : TopologicalSpace.Opens E) (T : ScalarWeak Ω) (v : E) :
    scalarWeakDerivative (transportedTestDomain (affineTestHomeomorph e a) Ω) (e v)
      (scalarWeakAffineEquiv e a Ω T) =
    scalarWeakAffineEquiv e a Ω (scalarWeakDerivative Ω v T) := by
  apply LinearMap.ext
  intro f
  change -T ((affineTestEquiv e a Ω).symm (TestFunction.lineDerivCLM ℝ (e v) f)) =
    -T (TestFunction.lineDerivCLM ℝ v ((affineTestEquiv e a Ω).symm f))
  rw [affineTestEquiv_symm_derivative]

/-- The actual affine equivalence of weak directional one-forms. -/
def weakOneAffineEquiv (e : E ≃L[ℝ] F) (a : F) (Ω : TopologicalSpace.Opens E) :
    ScalarWeakOne Ω ≃ₗ[ℝ] ScalarWeakOne (transportedTestDomain (affineTestHomeomorph e a) Ω) :=
  LinearEquiv.arrowCongr e.toLinearEquiv (scalarWeakAffineEquiv e a Ω)

@[simp] theorem weakOneAffineEquiv_apply (e : E ≃L[ℝ] F) (a : F)
    (Ω : TopologicalSpace.Opens E) (w : ScalarWeakOne Ω) (v : F) :
    weakOneAffineEquiv e a Ω w v = scalarWeakAffineEquiv e a Ω (w (e.symm v)) := rfl

@[simp] theorem weakOneAffineEquiv_symm_apply (e : E ≃L[ℝ] F) (a : F)
    (Ω : TopologicalSpace.Opens E)
    (w : ScalarWeakOne (transportedTestDomain (affineTestHomeomorph e a) Ω)) (v : E) :
    (weakOneAffineEquiv e a Ω).symm w v = (scalarWeakAffineEquiv e a Ω).symm (w (e v)) := rfl

/-- The actual weak gradient is compatible with affine coordinate transport. -/
theorem weakOneAffineEquiv_gradient (e : E ≃L[ℝ] F) (a : F)
    (Ω : TopologicalSpace.Opens E) (T : ScalarWeak Ω) :
    weakOneAffineEquiv e a Ω (scalarWeakGradient Ω T) =
      scalarWeakGradient (transportedTestDomain (affineTestHomeomorph e a) Ω)
        (scalarWeakAffineEquiv e a Ω T) := by
  apply LinearMap.ext
  intro v
  have h := scalarWeakAffineEquiv_derivative e a Ω T (e.symm v)
  rw [e.apply_symm_apply] at h
  exact h.symm

end TernaryPoly.PolynomialFormWeakSmooth
