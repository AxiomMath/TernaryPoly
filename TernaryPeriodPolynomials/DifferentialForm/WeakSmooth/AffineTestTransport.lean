module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Test.Transport
public import Mathlib.Tactic.Abel

@[expose] public section


/-! Exact affine transport of actual compact smooth tests and their directional derivatives. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open scoped ContDiff Distributions
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The literal invertible affine coordinate map `x ↦ e x + a`. -/
def affineTestHomeomorph (e : E ≃L[ℝ] F) (a : F) : E ≃ₜ F where
  toFun x := e x + a
  invFun y := e.symm (y - a)
  left_inv x := by simp
  right_inv y := by simp
  continuous_toFun := e.continuous.add continuous_const
  continuous_invFun := e.symm.continuous.comp (continuous_id.sub continuous_const)

theorem affineTestHomeomorph_contDiff (e : E ≃L[ℝ] F) (a : F) :
    ContDiff ℝ ∞ (affineTestHomeomorph e a) := e.contDiff.add contDiff_const

theorem affineTestHomeomorph_symm_contDiff (e : E ≃L[ℝ] F) (a : F) :
    ContDiff ℝ ∞ (affineTestHomeomorph e a).symm :=
  e.symm.contDiff.comp (contDiff_id.sub contDiff_const)

/-- Actual compact smooth test transport under the invertible affine map. -/
def affineTestEquiv (e : E ≃L[ℝ] F) (a : F) (Ω : TopologicalSpace.Opens E) :
    𝓓(Ω, ℝ) ≃ₗ[ℝ] 𝓓(transportedTestDomain (affineTestHomeomorph e a) Ω, ℝ) :=
  smoothTestEquiv (affineTestHomeomorph e a) (affineTestHomeomorph_contDiff e a)
    (affineTestHomeomorph_symm_contDiff e a) Ω

@[simp] theorem affineTestEquiv_apply (e : E ≃L[ℝ] F) (a : F) (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(Ω, ℝ)) (y : F) : affineTestEquiv e a Ω f y = f (e.symm (y - a)) := rfl

@[simp] theorem affineTestEquiv_symm_apply (e : E ≃L[ℝ] F) (a : F) (Ω : TopologicalSpace.Opens E)
    (g : 𝓓(transportedTestDomain (affineTestHomeomorph e a) Ω, ℝ)) (x : E) :
    (affineTestEquiv e a Ω).symm g x = g (e x + a) := rfl

/-- Constant-direction derivatives are transported by the actual linear part of the affine map. -/
theorem affineTestEquiv_derivative (e : E ≃L[ℝ] F) (a : F) (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(Ω, ℝ)) (v : E) :
    TestFunction.lineDerivCLM ℝ (e v) (affineTestEquiv e a Ω f) =
      affineTestEquiv e a Ω (TestFunction.lineDerivCLM ℝ v f) := by
  apply TestFunction.ext
  intro y
  simp only [TestFunction.lineDerivCLM_apply_of_le (n := ⊤) (k := ⊤) (by simp),
    affineTestEquiv_apply]
  change deriv (fun t : ℝ => f (e.symm (y + t • e v - a))) 0 =
    deriv (fun t : ℝ => f (e.symm (y - a) + t • v)) 0
  have he (t : ℝ) : e.symm (y + t • e v - a) = e.symm (y - a) + t • v := by
    rw [map_sub, map_add, map_smul, e.symm_apply_apply, map_sub]
    abel
  simp only [he]

/-- The inverse affine test map has the exact inverse derivative compatibility. -/
theorem affineTestEquiv_symm_derivative (e : E ≃L[ℝ] F) (a : F)
    (Ω : TopologicalSpace.Opens E)
    (g : 𝓓(transportedTestDomain (affineTestHomeomorph e a) Ω, ℝ)) (v : E) :
    (affineTestEquiv e a Ω).symm (TestFunction.lineDerivCLM ℝ (e v) g) =
      TestFunction.lineDerivCLM ℝ v ((affineTestEquiv e a Ω).symm g) := by
  apply (affineTestEquiv e a Ω).injective
  rw [LinearEquiv.apply_symm_apply, ← affineTestEquiv_derivative, LinearEquiv.apply_symm_apply]

end TernaryPoly.PolynomialFormWeakSmooth
