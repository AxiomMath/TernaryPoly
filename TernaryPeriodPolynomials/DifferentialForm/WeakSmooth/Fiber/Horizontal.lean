module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Fiber.Homotopy

@[expose] public section


/-! Horizontal differentiation commutes with the actual fiber integral and normalized section. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory SmoothLocalDeRham
open scoped ContDiff Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The directional derivative of the actual compact parameter integral is the integral
of the actual horizontal directional derivative. -/
theorem fiberTestIntegralRaw_lineDeriv {f : E × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : E) :
    lineDeriv ℝ (fiberTestIntegralRaw f) x v =
      ∫ t in (0 : ℝ)..1, lineDeriv ℝ f (x, t) (v, 0) := by
  have hd := hasFDerivAt_parameterIntegral isOpen_univ hf.contDiffOn
    (x := x) (by intro t ht; trivial)
  change HasFDerivAt (fiberTestIntegralRaw f) _ x at hd
  rw [hd.differentiableAt.lineDeriv_eq_fderiv, hd.fderiv]
  have hp := parameterDerivative_smooth isOpen_univ hf.contDiffOn
  rw [contDiffOn_univ] at hp
  have hpi : IntervalIntegrable (fun t : ℝ => parameterDerivative f (x, t)) volume 0 1 :=
    (hp.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  rw [ContinuousLinearMap.intervalIntegral_apply hpi v]
  apply intervalIntegral.integral_congr
  intro t ht
  exact ((hf.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv).symm

/-- Actual compact-test fiber integration commutes with each horizontal test derivative. -/
theorem fiberTestIntegral_horizontal_derivative (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(testCylinder Ω, ℝ)) (v : E) :
    fiberTestIntegral Ω (TestFunction.lineDerivCLM ℝ (v, 0) f) =
      TestFunction.lineDerivCLM ℝ v (fiberTestIntegral Ω f) := by
  apply TestFunction.ext
  intro x
  rw [TestFunction.lineDerivCLM_apply_of_le (n := ⊤) (k := ⊤) (by simp)]
  change (∫ t in (0 : ℝ)..1, (TestFunction.lineDerivCLM ℝ (v, 0) f :
    𝓓(testCylinder Ω, ℝ)) (x, t)) = lineDeriv ℝ (fiberTestIntegralRaw f) x v
  simp_rw [TestFunction.lineDerivCLM_apply_of_le (n := ⊤) (k := ⊤) (by simp)]
  exact (fiberTestIntegralRaw_lineDeriv f.contDiff x v).symm

omit [FiniteDimensional ℝ E] in
/-- Actual tensor insertion of the fixed bump commutes with every horizontal derivative. -/
theorem fiberTestSection_horizontal_derivative (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(Ω, ℝ)) (v : E) :
    TestFunction.lineDerivCLM ℝ (v, 0) (fiberTestSection Ω f) =
      fiberTestSection Ω (TestFunction.lineDerivCLM ℝ v f) := by
  apply TestFunction.ext
  intro p
  simp only [TestFunction.lineDerivCLM_apply_of_le (n := ⊤) (k := ⊤) (by simp), fiberTestSection_apply]
  simp only [lineDeriv, Prod.smul_mk, smul_zero, fiberTestSection_apply, Prod.fst_add, Prod.snd_add, add_zero]
  exact deriv_mul_const_field (𝕜 := ℝ) (u := fun t : ℝ => f (p.1 + t • v))
    (x := 0) (unitTest p.2)

end TernaryPoly.PolynomialFormWeakSmooth
