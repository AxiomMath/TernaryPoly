module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Fiber.Primitive

@[expose] public section


/-! Exact fiberwise fundamental theorem identities for actual compact smooth tests. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory
open scoped ContDiff Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem cylinderTest_zero_left (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(testCylinder Ω, ℝ)) (x : E) : f (x, 0) = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => (f.tsupport_subset h).2.1.false)

omit [FiniteDimensional ℝ E] in
theorem cylinderTest_zero_right (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(testCylinder Ω, ℝ)) (x : E) : f (x, 1) = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => (f.tsupport_subset h).2.2.false)

omit [FiniteDimensional ℝ E] in
theorem cylinderTest_last_derivative_apply (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(testCylinder Ω, ℝ)) (x : E) (t : ℝ) :
    (TestFunction.lineDerivCLM ℝ (0, 1) f : 𝓓(testCylinder Ω, ℝ)) (x, t) =
      deriv (fun s => f (x, s)) t := by
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  exact lineDeriv_last_eq_deriv x t (f.contDiff.differentiable (by simp)).differentiableAt

/-- Integration kills the last-coordinate derivative of every actual compact test. -/
theorem fiberTestIntegral_last_derivative (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(testCylinder Ω, ℝ)) :
    fiberTestIntegral Ω (TestFunction.lineDerivCLM ℝ (0, 1) f) = 0 := by
  apply TestFunction.ext
  intro x
  have hs : ContDiff ℝ ∞ (fun t => f (x, t)) :=
    f.contDiff.comp (contDiff_const.prodMk contDiff_id)
  change (∫ t in (0 : ℝ)..1, (TestFunction.lineDerivCLM ℝ (0, 1) f :
    𝓓(testCylinder Ω, ℝ)) (x, t)) = 0
  simp_rw [cylinderTest_last_derivative_apply]
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun t _ => (hs.differentiable (by simp)).differentiableAt)
    ((hs.continuous_deriv (by simp)).intervalIntegrable 0 1)]
  rw [cylinderTest_zero_left, cylinderTest_zero_right, sub_self]

/-- The actual zero-based primitive of a compact test derivative is the original test. -/
theorem fiberTestPrimitive_last_derivative (Ω : TopologicalSpace.Opens E)
    (f : 𝓓(testCylinder Ω, ℝ)) :
    fiberTestPrimitive Ω ⟨TestFunction.lineDerivCLM ℝ (0, 1) f,
      fiberTestIntegral_last_derivative Ω f⟩ = f := by
  apply TestFunction.ext
  intro p
  have hs : ContDiff ℝ ∞ (fun t => f (p.1, t)) :=
    f.contDiff.comp (contDiff_const.prodMk contDiff_id)
  change (∫ t in (0 : ℝ)..p.2, (TestFunction.lineDerivCLM ℝ (0, 1) f :
    𝓓(testCylinder Ω, ℝ)) (p.1, t)) = f p
  simp_rw [cylinderTest_last_derivative_apply]
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun t _ => (hs.differentiable (by simp)).differentiableAt)
    ((hs.continuous_deriv (by simp)).intervalIntegrable 0 p.2)]
  rw [cylinderTest_zero_left, sub_zero]

end TernaryPoly.PolynomialFormWeakSmooth
