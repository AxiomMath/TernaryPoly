module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Fiber.PrimitiveSupport
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section


/-! The actual compact-test primitive on the kernel of fiber integration. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory
open scoped ContDiff Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The zero-mass antiderivative as a genuine linear map of actual compact-test spaces. -/
def fiberTestPrimitive (Ω : TopologicalSpace.Opens E) :
    LinearMap.ker (fiberTestIntegral Ω) →ₗ[ℝ] 𝓓(testCylinder Ω, ℝ) where
  toFun f :=
    { toFun := fiberTestPrimitiveRaw f.val
      contDiff' := fiberTestPrimitiveRaw_contDiff f.val.contDiff
      hasCompactSupport' := (fiberTestPrimitiveRaw_support Ω f.val f.property).1
      tsupport_subset' := (fiberTestPrimitiveRaw_support Ω f.val f.property).2 }
  map_add' f g := by
    apply TestFunction.ext
    intro p
    exact intervalIntegral.integral_add
      ((f.val.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 p.2)
      ((g.val.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 p.2)
  map_smul' c f := by
    apply TestFunction.ext
    intro p
    exact intervalIntegral.integral_smul c (fun t => f.val (p.1, t))

@[simp] theorem fiberTestPrimitive_apply (Ω : TopologicalSpace.Opens E)
    (f : LinearMap.ker (fiberTestIntegral Ω)) (p : E × ℝ) :
    fiberTestPrimitive Ω f p = ∫ t in (0 : ℝ)..p.2, f.val (p.1, t) := rfl

omit [FiniteDimensional ℝ E] in
/-- Last-coordinate directional differentiation is ordinary differentiation of that slice. -/
theorem lineDeriv_last_eq_deriv {f : E × ℝ → ℝ} (x : E) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x, t)) :
    lineDeriv ℝ f (x, t) (0, 1) = deriv (fun s => f (x, s)) t := by
  rw [hf.lineDeriv_eq_fderiv]
  exact (hf.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))).deriv.symm

/-- The actual compact primitive is a right inverse of the last-coordinate test derivative. -/
theorem fiberTestPrimitive_derivative (Ω : TopologicalSpace.Opens E)
    (f : LinearMap.ker (fiberTestIntegral Ω)) :
    TestFunction.lineDerivCLM ℝ (0, 1) (fiberTestPrimitive Ω f) = f.val := by
  apply TestFunction.ext
  intro p
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  rw [lineDeriv_last_eq_deriv p.1 p.2
    ((fiberTestPrimitive Ω f).contDiff.differentiable (by simp)).differentiableAt]
  exact (fiberTestPrimitiveRaw_hasDerivAt f.val.continuous p.1 p.2).deriv

end TernaryPoly.PolynomialFormWeakSmooth
