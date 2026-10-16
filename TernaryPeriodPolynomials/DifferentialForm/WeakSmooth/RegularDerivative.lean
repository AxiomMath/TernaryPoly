module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.RegularCurrent
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn

@[expose] public section


/-! The derivative of a genuine smooth scalar current is the current of the genuine derivative. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory Measure
open scoped ContDiff Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual directional derivative of a locally smooth coefficient is continuous on its domain. -/
theorem regularDerivative_continuousOn (Ω : TopologicalSpace.Opens E) (f : E → ℝ)
    (hf : ContDiffOn ℝ ∞ f Ω) (v : E) :
    ContinuousOn (fun x => fderiv ℝ f x v) Ω :=
  (hf.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply continuousOn_const

/-- The literal test derivative equals the genuine directional Frechet derivative. -/
theorem regularTestDerivative_apply (Ω : TopologicalSpace.Opens E) (φ : 𝓓(Ω, ℝ))
    (v x : E) : TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ x = fderiv ℝ φ x v := by
  rw [TestFunction.lineDerivCLM_apply_of_le (n := ⊤) (k := ⊤) (by simp)]
  exact (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsAddHaarMeasure μ]

/-- Integration by parts against genuine compact smooth tests identifies weak and smooth
scalar differentiation on the actual domain, without any global regularity assumption on f. -/
theorem scalarRegularCurrent_derivative (Ω : TopologicalSpace.Opens E) (f : E → ℝ)
    (hf : ContDiffOn ℝ ∞ f Ω) (v : E) :
    scalarWeakDerivative Ω v (scalarRegularCurrent μ Ω f hf.continuousOn) =
      scalarRegularCurrent μ Ω (fun x => fderiv ℝ f x v)
        (regularDerivative_continuousOn Ω f hf v) := by
  apply LinearMap.ext
  intro φ
  have hfg' : Integrable (fun x => f x * fderiv ℝ φ x v) μ := by
    simpa only [regularTestDerivative_apply] using
      regularCurrent_test_integrable μ Ω f hf.continuousOn
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (regularCurrent_test_integrable μ Ω _ (regularDerivative_continuousOn Ω f hf v) φ)
    hfg' (regularCurrent_test_integrable μ Ω f hf.continuousOn φ)
    (fun x hx => (hf.differentiableOn (by simp) x (φ.tsupport_subset hx)).differentiableAt
      (Ω.isOpen.mem_nhds (φ.tsupport_subset hx)))
    (fun x _ => (φ.contDiff.differentiable (by simp)).differentiableAt (x := x))
  change -(∫ x, f x * TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ x ∂μ) = ∫ x, fderiv ℝ f x v * φ x ∂μ
  simp only [regularTestDerivative_apply, hibp, neg_neg]

end TernaryPoly.PolynomialFormWeakSmooth
