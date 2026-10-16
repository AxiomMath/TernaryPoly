module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.Regular
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.RegularDerivative

@[expose] public section


/-! Actual Bochner integration by parts for coefficient-valued regular currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory Measure
open scoped ContDiff Distributions
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual directional Frechet derivatives of a locally smooth coefficient function are continuous. -/
theorem valuedRegularDerivative_continuousOn (Ω : TopologicalSpace.Opens E) (f : E → V)
    (hf : ContDiffOn ℝ ∞ f Ω) (v : E) : ContinuousOn (fun x => fderiv ℝ f x v) Ω :=
  (hf.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply continuousOn_const

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsAddHaarMeasure μ]

/-- The literal weak derivative of a smooth vector-valued regular current is the regular current
of its literal directional Frechet derivative. -/
theorem valuedRegularCurrent_derivative (Ω : TopologicalSpace.Opens E) (f : E → V)
    (hf : ContDiffOn ℝ ∞ f Ω) (v : E) :
    valuedWeakDerivative Ω v (valuedRegularCurrent μ Ω f hf.continuousOn) =
      valuedRegularCurrent μ Ω (fun x => fderiv ℝ f x v)
        (valuedRegularDerivative_continuousOn Ω f hf v) := by
  apply LinearMap.ext
  intro φ
  have hdf : Integrable (fun x => fderiv ℝ φ x v • f x) μ := by
    simpa only [regularTestDerivative_apply] using
      valuedRegular_test_integrable μ Ω f hf.continuousOn
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ)
  have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hdf
    (valuedRegular_test_integrable μ Ω _ (valuedRegularDerivative_continuousOn Ω f hf v) φ)
    (valuedRegular_test_integrable μ Ω f hf.continuousOn φ)
    (fun x _ => (φ.contDiff.differentiable (by simp)).differentiableAt (x := x))
    (fun x hx => (hf.differentiableOn (by simp) x (φ.tsupport_subset hx)).differentiableAt
      (Ω.isOpen.mem_nhds (φ.tsupport_subset hx)))
  change -(∫ x, TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ x • f x ∂μ) = _
  simp only [regularTestDerivative_apply]
  exact hibp.symm

end TernaryPoly.PolynomialFormWeakSmooth
