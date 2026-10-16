module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.Derivative
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.RegularCurrent
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section


/-! Literal coefficient-valued regular currents defined by actual Bochner compact-test integrals. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory
open scoped Distributions
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (μ : Measure E) [IsLocallyFiniteMeasure μ]

/-- The actual scalar-test multiple of a locally continuous coefficient function is integrable. -/
theorem valuedRegular_test_integrable (Ω : TopologicalSpace.Opens E) (f : E → V)
    (hf : ContinuousOn f Ω) (φ : 𝓓(Ω, ℝ)) : Integrable (fun x => φ x • f x) μ := by
  have hc : Continuous (fun x => φ x • f x) :=
    (φ.continuous.continuousOn.smul hf).continuous_of_tsupport_subset Ω.isOpen
      ((tsupport_smul_subset_left φ f).trans φ.tsupport_subset)
  exact hc.integrable_of_hasCompactSupport φ.hasCompactSupport.smul_right

/-- The actual vector-valued current of a locally continuous coefficient function. -/
def valuedRegularCurrent (Ω : TopologicalSpace.Opens E) (f : E → V) (hf : ContinuousOn f Ω) :
    ValuedWeak (V := V) Ω where
  toFun φ := ∫ x, φ x • f x ∂μ
  map_add' φ ψ := by
    change (∫ x, (φ x + ψ x) • f x ∂μ) = _
    simp only [add_smul]
    exact integral_add (valuedRegular_test_integrable μ Ω f hf φ)
      (valuedRegular_test_integrable μ Ω f hf ψ)
  map_smul' c φ := by
    change (∫ x, (c * φ x) • f x ∂μ) = c • ∫ x, φ x • f x ∂μ
    simp only [mul_smul]
    exact integral_smul c _

@[simp] theorem valuedRegularCurrent_apply (Ω : TopologicalSpace.Opens E) (f : E → V)
    (hf : ContinuousOn f Ω) (φ : 𝓓(Ω, ℝ)) :
    valuedRegularCurrent μ Ω f hf φ = ∫ x, φ x • f x ∂μ := rfl

/-- Every genuine continuous coefficient linear map commutes with the literal regular current. -/
theorem valuedRegularCurrent_comp {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace V] [CompleteSpace W] (Ω : TopologicalSpace.Opens E) (L : V →L[ℝ] W) (f : E → V)
    (hf : ContinuousOn f Ω) :
    L.toLinearMap.comp (valuedRegularCurrent μ Ω f hf) =
      valuedRegularCurrent μ Ω (fun x => L (f x)) (L.continuous.comp_continuousOn hf) := by
  apply LinearMap.ext
  intro φ
  change L (∫ x, φ x • f x ∂μ) = ∫ x, φ x • L (f x) ∂μ
  exact (L.integral_comp_comm (valuedRegular_test_integrable μ Ω f hf φ)).symm.trans
    (integral_congr_ae (Filter.Eventually.of_forall (fun x => L.map_smul (φ x) (f x))))

/-- For scalar coefficients the Bochner current is the established scalar current. -/
theorem valuedRegularCurrent_scalar (Ω : TopologicalSpace.Opens E) (f : E → ℝ)
    (hf : ContinuousOn f Ω) : valuedRegularCurrent μ Ω f hf = scalarRegularCurrent μ Ω f hf := by
  apply LinearMap.ext
  intro φ
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm (φ x) (f x)))

end TernaryPoly.PolynomialFormWeakSmooth
