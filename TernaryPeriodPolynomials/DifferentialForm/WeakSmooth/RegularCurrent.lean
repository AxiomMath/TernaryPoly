module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.ScalarWeak
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import Mathlib.Topology.Algebra.IsUniformGroup.Order
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.ShrinkingLemma

@[expose] public section


/-! Actual scalar currents of locally continuous functions, with literal compact-test integration. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory
open scoped Distributions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsLocallyFiniteMeasure μ]

/-- A locally continuous coefficient times an actual compact test is globally integrable. -/
theorem regularCurrent_test_integrable (Ω : TopologicalSpace.Opens E) (f : E → ℝ)
    (hf : ContinuousOn f Ω) (φ : 𝓓(Ω, ℝ)) : Integrable (fun x => f x * φ x) μ := by
  have hc : Continuous (fun x => f x * φ x) :=
    (hf.mul φ.continuous.continuousOn).continuous_of_tsupport_subset Ω.isOpen
      (tsupport_mul_subset_right.trans φ.tsupport_subset)
  exact hc.integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left

/-- The genuine scalar current represented by a function continuous on the test domain. Values
outside that domain do not affect the integral, since actual test supports lie inside it. -/
def scalarRegularCurrent (Ω : TopologicalSpace.Opens E) (f : E → ℝ) (hf : ContinuousOn f Ω) :
    ScalarWeak Ω where
  toFun φ := ∫ x, f x * φ x ∂μ
  map_add' φ ψ := by
    change (∫ x, f x * (φ x + ψ x) ∂μ) = _
    simp only [mul_add]
    exact integral_add (regularCurrent_test_integrable μ Ω f hf φ)
      (regularCurrent_test_integrable μ Ω f hf ψ)
  map_smul' c φ := by
    change (∫ x, f x * (c * φ x) ∂μ) = c * ∫ x, f x * φ x ∂μ
    calc
      _ = ∫ x, c * (f x * φ x) ∂μ := integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
      _ = _ := integral_const_mul c _

@[simp] theorem scalarRegularCurrent_apply (Ω : TopologicalSpace.Opens E) (f : E → ℝ)
    (hf : ContinuousOn f Ω) (φ : 𝓓(Ω, ℝ)) :
    scalarRegularCurrent μ Ω f hf φ = ∫ x, f x * φ x ∂μ := rfl

theorem scalarRegularCurrent_congr (Ω : TopologicalSpace.Opens E) {f g : E → ℝ}
    (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω) (h : EqOn f g Ω) :
    scalarRegularCurrent μ Ω f hf = scalarRegularCurrent μ Ω g hg := by
  apply LinearMap.ext
  intro φ
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ (Ω : Set E)
  · rw [h hx]
  · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (φ.tsupport_subset ht))
    simp only [hz, mul_zero]

theorem scalarRegularCurrent_add (Ω : TopologicalSpace.Opens E) (f g : E → ℝ)
    (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω) :
    scalarRegularCurrent μ Ω (f + g) (hf.add hg) =
      scalarRegularCurrent μ Ω f hf + scalarRegularCurrent μ Ω g hg := by
  apply LinearMap.ext
  intro φ
  change (∫ x, (f x + g x) * φ x ∂μ) = _
  simp only [add_mul]
  exact integral_add (regularCurrent_test_integrable μ Ω f hf φ)
    (regularCurrent_test_integrable μ Ω g hg φ)

theorem scalarRegularCurrent_smul (Ω : TopologicalSpace.Opens E) (c : ℝ) (f : E → ℝ)
    (hf : ContinuousOn f Ω) :
    scalarRegularCurrent μ Ω (c • f) (hf.const_smul c) = c • scalarRegularCurrent μ Ω f hf := by
  apply LinearMap.ext
  intro φ
  change (∫ x, (c * f x) * φ x ∂μ) = c * ∫ x, f x * φ x ∂μ
  simp only [mul_assoc]
  exact integral_const_mul c _

@[simp] theorem scalarRegularCurrent_zero (Ω : TopologicalSpace.Opens E) :
    scalarRegularCurrent μ Ω (fun _ => 0) continuousOn_const = 0 := by
  ext φ
  simp only [scalarRegularCurrent_apply, zero_mul, integral_zero, LinearMap.zero_apply]

end TernaryPoly.PolynomialFormWeakSmooth
