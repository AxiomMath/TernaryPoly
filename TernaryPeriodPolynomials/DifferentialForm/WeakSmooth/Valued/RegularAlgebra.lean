module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.Regular

@[expose] public section

/-! Algebra and locality of literal coefficient-valued Bochner regular currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory
open scoped Distributions
variable {E V I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (μ : Measure E) [IsLocallyFiniteMeasure μ]

/-- Equal actual local coefficient functions define equal actual regular currents. -/
theorem valuedRegularCurrent_congr (Ω : TopologicalSpace.Opens E) {f g : E → V}
    (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω) (h : EqOn f g Ω) :
    valuedRegularCurrent μ Ω f hf = valuedRegularCurrent μ Ω g hg := by
  apply LinearMap.ext
  intro φ
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ (Ω : Set E)
  · rw [h hx]
  · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (φ.tsupport_subset ht))
    simp only [hz, zero_smul]

/-- The actual regular current is linear under finite sums of locally continuous coefficients. -/
theorem valuedRegularCurrent_sum (Ω : TopologicalSpace.Opens E) (s : Finset I)
    (f : I → E → V) (hf : ∀ i, ContinuousOn (f i) Ω) :
    valuedRegularCurrent μ Ω (fun x => ∑ i ∈ s, f i x) (continuousOn_finsetSum s (fun i _ => hf i)) =
      ∑ i ∈ s, valuedRegularCurrent μ Ω (f i) (hf i) := by
  apply LinearMap.ext
  intro φ
  simp only [valuedRegularCurrent_apply, Finset.smul_sum, LinearMap.sum_apply]
  exact integral_finsetSum s (fun i _ => valuedRegular_test_integrable μ Ω (f i) (hf i) φ)

/-- The literal regular current of a zero coefficient is zero. -/
@[simp] theorem valuedRegularCurrent_zero (Ω : TopologicalSpace.Opens E) :
    valuedRegularCurrent μ Ω (fun _ => (0 : V)) continuousOn_const = 0 := by
  apply LinearMap.ext
  intro φ
  simp only [valuedRegularCurrent_apply, smul_zero, integral_zero, LinearMap.zero_apply]

/-- Differences of coefficient functions give differences of actual regular currents. -/
theorem valuedRegularCurrent_sub (Ω : TopologicalSpace.Opens E) (f g : E → V)
    (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω) :
    valuedRegularCurrent μ Ω (fun x => f x - g x) (hf.sub hg) =
      valuedRegularCurrent μ Ω f hf - valuedRegularCurrent μ Ω g hg := by
  apply LinearMap.ext
  intro φ
  simp only [valuedRegularCurrent_apply, smul_sub, LinearMap.sub_apply]
  exact integral_sub (valuedRegular_test_integrable μ Ω f hf φ)
    (valuedRegular_test_integrable μ Ω g hg φ)

end TernaryPoly.PolynomialFormWeakSmooth
