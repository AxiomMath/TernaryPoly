module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Valued.Regular
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.RegularSeparation

@[expose] public section

/-! Exact scalar coefficients and separation of genuine vector-valued regular currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory Measure
open scoped Distributions
variable {E V I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [CompleteSpace V]
variable (μ : Measure E) [IsLocallyFiniteMeasure μ]

/-- The scalar coefficient of the genuine Bochner regular current is the actual scalar current. -/
theorem valuedRegularCurrent_scalarCoefficient (Ω : TopologicalSpace.Opens E)
    (L : V →L[ℝ] ℝ) (f : E → V) (hf : ContinuousOn f Ω) :
    L.toLinearMap.comp (valuedRegularCurrent μ Ω f hf) =
      scalarRegularCurrent μ Ω (fun x => L (f x)) (L.continuous.comp_continuousOn hf) :=
  (valuedRegularCurrent_comp μ Ω L f hf).trans (valuedRegularCurrent_scalar μ Ω _ _)

/-- Actual compact smooth scalar tests separate continuous vector-valued functions. -/
theorem valuedRegularCurrent_eq_iff [IsOpenPosMeasure μ] [Fintype I]
    (e : V ≃L[ℝ] (I → ℝ)) (Ω : TopologicalSpace.Opens E) (f g : E → V)
    (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω) :
    valuedRegularCurrent μ Ω f hf = valuedRegularCurrent μ Ω g hg ↔ EqOn f g Ω := by
  constructor
  · intro h x hx
    apply e.injective
    funext i
    let L : V →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
    have hi := congrArg (fun T : ValuedWeak (V := V) Ω => L.toLinearMap.comp T) h
    rw [valuedRegularCurrent_scalarCoefficient, valuedRegularCurrent_scalarCoefficient] at hi
    exact ((scalarRegularCurrent_eq_iff μ Ω _ _ _ _).mp hi) hx
  · intro h
    apply LinearMap.ext
    intro φ
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ (Ω : Set E)
    · rw [h hx]
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (φ.tsupport_subset ht))
      simp only [hz, zero_smul]

end TernaryPoly.PolynomialFormWeakSmooth
