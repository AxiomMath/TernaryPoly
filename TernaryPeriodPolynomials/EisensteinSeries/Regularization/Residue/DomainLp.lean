module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Reduced.ShrinkingCover
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.GlobalBound

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

instance integerSpecialLinearDomain_restrict_finite :
    IsFiniteMeasure (realSpecialLinearHaar.restrict integerSpecialLinearDomain) := by
  constructor
  rw [Measure.restrict_apply_univ, ← integerSpecialLinearQuotientMeasure_univ]
  exact integerSpecialLinearQuotientMeasure_finite

theorem normalizedBoundaryResidue_finite_measure_memLp
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (measure : Measure X) [IsFiniteMeasure measure] {map : X → AdelicGL} (continuous : Continuous map)
    (exponent : ℝ≥0∞) :
    MemLp (fun point => normalizedBoundaryResidue degree continuation (map point)) exponent measure := by
  obtain ⟨bound, _, bounded⟩ := normalizedBoundaryResidue_global_bound flat continuation_spec
  exact MemLp.of_bound
    (normalizedBoundaryResidue_aestronglyMeasurable flat continuation_spec measure continuous)
    bound (Filter.Eventually.of_forall (fun point => bounded (map point)))

theorem normalizedBoundaryResidue_integer_domain_memLp
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    {map : SpecialLinearGroup (Fin 3) ℝ → AdelicGL} (continuous : Continuous map) (exponent : ℝ≥0∞) :
    MemLp (fun point => normalizedBoundaryResidue degree continuation (map point)) exponent
      (realSpecialLinearHaar.restrict integerSpecialLinearDomain) :=
  normalizedBoundaryResidue_finite_measure_memLp flat continuation_spec _ continuous exponent

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
