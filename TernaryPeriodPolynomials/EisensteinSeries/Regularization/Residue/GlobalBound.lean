module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.IntegralBound
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.RationalDecomposition
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.ResidueIntegrals

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalizedBoundaryResidue_global_bound
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ matrix : AdelicGL,
      ‖normalizedBoundaryResidue degree continuation matrix‖ ≤ bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedBoundaryResidue_integral_finite_bound flat continuation_spec
  refine ⟨bound, nonnegative, ?_⟩
  intro matrix
  obtain ⟨rational, integral⟩ := adelic_rational_translate_integral matrix
  simpa only [normalizedBoundaryResidue_rational_invariant flat continuation_spec] using
    bounded (rationalGroup rational * matrix) integral

theorem normalizedBoundaryResidue_finite_measure_integrable
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (measure : Measure X) [IsFiniteMeasure measure] {map : X → AdelicGL} (continuous : Continuous map) :
    Integrable (fun point => normalizedBoundaryResidue degree continuation (map point)) measure := by
  obtain ⟨bound, _, bounded⟩ := normalizedBoundaryResidue_global_bound flat continuation_spec
  exact Integrable.of_bound
    (normalizedBoundaryResidue_aestronglyMeasurable flat continuation_spec measure continuous)
    bound (Filter.Eventually.of_forall (fun point => bounded (map point)))

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
