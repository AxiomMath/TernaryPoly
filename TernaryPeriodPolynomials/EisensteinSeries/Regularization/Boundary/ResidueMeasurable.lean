module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.ResidueIntegrals

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalizedBoundaryResidue_measurable
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {map : X → AdelicGL} (continuous : Continuous map) :
    Measurable (fun point => normalizedBoundaryResidue degree continuation (map point)) := by
  let approximation (displacement : ℝ) (point : X) : ℂ :=
    if 0 < displacement then (displacement : ℂ) * ∑' flag,
      eisensteinSummand (unitaryNormalize degree family) ((3 : ℂ) / 2 + (displacement : ℂ)) (map point) flag else 0
  have measurable (displacement : ℝ) : Measurable (approximation displacement) := by
    by_cases positive : 0 < displacement
    · have large : 3 / 2 < ((3 : ℂ) / 2 + (displacement : ℂ)).re := by norm_num; exact positive
      simpa only [approximation, ite_eq_left positive, Pi.mul_def] using
        (continuous_const.mul (normalized_scalar_sum_continuous flat _ large continuous)).measurable
    · simp only [approximation, ite_eq_right positive]
      exact measurable_const
  apply measurable_of_tendsto_metrizable' (nhdsWithin (0 : ℝ) (Set.Ioi 0)) measurable
  apply tendsto_pi_nhds.mpr
  intro point
  apply (normalizedBoundaryResidue_tendsto flat continuation_spec (map point)).congr'
  filter_upwards [self_mem_nhdsWithin] with displacement positive
  exact (ite_eq_left positive).symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
