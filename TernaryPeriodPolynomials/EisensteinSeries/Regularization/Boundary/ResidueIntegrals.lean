module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.Residue
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.SeriesContinuity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem normalized_scalar_sum_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (large : 3 / 2 < parameter.re)
    {X : Type*} [TopologicalSpace X] {map : X → AdelicGL} (continuous : Continuous map) :
    Continuous (fun point => ∑' flag, eisensteinSummand (unitaryNormalize degree family) parameter (map point) flag) := by
  have composed := (normalized_scalar_flag_sum_joint_continuous flat).comp_continuous
    (continuous_const.prodMk continuous) (fun _ => large)
  dsimp only [Function.comp_def] at composed
  exact composed

theorem normalizedBoundaryResidue_aestronglyMeasurable
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (measure : Measure X) {map : X → AdelicGL} (continuous : Continuous map) :
    AEStronglyMeasurable (fun point => normalizedBoundaryResidue degree continuation (map point)) measure := by
  let approximation (displacement : ℝ) (point : X) : ℂ :=
    if 0 < displacement then (displacement : ℂ) * ∑' flag,
      eisensteinSummand (unitaryNormalize degree family) ((3 : ℂ) / 2 + (displacement : ℂ)) (map point) flag else 0
  have measurable (displacement : ℝ) : AEStronglyMeasurable (approximation displacement) measure := by
    by_cases positive : 0 < displacement
    · have large : 3 / 2 < ((3 : ℂ) / 2 + (displacement : ℂ)).re := by norm_num; exact positive
      simpa only [approximation, ite_eq_left positive, Pi.mul_def] using
        (continuous_const.mul (normalized_scalar_sum_continuous flat _ large continuous)).aestronglyMeasurable
    · simp only [approximation, ite_eq_right positive]
      exact aestronglyMeasurable_const
  apply aestronglyMeasurable_of_tendsto_ae (nhdsWithin (0 : ℝ) (Set.Ioi 0)) measurable
  apply Filter.Eventually.of_forall
  intro point
  apply (normalizedBoundaryResidue_tendsto flat continuation_spec (map point)).congr'
  filter_upwards [self_mem_nhdsWithin] with displacement positive
  exact (ite_eq_left positive).symm

theorem normalizedBoundaryResidue_integrable
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (measure : Measure X) [IsFiniteMeasure measure] {map : X → AdelicGL} (continuous : Continuous map)
    (matrices : Set AdelicGL) (compact : IsCompact matrices)
    (contained : ∀ᵐ point ∂measure, map point ∈ matrices) :
    Integrable (fun point => normalizedBoundaryResidue degree continuation (map point)) measure := by
  obtain ⟨bound, _, bounded⟩ := normalizedBoundaryResidue_compact_bound flat continuation_spec matrices compact
  apply Integrable.of_bound (normalizedBoundaryResidue_aestronglyMeasurable flat continuation_spec measure continuous) bound
  filter_upwards [contained] with point member
  exact bounded (map point) member

theorem normalizedBoundaryResidue_integral_tendsto
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (measure : Measure X) [IsFiniteMeasure measure] {map : X → AdelicGL} (continuous : Continuous map)
    (matrices : Set AdelicGL) (compact : IsCompact matrices)
    (contained : ∀ᵐ point ∂measure, map point ∈ matrices) :
    Tendsto (fun displacement : ℝ => ∫ point, (displacement : ℂ) *
      ∑' flag, eisensteinSummand (unitaryNormalize degree family)
        ((3 : ℂ) / 2 + (displacement : ℂ)) (map point) flag ∂measure)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ point, normalizedBoundaryResidue degree continuation (map point) ∂measure)) := by
  obtain ⟨bound, _, bounded⟩ := normalized_scalar_sum_compact_boundary_bound flat matrices compact
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => bound)
  · filter_upwards [self_mem_nhdsWithin] with displacement positive
    have large : 3 / 2 < ((3 : ℂ) / 2 + (displacement : ℂ)).re := by norm_num; exact positive
    exact (continuous_const.mul (normalized_scalar_sum_continuous flat _ large continuous)).aestronglyMeasurable
  · filter_upwards [bounded, self_mem_nhdsWithin] with displacement bounded positive
    filter_upwards [contained] with point member
    change 0 < displacement at positive
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
    exact bounded (map point) member
  · exact integrable_const bound
  · exact Filter.Eventually.of_forall (fun point => normalizedBoundaryResidue_tendsto flat continuation_spec (map point))

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
