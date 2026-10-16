module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.DifferenceBound
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.PrincipalQuotient

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem normalizedBoundaryResidue_real_right_tendsto
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (matrix : AdelicGL) (integral : finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    Tendsto (fun shift : RealGL3 => normalizedBoundaryResidue degree continuation (matrix * atInfinity shift))
      (nhds 1) (nhds (normalizedBoundaryResidue degree continuation matrix)) := by
  obtain ⟨bound, nonnegative, estimate⟩ := normalizedBoundaryResidue_difference_bound flat continuation_spec matrix integral
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  have divisor_positive : 0 < bound + 1 := by positivity
  have small := normalizedScalarDifferenceProfile_uniformly_small flat normalizedBoundaryParameterSet_compact
    (epsilon := epsilon / (bound + 1)) (div_pos positive divisor_positive)
  filter_upwards [small] with shift small_at
  rw [dist_eq_norm]
  apply (estimate (atInfinity shift) (epsilon / (bound + 1)) (by positivity) small_at).trans_lt
  rw [← mul_div_assoc, div_lt_iff₀ divisor_positive]
  nlinarith

theorem normalizedBoundaryResidue_real_integral_slice_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) :
    Continuous (fun matrix : SpecialLinearGroup (Fin 3) ℝ =>
      normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral matrix)) := by
  apply continuous_iff_continuousAt.mpr
  intro base
  have finite_integral : finiteGroup (realSpecialIntegralSlice integral base) ∈
      Set.range (GeneralLinearGroup.map integralEmbedding) := by
    simp only [realSpecialIntegralSlice, map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul]
    exact ⟨integral, rfl⟩
  have difference_limit : Tendsto (fun matrix : SpecialLinearGroup (Fin 3) ℝ =>
      (SpecialLinearGroup.toGL base)⁻¹ * SpecialLinearGroup.toGL matrix) (nhds base) (nhds 1) := by
    simpa only [inv_mul_cancel] using
      ((show Continuous (fun matrix : SpecialLinearGroup (Fin 3) ℝ =>
        (SpecialLinearGroup.toGL base)⁻¹ * SpecialLinearGroup.toGL matrix) from
          continuous_const.mul SpecialLinearGroup.continuous_toGL).tendsto base)
  have limit := (normalizedBoundaryResidue_real_right_tendsto flat continuation_spec
    (realSpecialIntegralSlice integral base) finite_integral).comp difference_limit
  have identity (matrix : SpecialLinearGroup (Fin 3) ℝ) :
      realSpecialIntegralSlice integral base * atInfinity ((SpecialLinearGroup.toGL base)⁻¹ * SpecialLinearGroup.toGL matrix) =
        realSpecialIntegralSlice integral matrix := by
    apply adelicGroup_eq_of_components
    · simp only [realSpecialIntegralSlice, map_mul, realGroup_atInfinity, realGroup_atFinite, mul_one, mul_inv_cancel_left]
    · simp only [realSpecialIntegralSlice, map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul, mul_one]
  change Tendsto _ (nhds base) _
  simpa only [Function.comp_def, identity] using limit

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
