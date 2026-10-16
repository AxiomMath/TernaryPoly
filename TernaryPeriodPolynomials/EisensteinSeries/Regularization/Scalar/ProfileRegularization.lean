module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.ProfileFlagBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.Continuation
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalized_scalar_flag_compact_majorant
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (profile_bounds : ∀ parameters : Set ℂ, ∀ matrices : Set AdelicGL,
      IsCompact parameters → IsCompact matrices → ∃ bound : ℝ,
        ∀ parameter ∈ parameters, ∀ matrix ∈ matrices,
          ‖normalizedScalarProfile flat parameter matrix‖ ≤ bound)
    (parameters : Set ℂ) (matrices : Set AdelicGL)
    (parameters_compact : IsCompact parameters) (matrices_compact : IsCompact matrices)
    (large : ∀ parameter ∈ parameters, 3 / 2 < parameter.re) :
    ∃ majorant : Flags .plane → ℝ, Summable majorant ∧
      ∀ parameter ∈ parameters, ∀ matrix ∈ matrices, ∀ flag,
        ‖eisensteinSummand (unitaryNormalize degree family) parameter matrix flag‖ ≤ majorant flag := by
  obtain ⟨majorant, summable, bounded⟩ := normalized_scalar_profile_compact_summable_majorant
    flat profile_bounds parameters matrices parameters_compact matrices_compact large
  refine ⟨majorant, summable, ?_⟩
  intro parameter parameter_in matrix matrix_in flag
  exact (normalized_scalar_norm_le_profile flat parameter (rationalGroup flag.out⁻¹ * matrix)).trans
    (bounded parameter parameter_in matrix matrix_in flag)

theorem normalized_scalar_flag_sum_analytic_of_profile_bounds
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (profile_bounds : ∀ parameters : Set ℂ, ∀ matrices : Set AdelicGL,
      IsCompact parameters → IsCompact matrices → ∃ bound : ℝ,
        ∀ parameter ∈ parameters, ∀ matrix ∈ matrices,
          ‖normalizedScalarProfile flat parameter matrix‖ ≤ bound)
    (matrix : AdelicGL) :
    AnalyticOnNhd ℂ
      (fun parameter => ∑' flag, eisensteinSummand (unitaryNormalize degree family) parameter matrix flag)
      {parameter : ℂ | 3 / 2 < parameter.re} ∧
    ∀ parameter : ℂ, 3 / 2 < parameter.re →
      Summable (eisensteinSummand (unitaryNormalize degree family) parameter matrix) := by
  have domain_open : IsOpen {parameter : ℂ | 3 / 2 < parameter.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have uniform : SummableLocallyUniformlyOn
      (fun flag parameter => eisensteinSummand (unitaryNormalize degree family) parameter matrix flag)
      {parameter : ℂ | 3 / 2 < parameter.re} := by
    apply SummableLocallyUniformlyOn_of_locally_bounded domain_open
    intro parameters contained compact
    obtain ⟨majorant, summable, bounded⟩ := normalized_scalar_flag_compact_majorant
      flat profile_bounds parameters {matrix} compact isCompact_singleton contained
    exact ⟨majorant, summable, fun flag parameter member =>
      bounded parameter member matrix (Set.mem_singleton matrix) flag⟩
  refine ⟨?_, fun parameter large => uniform.summable large⟩
  apply DifferentiableOn.analyticOnNhd _ domain_open
  apply uniform.differentiableOn domain_open
  intro flag parameter _
  exact (unitaryNormalize_analytic degree flat.2.1 (rationalGroup flag.out⁻¹ * matrix) parameter).differentiableAt

theorem normalized_continuation_order_of_profile_bounds
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (profile_bounds : ∀ parameters : Set ℂ, ∀ matrices : Set AdelicGL,
      IsCompact parameters → IsCompact matrices → ∃ bound : ℝ,
        ∀ parameter ∈ parameters, ∀ matrix ∈ matrices,
          ‖normalizedScalarProfile flat parameter matrix‖ ≤ bound)
    (matrix : AdelicGL) (point : ℂ) (large : 3 / 2 < point.re) :
    0 ≤ meromorphicOrderAt (fun parameter => unitaryNormalize degree continuation parameter matrix) point := by
  obtain ⟨sum_analytic, summable⟩ := normalized_scalar_flag_sum_analytic_of_profile_bounds flat profile_bounds matrix
  have normalized_spec := unitaryNormalize_continuation degree continuation_spec
  obtain ⟨threshold, convergence⟩ := normalized_spec.2
  let actualSum (parameter : ℂ) :=
    ∑' flag, eisensteinSummand (unitaryNormalize degree family) parameter matrix flag
  let base : ℂ := (max threshold (3 / 2) + 1 : ℝ)
  have base_large : 3 / 2 < base.re := by
    dsimp [base]
    linarith [le_max_right threshold (3 / 2)]
  have base_threshold : threshold < base.re := by
    dsimp [base]
    linarith [le_max_left threshold (3 / 2)]
  have same_near_base : (fun parameter => unitaryNormalize degree continuation parameter matrix) =ᶠ[nhds base]
      actualSum := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).eventually_mem base_large,
      (isOpen_lt continuous_const Complex.continuous_re).eventually_mem base_threshold]
      with parameter parameter_large parameter_threshold
    exact (convergence parameter parameter_threshold matrix).unique (summable parameter parameter_large).hasSum
  have difference_meromorphic : MeromorphicOn
      (fun parameter => unitaryNormalize degree continuation parameter matrix - actualSum parameter)
      {parameter : ℂ | 3 / 2 < parameter.re} := by
    intro parameter parameter_large
    exact (normalized_spec.1 matrix parameter).sub (sum_analytic parameter parameter_large).meromorphicAt
  have zero_order_base : meromorphicOrderAt
      (fun parameter => unitaryNormalize degree continuation parameter matrix - actualSum parameter) base = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [same_near_base.filter_mono nhdsWithin_le_nhds] with parameter equality
    exact sub_eq_zero.mpr equality
  have zero_order_point : meromorphicOrderAt
      (fun parameter => unitaryNormalize degree continuation parameter matrix - actualSum parameter) point = ⊤ := by
    by_contra nonzero
    exact (difference_meromorphic.meromorphicOrderAt_ne_top_of_isPreconnected
      ((convex_Ioi (3 / 2)).linear_preimage Complex.reLm).isPreconnected large base_large nonzero) zero_order_base
  have same_germ : (fun parameter => unitaryNormalize degree continuation parameter matrix) =ᶠ[
      nhdsWithin point {point}ᶜ] actualSum := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp zero_order_point] with parameter equality
    exact sub_eq_zero.mp equality
  rw [meromorphicOrderAt_congr same_germ]
  exact (sum_analytic point large).meromorphicOrderAt_nonneg

theorem regularization_of_large_degree_profile_bounds
    {degree : ℕ} (degree_large : 3 < degree) {inducingData : InducingData degree}
    {family continuation : ℂ → AdelicGL → ℂ} (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (profile_bounds : ∀ parameters : Set ℂ, ∀ matrices : Set AdelicGL,
      IsCompact parameters → IsCompact matrices → ∃ bound : ℝ,
        ∀ parameter ∈ parameters, ∀ matrix ∈ matrices,
          ‖normalizedScalarProfile flat parameter matrix‖ ≤ bound) :
    ∃ repaired : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation family repaired ∧ SameOffCohomologicalPoint continuation repaired ∧
        ∀ matrix, AnalyticAt ℂ (fun parameter => repaired parameter matrix) cohomologicalPoint := by
  apply regularization_of_unitaryNormalize_order (degree := degree) continuation_spec
  intro matrix
  apply normalized_continuation_order_of_profile_bounds flat continuation_spec profile_bounds matrix
  have real_large : (3 : ℝ) < (degree : ℝ) := by exact_mod_cast degree_large
  norm_num
  linarith

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
