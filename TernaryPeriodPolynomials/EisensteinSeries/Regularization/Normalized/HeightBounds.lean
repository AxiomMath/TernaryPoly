module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.KernelIntegrals

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalizedCuspVector_integral_finite_norm_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ parameter matrix,
      finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding) →
      ‖(normalizedCuspVector flat.1 parameter matrix).val‖ ≤
        Real.exp ((inductionExponent .plane parameter).re *
          Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) -
          (3 / 2 + parameter.re) * Real.log (realPlaneHeight (realGroup matrix))) * bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedCuspVector_parabolic_norm_bound flat
  refine ⟨bound, nonnegative, ?_⟩
  intro parameter matrix integral
  obtain ⟨first, second, binary, scalar, compactMatrix, decomposition, compact_spec, scalar_height⟩ :=
    integral_finite_plane_decomposition matrix integral
  have bound_at := bounded parameter first second binary (realAdeleUnit scalar) compactMatrix compact_spec
  rw [← decomposition] at bound_at
  have scalar_norm : (adeleNorm (realAdeleUnit scalar) : ℝ) = realPlaneHeight (realGroup matrix) := by
    rw [adeleNorm_realAdeleUnit, scalar_height, abs_of_pos (realPlaneHeight_pos _)]
  have determinant_norm : (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) =
      (adeleNorm (GeneralLinearGroup.det binary) : ℝ) * realPlaneHeight (realGroup matrix) := by
    conv_lhs => rw [decomposition]
    simp only [map_mul, det_planeUnipotent, one_mul, det_planeLevi,
      adeleNorm_det_compact compactMatrix compact_spec, mul_one, NNReal.coe_mul]
    rw [scalar_norm]
  have log_det : Real.log (adeleNorm (GeneralLinearGroup.det matrix) : ℝ) =
      Real.log (adeleNorm (GeneralLinearGroup.det binary) : ℝ) +
        Real.log (realPlaneHeight (realGroup matrix)) := by
    rw [determinant_norm, Real.log_mul
      (ne_of_gt (NNReal.coe_pos.mpr (adeleNorm_pos _))) (ne_of_gt (realPlaneHeight_pos _))]
  rw [scalar_norm] at bound_at
  convert bound_at using 2
  congr 1
  rw [log_det]
  norm_num [inductionExponent, Complex.mul_re, Complex.div_re]
  ring

theorem real_standard_kernel_finite_integral (first second : ℝ) :
    finiteGroup (weyl⁻¹ * lineUnipotent (first, (0 : FiniteAdeles)) (second, (0 : FiniteAdeles))) ∈
      Set.range (GeneralLinearGroup.map integralEmbedding) := by
  refine ⟨(weyl : GL3 IntegralAdeles)⁻¹, ?_⟩
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [finiteGroup, weyl, lineUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem real_standard_kernel_height (first second : ℝ) :
    realPlaneHeight (realGroup
      (weyl⁻¹ * lineUnipotent (first, (0 : FiniteAdeles)) (second, (0 : FiniteAdeles)))) =
      Real.sqrt (1 + first ^ 2 + second ^ 2) := by
  simp [realPlaneHeight, realGroup, weyl, lineUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem normalized_standard_real_kernel_norm_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ (parameter : ℂ) (first second : ℝ),
      ‖(normalizedCuspVector flat.1 parameter
        (weyl⁻¹ * lineUnipotent (first, (0 : FiniteAdeles)) (second, (0 : FiniteAdeles)))).val‖ ≤
        (1 + first ^ 2 + second ^ 2) ^ (-(3 / 2 + parameter.re) / 2) * bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedCuspVector_integral_finite_norm_bound flat
  refine ⟨bound, nonnegative, ?_⟩
  intro parameter first second
  have bound_at := bounded parameter _ (real_standard_kernel_finite_integral first second)
  rw [real_standard_kernel_height] at bound_at
  simp only [map_mul, map_inv, det_weyl, det_lineUnipotent, inv_one, one_mul,
    map_one, NNReal.coe_one, Real.log_one, mul_zero, zero_sub] at bound_at
  rw [Real.log_sqrt (by positivity)] at bound_at
  rw [Real.rpow_def_of_pos (by positivity)]
  convert bound_at using 2
  congr 1
  ring

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
