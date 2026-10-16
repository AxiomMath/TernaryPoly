module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.DifferencePowerBound
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.DifferenceUniformity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.Residue
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.LargeDegreeRegularization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

def normalizedBoundaryParameterSet : Set ℂ :=
  (fun displacement : ℝ => (3 : ℂ) / 2 + (displacement : ℂ)) '' Set.Icc 0 1

theorem normalizedBoundaryParameterSet_compact : IsCompact normalizedBoundaryParameterSet :=
  isCompact_Icc.image (continuous_const.add Complex.continuous_ofReal)

theorem normalizedBoundaryResidue_difference_bound
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (matrix : AdelicGL) (integral : finiteGroup matrix ∈ Set.range (GeneralLinearGroup.map integralEmbedding)) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ shift : AdelicGL, ∀ epsilon : ℝ, 0 ≤ epsilon →
      (∀ parameter ∈ normalizedBoundaryParameterSet, ∀ compactMatrix : AdelicGL, inMaximalCompact compactMatrix →
        ‖normalizedScalarDifferenceProfile flat shift parameter compactMatrix‖ ≤ epsilon) →
      ‖normalizedBoundaryResidue degree continuation (matrix * shift) - normalizedBoundaryResidue degree continuation matrix‖ ≤
        bound * epsilon := by
  have parameter_nonnegative : ∀ parameter ∈ normalizedBoundaryParameterSet, 0 ≤ (3 : ℝ) / 2 + parameter.re := by
    rintro parameter ⟨displacement, member, rfl⟩
    norm_num
    linarith [member.1]
  obtain ⟨coefficient, coefficient_nonnegative, power_bound⟩ := normalized_scalar_difference_compact_power_bound flat
    normalizedBoundaryParameterSet {matrix} normalizedBoundaryParameterSet_compact isCompact_singleton parameter_nonnegative
    (by intro point member; simpa only [Set.mem_singleton_iff.mp member] using integral)
  obtain ⟨latticeBound, lattice_nonnegative, lattice_estimate⟩ := planeFlagIntegerRow_boundary_bound
  refine ⟨latticeBound * coefficient, mul_nonneg lattice_nonnegative coefficient_nonnegative, ?_⟩
  intro shift epsilon epsilon_nonnegative compact_bound
  apply le_of_tendsto ((normalizedBoundaryResidue_tendsto flat continuation_spec (matrix * shift)).sub
    (normalizedBoundaryResidue_tendsto flat continuation_spec matrix)).norm
  have below_one : ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0), displacement < 1 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, below_one, lattice_estimate] with displacement positive small lattice_bound
  change 0 < displacement at positive
  let parameter : ℂ := (3 : ℂ) / 2 + (displacement : ℂ)
  have parameter_member : parameter ∈ normalizedBoundaryParameterSet :=
    ⟨displacement, ⟨positive.le, small.le⟩, rfl⟩
  have large : 3 / 2 < parameter.re := by dsimp [parameter]; norm_num; exact positive
  have exponent : -((3 : ℝ) / 2 + parameter.re) = -3 - displacement := by dsimp [parameter]; norm_num; ring
  let term (flag : Flags .plane) : ℂ :=
    eisensteinSummand (unitaryNormalize degree family) parameter (matrix * shift) flag -
      eisensteinSummand (unitaryNormalize degree family) parameter matrix flag
  have term_bound (flag : Flags .plane) : ‖term flag‖ ≤
      ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-3 - displacement) * (coefficient * epsilon) := by
    have profile_bound := power_bound shift epsilon epsilon_nonnegative compact_bound parameter parameter_member
      matrix (Set.mem_singleton matrix) flag
    rw [exponent] at profile_bound
    have scalar_bound : ‖term flag‖ ≤ ‖normalizedScalarDifferenceProfile flat shift parameter (rationalGroup flag.out⁻¹ * matrix)‖ := by
      simpa only [term, eisensteinSummand, mul_assoc] using
        normalized_scalar_difference_norm_le_profile flat shift parameter (rationalGroup flag.out⁻¹ * matrix)
    exact scalar_bound.trans profile_bound
  have majorant_summable := (planeFlagIntegerRow_summable (-3 - displacement) (by linarith)).mul_right (coefficient * epsilon)
  have norm_summable := Summable.of_nonneg_of_le (fun flag => norm_nonneg (term flag)) term_bound majorant_summable
  have sum_bound := (norm_tsum_le_tsum_norm norm_summable).trans (norm_summable.tsum_le_tsum term_bound majorant_summable)
  rw [tsum_mul_right] at sum_bound
  have first_sum := (normalized_scalar_sum_analytic flat (matrix * shift)).2 parameter large
  have second_sum := (normalized_scalar_sum_analytic flat matrix).2 parameter large
  change ‖(displacement : ℂ) * (∑' flag, eisensteinSummand (unitaryNormalize degree family) parameter (matrix * shift) flag) -
    (displacement : ℂ) * (∑' flag, eisensteinSummand (unitaryNormalize degree family) parameter matrix flag)‖ ≤ _
  rw [← mul_sub, ← first_sum.tsum_sub second_sum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  calc
    _ ≤ displacement * ((∑' flag : Flags .plane,
        ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-3 - displacement)) * (coefficient * epsilon)) :=
      mul_le_mul_of_nonneg_left sum_bound positive.le
    _ = (displacement * (∑' flag : Flags .plane,
        ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-3 - displacement))) * (coefficient * epsilon) := by ring
    _ ≤ latticeBound * (coefficient * epsilon) :=
      mul_le_mul_of_nonneg_right lattice_bound (mul_nonneg coefficient_nonnegative epsilon_nonnegative)
    _ = _ := by ring

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
