module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.AverageDecay
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.GeometricDomination

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open scoped ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ
local notation "PrincipalQuotient" => Quotient (MulAction.orbitRel principalRealSpecialLinear RealSL3)

theorem two_piece_growth_eight_decay (m n : ℕ) :
    (2 : ℝ) ^ (4 * m + 8 * n) * (8 : ℝ)⁻¹ ^ n ≤ (32 : ℝ) ^ (m + n) := by
  have exponent : 4 * m + 8 * n = (4 * m + 5 * n) + 3 * n := by omega
  have cancels : (2 : ℝ) ^ (3 * n) * (8 : ℝ)⁻¹ ^ n = 1 := by
    rw [pow_mul, ← mul_pow]
    norm_num
  rw [exponent, pow_add, mul_assoc, cancels, mul_one]
  calc
    _ ≤ (2 : ℝ) ^ (5 * (m + n)) := pow_le_pow_right₀ (by norm_num) (by omega)
    _ = _ := by rw [pow_mul]; norm_num

theorem normalizedScalarEisensteinPrincipalQuotient_eight_decay_test_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) {test : PrincipalQuotient → ℂ} {testBound : ℝ}
    (test_nonnegative : 0 ≤ testBound)
    (decay : ∀ residue : integerSpecialLinearReduction.range, ∀ m n : ℕ,
      ∀ point ∈ principalQuotientPiece residue m n, ‖test point‖ ≤ testBound * (8 : ℝ)⁻¹ ^ n) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ residue : integerSpecialLinearReduction.range, ∀ m n : ℕ,
      ∀ point ∈ principalQuotientPiece residue m n, ∀ integral : GL3 IntegralAdeles,
        ENNReal.ofReal ‖((displacement : ℂ) * normalizedScalarEisensteinPrincipalQuotient flat
          ((3 : ℂ) / 2 + (displacement : ℂ)) integral point) * test point‖ ≤
            ENNReal.ofReal bound * (32 : ℝ≥0∞) ^ (m + n) := by
  obtain ⟨sumBound, sum_nonnegative, sum_bound⟩ := normalizedScalarEisensteinPrincipalQuotient_piece_bound flat
  refine ⟨sumBound * testBound, mul_nonneg sum_nonnegative test_nonnegative, ?_⟩
  filter_upwards [sum_bound, self_mem_nhdsWithin] with displacement estimate positive
  change 0 < displacement at positive
  intro residue m n point member integral
  have real_bound : ‖((displacement : ℂ) * normalizedScalarEisensteinPrincipalQuotient flat
      ((3 : ℂ) / 2 + (displacement : ℂ)) integral point) * test point‖ ≤
        (sumBound * testBound) * (32 : ℝ) ^ (m + n) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
    calc
      _ ≤ ((2 : ℝ) ^ (4 * m + 8 * n) * sumBound) * (testBound * (8 : ℝ)⁻¹ ^ n) :=
        mul_le_mul (estimate residue m n point member integral) (decay residue m n point member)
          (norm_nonneg _) (by positivity)
      _ = (sumBound * testBound) * ((2 : ℝ) ^ (4 * m + 8 * n) * (8 : ℝ)⁻¹ ^ n) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (two_piece_growth_eight_decay m n) (by positivity)
  have bound := ENNReal.ofReal_le_ofReal real_bound
  simpa only [ENNReal.ofReal_mul (mul_nonneg sum_nonnegative test_nonnegative),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 32), ENNReal.ofReal_ofNat] using bound

theorem normalizedScalarEisensteinPrincipalQuotient_eight_decay_pairing_tendsto
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) {test : PrincipalQuotient → ℂ} (measurable : Measurable test)
    {testBound : ℝ} (test_nonnegative : 0 ≤ testBound)
    (decay : ∀ residue : integerSpecialLinearReduction.range, ∀ m n : ℕ,
      ∀ point ∈ principalQuotientPiece residue m n, ‖test point‖ ≤ testBound * (8 : ℝ)⁻¹ ^ n) :
    Tendsto (fun displacement : ℝ => ∫ point,
      ((displacement : ℂ) * normalizedScalarEisensteinPrincipalQuotient flat
        ((3 : ℂ) / 2 + (displacement : ℂ)) integral point) * test point ∂principalSpecialLinearQuotientMeasure)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ point, normalizedBoundaryResiduePrincipalQuotient flat continuation_spec integral point *
        test point ∂principalSpecialLinearQuotientMeasure)) := by
  obtain ⟨bound, _, bounded⟩ := normalizedScalarEisensteinPrincipalQuotient_eight_decay_test_bound flat test_nonnegative decay
  apply principalQuotient_tendsto_integral_of_geometric_bounds (nhdsWithin (0 : ℝ) (Set.Ioi 0)) bound
    (base := 32) (by norm_num)
  · filter_upwards [self_mem_nhdsWithin] with displacement positive
    have large : 3 / 2 < ((3 : ℂ) / 2 + (displacement : ℂ)).re := by norm_num; exact positive
    exact ((measurable_const.mul (normalizedScalarEisensteinPrincipalQuotient_measurable flat _ large integral)).mul
      measurable).aestronglyMeasurable
  · filter_upwards [bounded] with displacement bound_at
    intro residue m n point member
    exact bound_at residue m n point member integral
  · exact Filter.Eventually.of_forall (fun point =>
      (normalizedScalarEisensteinPrincipalQuotient_residue_limit flat continuation_spec integral point).mul_const (test point))

theorem normalizedScalarEisensteinPrincipalQuotient_tent_pairing_tendsto
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (radius : ℝ) :
    Tendsto (fun displacement : ℝ => ∫ point,
      ((displacement : ℂ) * normalizedScalarEisensteinPrincipalQuotient flat
        ((3 : ℂ) / 2 + (displacement : ℂ)) integral point) *
          star (normalizedBoundaryResidueAveragePrincipalQuotient flat continuation_spec integral (realSpecialTent radius) point)
            ∂principalSpecialLinearQuotientMeasure)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ point, normalizedBoundaryResiduePrincipalQuotient flat continuation_spec integral point *
        star (normalizedBoundaryResidueAveragePrincipalQuotient flat continuation_spec integral (realSpecialTent radius) point)
          ∂principalSpecialLinearQuotientMeasure)) := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedBoundaryResidueTentAverage_piece_decay flat continuation_spec radius
  apply normalizedScalarEisensteinPrincipalQuotient_eight_decay_pairing_tendsto flat continuation_spec integral
    (continuous_star.measurable.comp (normalizedBoundaryResidueAveragePrincipalQuotient_measurable flat continuation_spec integral
      (realSpecialTent_continuous radius).measurable)) nonnegative
  intro residue m n point member
  simpa only [Function.comp_def, norm_star] using bounded residue m n point member integral

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
