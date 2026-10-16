module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.NormSumBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.AveragePairing

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open scoped ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ
local notation "PrincipalQuotient" => Quotient (MulAction.orbitRel principalRealSpecialLinear RealSL3)

theorem normalizedScalarEisensteinNormPrincipalQuotient_test_integrable
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (integral : GL3 IntegralAdeles)
    {test : PrincipalQuotient → ℂ} (measurable : Measurable test) {testBound : ℝ}
    (test_nonnegative : 0 ≤ testBound)
    (decay : ∀ residue : integerSpecialLinearReduction.range, ∀ m n : ℕ,
      ∀ point ∈ principalQuotientPiece residue m n, ‖test point‖ ≤ testBound * (8 : ℝ)⁻¹ ^ n) :
    ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      Integrable (fun point => normalizedScalarEisensteinNormPrincipalQuotient flat
        ((3 : ℂ) / 2 + (displacement : ℂ)) integral point * ‖test point‖) principalSpecialLinearQuotientMeasure := by
  obtain ⟨sumBound, sum_nonnegative, sum_bound⟩ := normalizedScalarEisensteinNormPrincipalQuotient_piece_bound flat
  filter_upwards [sum_bound, self_mem_nhdsWithin] with displacement estimate positive
  change 0 < displacement at positive
  have weighted : Integrable (fun point => displacement * normalizedScalarEisensteinNormPrincipalQuotient flat
      ((3 : ℂ) / 2 + (displacement : ℂ)) integral point * ‖test point‖) principalSpecialLinearQuotientMeasure := by
    apply principalQuotient_integrable_of_geometric_bounds (sumBound * testBound) (base := 32) (by norm_num)
      (((measurable_const.mul (normalizedScalarEisensteinNormPrincipalQuotient_measurable flat _ integral)).mul
        measurable.norm).aestronglyMeasurable)
    intro residue m n point member
    have bound : ‖displacement * normalizedScalarEisensteinNormPrincipalQuotient flat
        ((3 : ℂ) / 2 + (displacement : ℂ)) integral point * ‖test point‖‖ ≤
          (sumBound * testBound) * (32 : ℝ) ^ (m + n) := by
      rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg positive.le
        (normalizedScalarEisensteinNormPrincipalQuotient_nonnegative flat _ integral point)) (norm_nonneg _))]
      calc
        _ ≤ ((2 : ℝ) ^ (4 * m + 8 * n) * sumBound) * (testBound * (8 : ℝ)⁻¹ ^ n) :=
          mul_le_mul (estimate residue m n point member integral) (decay residue m n point member)
            (norm_nonneg _) (by positivity)
        _ = (sumBound * testBound) * ((2 : ℝ) ^ (4 * m + 8 * n) * (8 : ℝ)⁻¹ ^ n) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (two_piece_growth_eight_decay m n) (by positivity)
    simpa only [Pi.mul_apply, ENNReal.ofReal_mul (mul_nonneg sum_nonnegative test_nonnegative),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 32), ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal bound
  have unweighted := weighted.const_mul displacement⁻¹
  have identity : (fun point => displacement⁻¹ * (displacement * normalizedScalarEisensteinNormPrincipalQuotient flat
      ((3 : ℂ) / 2 + (displacement : ℂ)) integral point * ‖test point‖)) =
      (fun point => normalizedScalarEisensteinNormPrincipalQuotient flat
        ((3 : ℂ) / 2 + (displacement : ℂ)) integral point * ‖test point‖) := by
    funext point
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt positive), one_mul]
  exact identity ▸ unweighted

theorem normalizedScalarEisensteinNormPrincipalQuotient_tent_integrable
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (radius : ℝ) :
    ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      Integrable (fun point => normalizedScalarEisensteinNormPrincipalQuotient flat
        ((3 : ℂ) / 2 + (displacement : ℂ)) integral point *
        ‖normalizedBoundaryResidueAveragePrincipalQuotient flat continuation_spec integral (realSpecialTent radius) point‖)
        principalSpecialLinearQuotientMeasure := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedBoundaryResidueTentAverage_piece_decay flat continuation_spec radius
  apply normalizedScalarEisensteinNormPrincipalQuotient_test_integrable flat integral
    (normalizedBoundaryResidueAveragePrincipalQuotient_measurable flat continuation_spec integral
      (realSpecialTent_continuous radius).measurable) nonnegative
  intro residue m n point member
  exact bounded residue m n point member integral

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
