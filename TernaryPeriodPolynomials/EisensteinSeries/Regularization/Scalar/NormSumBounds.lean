module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.EisensteinNormSum

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Pointwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalized_scalar_reduced_piece_norm_boundary_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ m n : ℕ, ∀ matrix ∈ realSpecialScaling m n •
        realSpecialShrinkingBox m n (realSpecialDiagonalBox (1 / 64) 64),
      ∀ integral : GL3 IntegralAdeles,
        displacement * normalizedScalarEisensteinNormSum degree family
          ((3 : ℂ) / 2 + (displacement : ℂ)) (realSpecialIntegralSlice integral matrix) ≤
            (2 : ℝ) ^ (4 * m + 8 * n) * bound := by
  obtain ⟨coefficient, coefficient_nonnegative, coefficient_bound⟩ := normalized_scalar_reduced_piece_flag_bound flat
  obtain ⟨latticeBound, lattice_nonnegative, lattice_bound⟩ := planeFlagIntegerRow_boundary_bound
  refine ⟨latticeBound * coefficient, mul_nonneg lattice_nonnegative coefficient_nonnegative, ?_⟩
  have below_one : ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0), displacement < 1 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, below_one, lattice_bound] with displacement positive small lattice_bound
  change 0 < displacement at positive
  intro m n matrix member integral
  have bound_term := coefficient_bound displacement positive.le small.le m n matrix member integral
  have majorant_summable := (planeFlagIntegerRow_summable (-3 - displacement) (by linarith)).mul_right
    ((2 : ℝ) ^ (4 * m + 8 * n) * coefficient)
  have norm_summable := Summable.of_nonneg_of_le
    (fun flag => norm_nonneg (eisensteinSummand (unitaryNormalize degree family)
      ((3 : ℂ) / 2 + (displacement : ℂ)) (realSpecialIntegralSlice integral matrix) flag)) bound_term majorant_summable
  have sum_bound := norm_summable.tsum_le_tsum bound_term majorant_summable
  rw [tsum_mul_right] at sum_bound
  calc
    _ ≤ displacement * ((∑' flag : Flags .plane,
        ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-3 - displacement)) *
          ((2 : ℝ) ^ (4 * m + 8 * n) * coefficient)) := mul_le_mul_of_nonneg_left sum_bound positive.le
    _ = (2 : ℝ) ^ (4 * m + 8 * n) *
        ((displacement * ∑' flag : Flags .plane,
          ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-3 - displacement)) * coefficient) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right lattice_bound coefficient_nonnegative) (by positivity)

theorem normalizedScalarEisensteinNormPrincipalQuotient_piece_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ residue : integerSpecialLinearReduction.range, ∀ m n : ℕ,
      ∀ point ∈ principalQuotientPiece residue m n, ∀ integral : GL3 IntegralAdeles,
        displacement * normalizedScalarEisensteinNormPrincipalQuotient flat
          ((3 : ℂ) / 2 + (displacement : ℂ)) integral point ≤ (2 : ℝ) ^ (4 * m + 8 * n) * bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalized_scalar_reduced_piece_norm_boundary_bound flat
  refine ⟨bound, nonnegative, ?_⟩
  filter_upwards [bounded] with displacement bound_at
  intro residue m n point member integral
  obtain ⟨representative, representative_member, rfl⟩ := member
  obtain ⟨reduced, reduced_member, rfl⟩ := representative_member
  change displacement * normalizedScalarEisensteinNormSum degree family ((3 : ℂ) / 2 + (displacement : ℂ))
    (realSpecialIntegralSlice integral
      ((SpecialLinearGroup.map (Int.castRingHom ℝ) (integerSpecialLinearReductionRepresentative residue))⁻¹ * reduced)) ≤ _
  rw [normalizedScalarEisensteinNormSum_integer_inverse_slice flat]
  exact bound_at m n reduced reduced_member _

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
