module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Reduced.PieceRowBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.LatticeShapeBounds
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.PrincipalQuotient
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.LatticeBoundaryBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Pointwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem negative_power_bound_of_scale {radius transformed scale displacement : ℝ}
    (positive : 0 < radius) (scale_large : 1 ≤ scale)
    (displacement_nonnegative : 0 ≤ displacement) (displacement_small : displacement ≤ 1)
    (comparison : radius ≤ scale * transformed) :
    transformed ^ (-3 - displacement) ≤ radius ^ (-3 - displacement) * scale ^ 4 := by
  have scale_positive : 0 < scale := lt_of_lt_of_le zero_lt_one scale_large
  have lower : radius / scale ≤ transformed :=
    (div_le_iff₀ scale_positive).mpr (by simpa only [mul_comm] using comparison)
  calc
    _ ≤ (radius / scale) ^ (-3 - displacement) :=
      Real.rpow_le_rpow_of_nonpos (div_pos positive scale_positive) lower (by linarith)
    _ = radius ^ (-3 - displacement) * scale ^ (3 + displacement) := by
      rw [Real.div_rpow positive.le scale_positive.le]
      conv_lhs => rhs; rw [show -3 - displacement = -(3 + displacement) by ring,
        Real.rpow_neg scale_positive.le]
      rw [div_inv_eq_mul]
    _ ≤ radius ^ (-3 - displacement) * scale ^ 4 := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg positive.le _)
      have bound := Real.rpow_le_rpow_of_exponent_le scale_large (show 3 + displacement ≤ (4 : ℝ) by linarith)
      simpa only [Real.rpow_ofNat] using bound

theorem normalized_scalar_reduced_piece_flag_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ displacement : ℝ, 0 ≤ displacement → displacement ≤ 1 →
      ∀ m n : ℕ, ∀ matrix ∈ realSpecialScaling m n •
        realSpecialShrinkingBox m n (realSpecialDiagonalBox (1 / 64) 64),
      ∀ integral : GL3 IntegralAdeles, ∀ flag : Flags .plane,
        ‖eisensteinSummand (unitaryNormalize degree family) ((3 : ℂ) / 2 + (displacement : ℂ))
          (realSpecialIntegralSlice integral matrix) flag‖ ≤
          ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-3 - displacement) *
            ((2 : ℝ) ^ (4 * m + 8 * n) * bound) := by
  obtain ⟨scalarBound, scalar_nonnegative, scalar_bound⟩ := normalized_scalar_flag_transformed_row_bound flat
  obtain ⟨rowBound, row_large, row_bound⟩ := realSpecialShrinkingTranslate_row_bound
    (realSpecialDiagonalBox_isCompact (1 / 64) 64)
  refine ⟨rowBound ^ 4 * scalarBound, by positivity, ?_⟩
  intro displacement displacement_nonnegative displacement_small m n matrix member integral flag
  have real_slice : realGroup (realSpecialIntegralSlice integral matrix) = SpecialLinearGroup.toGL matrix := by
    simp only [realSpecialIntegralSlice, map_mul, realGroup_atInfinity, realGroup_atFinite, mul_one]
  have finite_slice : finiteGroup (realSpecialIntegralSlice integral matrix) ∈
      Set.range (GeneralLinearGroup.map integralEmbedding) := by
    simp only [realSpecialIntegralSlice, map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul]
    exact ⟨integral, rfl⟩
  have determinant : |(realGroup (realSpecialIntegralSlice integral matrix)).val.det| = 1 := by
    rw [real_slice]
    change |matrix.val.det| = 1
    rw [Matrix.SpecialLinearGroup.det_coe, abs_one]
  have exponent : -((3 : ℝ) / 2 + ((3 : ℂ) / 2 + (displacement : ℂ)).re) = -3 - displacement := by
    norm_num
    ring
  have estimate := scalar_bound ((3 : ℂ) / 2 + (displacement : ℂ)) (by norm_num; linarith)
    (realSpecialIntegralSlice integral matrix) finite_slice flag
  rw [determinant, Real.one_rpow, one_mul, real_slice, exponent] at estimate
  have scale_large : 1 ≤ (2 : ℝ) ^ (m + 2 * n) * rowBound :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) row_large
  have power_bound := negative_power_bound_of_scale
    (lt_of_lt_of_le zero_lt_one (planeFlagIntegerRow_norm_ge_one flag)) scale_large
    displacement_nonnegative displacement_small (row_bound m n matrix member _)
  have scale_power : ((2 : ℝ) ^ (m + 2 * n) * rowBound) ^ 4 =
      (2 : ℝ) ^ (4 * m + 8 * n) * rowBound ^ 4 := by
    rw [mul_pow, ← pow_mul]
    congr 2
    ring
  calc
    _ ≤ _ := estimate
    _ ≤ _ := mul_le_mul_of_nonneg_right power_bound scalar_nonnegative
    _ = _ := by rw [scale_power]; ring

theorem normalized_scalar_reduced_piece_boundary_bound
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ m n : ℕ, ∀ matrix ∈ realSpecialScaling m n •
        realSpecialShrinkingBox m n (realSpecialDiagonalBox (1 / 64) 64),
      ∀ integral : GL3 IntegralAdeles,
        displacement * ‖∑' flag, eisensteinSummand (unitaryNormalize degree family)
          ((3 : ℂ) / 2 + (displacement : ℂ)) (realSpecialIntegralSlice integral matrix) flag‖ ≤
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
  have sum_bound := (norm_tsum_le_tsum_norm norm_summable).trans
    (norm_summable.tsum_le_tsum bound_term majorant_summable)
  rw [tsum_mul_right] at sum_bound
  calc
    _ ≤ displacement * ((∑' flag : Flags .plane,
        ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-3 - displacement)) *
          ((2 : ℝ) ^ (4 * m + 8 * n) * coefficient)) := mul_le_mul_of_nonneg_left sum_bound positive.le
    _ = (2 : ℝ) ^ (4 * m + 8 * n) *
        ((displacement * ∑' flag : Flags .plane,
          ‖(fun index => (planeFlagIntegerRow flag index : ℝ))‖ ^ (-3 - displacement)) * coefficient) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right lattice_bound coefficient_nonnegative) (by positivity)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
