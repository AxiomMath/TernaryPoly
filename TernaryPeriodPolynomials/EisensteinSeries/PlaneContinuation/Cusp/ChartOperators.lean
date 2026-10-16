module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.OperatorBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspChartOperators

theorem norm_product (left right : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖left * right‖ ≤ 2 * ‖left‖ * ‖right‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro row column
  calc
    ‖(left * right) row column‖ ≤ ∑ index : Fin 2, ‖left row index * right index column‖ := by
      rw [Matrix.mul_apply]
      exact norm_sum_le _ _
    _ ≤ ∑ _index : Fin 2, ‖left‖ * ‖right‖ := by
      apply Finset.sum_le_sum
      intro index _
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm left)
        (Matrix.norm_entry_le_entrywise_sup_norm right) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

theorem norm_chart (argument : ℂ) (positive : 0 < argument.im)
    (height : 1 ≤ argument.im) (horizontal : |argument.re| ≤ 1) :
    ‖(unit argument positive).val‖ ≤ argument.im := by
  apply (Matrix.norm_le_iff positive.le).mpr
  intro row column
  fin_cases row <;> fin_cases column
  · change |argument.im| ≤ argument.im
    rw [abs_of_pos positive]
  · exact horizontal.trans height
  · change ‖(0 : ℝ)‖ ≤ argument.im
    simpa only [norm_zero] using positive.le
  · change ‖(1 : ℝ)‖ ≤ argument.im
    simpa only [norm_one] using height

theorem norm_chart_inverse (argument : ℂ) (positive : 0 < argument.im)
    (height : 1 ≤ argument.im) (horizontal : |argument.re| ≤ 1) :
    ‖(unit argument positive)⁻¹.val‖ ≤ 1 := by
  have inverse : |argument.im⁻¹| ≤ 1 := by
    rw [abs_inv, abs_of_pos positive]
    exact inv_le_one_of_one_le₀ height
  have quotient : |-argument.re / argument.im| ≤ 1 := by
    rw [abs_div, abs_neg, abs_of_pos positive]
    exact (div_le_one positive).mpr (horizontal.trans height)
  apply (Matrix.norm_le_iff zero_le_one).mpr
  intro row column
  fin_cases row <;> fin_cases column
  · exact inverse
  · exact quotient
  · change ‖(0 : ℝ)‖ ≤ 1
    norm_num
  · change ‖(1 : ℝ)‖ ≤ 1
    norm_num

theorem norm_chart_right (argument : ℂ) (positive : 0 < argument.im)
    (height : 1 ≤ argument.im) (horizontal : |argument.re| ≤ 1) (right : BinaryRealGL) :
    ‖(unit argument positive * right).val‖ ≤ 2 * argument.im * ‖right.val‖ := by
  exact (norm_product _ _).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_chart argument positive height horizontal) (by norm_num)) (norm_nonneg _))

theorem norm_chart_right_inverse (argument : ℂ) (positive : 0 < argument.im)
    (height : 1 ≤ argument.im) (horizontal : |argument.re| ≤ 1) (right : BinaryRealGL) :
    ‖(unit argument positive * right)⁻¹.val‖ ≤ 2 * ‖right⁻¹.val‖ := by
  rw [_root_.mul_inv_rev, Units.val_mul]
  exact (norm_product _ _).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (norm_chart_inverse argument positive height horizontal) (mul_nonneg (by norm_num) (norm_nonneg right⁻¹.val)))

theorem transform_bound (point : GeneralLinearGroup (Fin 3) ℝ) (right : BinaryRealGL)
    (argument : ℂ) (positive : 0 < argument.im) (height : 1 ≤ argument.im) (horizontal : |argument.re| ≤ 1) :
    ‖(realTransform point (unit argument positive * right)).toContinuousLinearMap‖ ≤
      (2 * ‖RectangularOperatorBounds.bilinear‖ * ‖point⁻¹.val‖ * ‖right.val‖) * argument.im := by
  apply (RectangularOperatorBounds.norm_transform _ _).trans
  calc
    _ ≤ ‖RectangularOperatorBounds.bilinear‖ * ‖point⁻¹.val‖ * (2 * argument.im * ‖right.val‖) :=
      mul_le_mul_of_nonneg_left (norm_chart_right argument positive height horizontal right) (by positivity)
    _ = _ := by ring

theorem inverse_bound (point : GeneralLinearGroup (Fin 3) ℝ) (right : BinaryRealGL)
    (argument : ℂ) (positive : 0 < argument.im) (height : 1 ≤ argument.im) (horizontal : |argument.re| ≤ 1) :
    ‖(realTransform point (unit argument positive * right)).symm.toContinuousLinearMap‖ ≤
      2 * ‖RectangularOperatorBounds.bilinear‖ * ‖point.val‖ * ‖right⁻¹.val‖ := by
  apply (RectangularOperatorBounds.norm_inverse _ _).trans
  calc
    _ ≤ ‖RectangularOperatorBounds.bilinear‖ * ‖point.val‖ * (2 * ‖right⁻¹.val‖) :=
      mul_le_mul_of_nonneg_left (norm_chart_right_inverse argument positive height horizontal right) (by positivity)
    _ = _ := by ring

theorem factor_bound (point : GeneralLinearGroup (Fin 3) ℝ) (right : BinaryRealGL)
    (argument : ℂ) (positive : 0 < argument.im) (height : 1 ≤ argument.im) :
    RealFourierLinear.factor (realTransform point (unit argument positive * right)) ≤
      |point.val.det| ^ 2 * |right.val.det|⁻¹ ^ 3 := by
  rw [RectangularFourierLinear.factor_eq, Units.val_mul, Matrix.det_mul]
  change |point.val.det| ^ 2 * |(matrix argument).det * right.val.det|⁻¹ ^ 3 ≤ _
  rw [matrix_det, abs_mul, abs_of_pos positive, mul_inv, mul_pow]
  have inversePower : argument.im⁻¹ ^ 3 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr positive.le) (inv_le_one_of_one_le₀ height)
  calc
    _ ≤ |point.val.det| ^ 2 * (1 * |right.val.det|⁻¹ ^ 3) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right inversePower (by positivity)) (by positivity)
    _ = _ := by rw [one_mul]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspChartOperators
