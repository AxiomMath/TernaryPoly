module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Real.Cuspidality

@[expose] public section


open MeasureTheory

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.MeanZeroBound

theorem norm_le_of_deriv_bound (function derivative : ℝ → ℂ) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (differentiable : ∀ point, HasDerivAt function (derivative point) point)
    (derivativeBound : ∀ point, ‖derivative point‖ ≤ bound) (point : ℝ)
    (meanZero : ∫ parameter in point..point + 3, function parameter = 0) :
    ‖function point‖ ≤ 3 * bound := by
  have continuous : Continuous function := continuous_iff_continuousAt.mpr
    (fun point => (differentiable point).continuousAt)
  have differenceBound (parameter : ℝ) (membership : parameter ∈ Set.uIoc point (point + 3)) :
      ‖function point - function parameter‖ ≤ 3 * bound := by
    have estimate := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun value _ => (differentiable value).differentiableAt)
      (fun value _ => by rw [(differentiable value).deriv]; exact derivativeBound value)
      (Set.mem_univ parameter) (Set.mem_univ point)
    rw [Set.uIoc_of_le (by linarith : point ≤ point + 3)] at membership
    have distanceBound : ‖point - parameter‖ ≤ 3 := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [membership.1])]
      linarith [membership.2]
    exact estimate.trans ((mul_le_mul_of_nonneg_left distanceBound nonnegative).trans_eq (mul_comm _ _))
  have integralBound := intervalIntegral.norm_integral_le_of_norm_le_const differenceBound
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) (continuous.intervalIntegrable _ _),
    intervalIntegral.integral_const, meanZero, sub_zero, norm_smul, Real.norm_eq_abs] at integralBound
  have distanceEquality : |point + 3 - point| = 3 := by rw [add_sub_cancel_left]; norm_num
  rw [distanceEquality] at integralBound
  nlinarith

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.MeanZeroBound
