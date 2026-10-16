module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.ThetaDistortion

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactChartOperators

theorem bounds (point : GeneralLinearGroup (Fin 3) ℝ) (rightSet : Set BinaryRealGL) (compact : IsCompact rightSet) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ right ∈ rightSet, ∀ (argument : ℂ) (positive : 0 < argument.im),
      1 ≤ argument.im → |argument.re| ≤ 1 →
        ‖(realTransform point (unit argument positive * right)).toContinuousLinearMap‖ ≤ constant * argument.im ∧
        ‖(realTransform point (unit argument positive * right)).symm.toContinuousLinearMap‖ ≤ constant ∧
        RealFourierLinear.factor (realTransform point (unit argument positive * right)) ≤ constant := by
  obtain ⟨rightBound, rightBounded⟩ := compact.exists_bound_of_continuousOn
    (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℝ)).continuousOn
  obtain ⟨inverseBound, inverseBounded⟩ := compact.exists_bound_of_continuousOn
    (Units.continuous_val.comp (continuous_inv : Continuous (fun right : BinaryRealGL => right⁻¹))).continuousOn
  obtain ⟨determinantBound, determinantBounded⟩ := compact.exists_bound_of_continuousOn
    (Units.continuous_val.comp (continuous_inv : Continuous (fun right : BinaryRealGL => right⁻¹))).matrix_det.continuousOn
  let direct := 2 * ‖RectangularOperatorBounds.bilinear‖ * ‖point⁻¹.val‖ * max rightBound 0
  let inverse := 2 * ‖RectangularOperatorBounds.bilinear‖ * ‖point.val‖ * max inverseBound 0
  let determinant := |point.val.det| ^ 2 * max determinantBound 0 ^ 3
  have directNonnegative : 0 ≤ direct := by dsimp [direct]; positivity
  have inverseNonnegative : 0 ≤ inverse := by dsimp [inverse]; positivity
  have determinantNonnegative : 0 ≤ determinant := by dsimp [determinant]; positivity
  refine ⟨direct + inverse + determinant, by positivity, ?_⟩
  intro right membership argument positive height horizontal
  have directEstimate : ‖(realTransform point (unit argument positive * right)).toContinuousLinearMap‖ ≤ direct * argument.im := by
    apply (CuspChartOperators.transform_bound point right argument positive height horizontal).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      ((rightBounded right membership).trans (le_max_left _ _)) (by positivity)) positive.le
  have inverseEstimate : ‖(realTransform point (unit argument positive * right)).symm.toContinuousLinearMap‖ ≤ inverse := by
    apply (CuspChartOperators.inverse_bound point right argument positive height horizontal).trans
    exact mul_le_mul_of_nonneg_left ((inverseBounded right membership).trans (le_max_left _ _)) (by positivity)
  have determinantEstimate : RealFourierLinear.factor (realTransform point (unit argument positive * right)) ≤ determinant := by
    apply (CuspChartOperators.factor_bound point right argument positive height).trans
    have inverseDet : right⁻¹.val.det = right.val.det⁻¹ := by
      simpa only [GeneralLinearGroup.val_det_apply, Units.val_inv_eq_inv_val] using
        congrArg Units.val (map_inv GeneralLinearGroup.det right)
    have bound : |right.val.det|⁻¹ ≤ max determinantBound 0 := by
      rw [← abs_inv, ← inverseDet]
      exact (determinantBounded right membership).trans (le_max_left _ _)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr (abs_nonneg _)) bound 3) (sq_nonneg _)
  refine ⟨directEstimate.trans (mul_le_mul_of_nonneg_right (by linarith) positive.le),
    inverseEstimate.trans (by linarith), determinantEstimate.trans (by linarith)⟩

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactChartOperators
