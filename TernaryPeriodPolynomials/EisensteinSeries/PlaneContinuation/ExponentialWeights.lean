module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ShellDecay

@[expose] public section


namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ExponentialWeights

theorem reweight (value constant exponent weight : ℝ) (bounded : Real.exp exponent * value ≤ constant) :
    Real.exp weight * value ≤ constant * Real.exp (weight - exponent) := by
  calc
    _ = Real.exp (weight - exponent) * (Real.exp exponent * value) := by
      rw [← mul_assoc, ← Real.exp_add, sub_add_cancel]
    _ ≤ Real.exp (weight - exponent) * constant := mul_le_mul_of_nonneg_left bounded (Real.exp_pos _).le
    _ = _ := mul_comm _ _

theorem two_ends (value largeConstant smallConstant scalarOrder heightOrder weight scalarLog heightLog shift : ℝ)
    (largeNonnegative : 0 ≤ largeConstant) (smallNonnegative : 0 ≤ smallConstant)
    (large : 0 ≤ scalarLog → Real.exp (scalarOrder * scalarLog + heightOrder * heightLog) * value ≤ largeConstant)
    (small : scalarLog ≤ 0 → Real.exp (7 * scalarLog + heightOrder * heightLog) * value ≤ smallConstant) :
    Real.exp (weight * (2 * scalarLog + heightLog - shift)) * value ≤
      ((largeConstant + smallConstant) * Real.exp (-weight * shift)) *
        (Real.exp (-min (scalarOrder - 2 * weight) (2 * weight - 7) * |scalarLog|) *
          Real.exp (-(heightOrder - weight) * heightLog)) := by
  let rate := min (scalarOrder - 2 * weight) (2 * weight - 7)
  have rateLarge : rate ≤ scalarOrder - 2 * weight := min_le_left _ _
  have rateSmall : rate ≤ 2 * weight - 7 := min_le_right _ _
  have factorization : ((largeConstant + smallConstant) * Real.exp (-weight * shift)) *
      (Real.exp (-rate * |scalarLog|) * Real.exp (-(heightOrder - weight) * heightLog)) =
      (largeConstant + smallConstant) * Real.exp (-weight * shift - rate * |scalarLog| - (heightOrder - weight) * heightLog) := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  rw [factorization]
  by_cases sign : 0 ≤ scalarLog
  · apply (reweight value largeConstant _ _ (large sign)).trans
    apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by linarith)
    rw [abs_of_nonneg sign]
    nlinarith
  · have negative : scalarLog ≤ 0 := (lt_of_not_ge sign).le
    apply (reweight value smallConstant _ _ (small negative)).trans
    apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by linarith)
    rw [abs_of_nonpos negative]
    nlinarith

theorem two_rates (value largeConstant smallConstant scalarOrder smallOrder heightOrder weight scalarLog heightLog shift : ℝ)
    (largeNonnegative : 0 ≤ largeConstant) (smallNonnegative : 0 ≤ smallConstant)
    (large : 0 ≤ scalarLog → Real.exp (scalarOrder * scalarLog + heightOrder * heightLog) * value ≤ largeConstant)
    (small : scalarLog ≤ 0 → Real.exp (smallOrder * scalarLog + heightOrder * heightLog) * value ≤ smallConstant) :
    Real.exp (weight * (2 * scalarLog + heightLog - shift)) * value ≤
      ((largeConstant + smallConstant) * Real.exp (-weight * shift)) *
        (Real.exp (-min (scalarOrder - 2 * weight) (2 * weight - smallOrder) * |scalarLog|) *
          Real.exp (-(heightOrder - weight) * heightLog)) := by
  let rate := min (scalarOrder - 2 * weight) (2 * weight - smallOrder)
  have rateLarge : rate ≤ scalarOrder - 2 * weight := min_le_left _ _
  have rateSmall : rate ≤ 2 * weight - smallOrder := min_le_right _ _
  have factorization : ((largeConstant + smallConstant) * Real.exp (-weight * shift)) *
      (Real.exp (-rate * |scalarLog|) * Real.exp (-(heightOrder - weight) * heightLog)) =
      (largeConstant + smallConstant) * Real.exp (-weight * shift - rate * |scalarLog| - (heightOrder - weight) * heightLog) := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  rw [factorization]
  by_cases sign : 0 ≤ scalarLog
  · apply (reweight value largeConstant _ _ (large sign)).trans
    apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by linarith)
    rw [abs_of_nonneg sign]
    nlinarith
  · have negative : scalarLog ≤ 0 := (lt_of_not_ge sign).le
    apply (reweight value smallConstant _ _ (small negative)).trans
    apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by linarith)
    rw [abs_of_nonpos negative]
    nlinarith

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ExponentialWeights
