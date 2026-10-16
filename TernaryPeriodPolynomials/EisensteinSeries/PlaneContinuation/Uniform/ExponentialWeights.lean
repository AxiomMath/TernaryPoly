module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ExponentialWeights

@[expose] public section


namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformExponentialWeights

theorem two_rates (value largeConstant smallConstant scalarOrder heightOrder weight weightBound scalarLog heightLog shift : ℝ)
    (largeNonnegative : 0 ≤ largeConstant) (smallNonnegative : 0 ≤ smallConstant)
    (boundedWeight : |weight| ≤ weightBound) (heightNonnegative : 0 ≤ heightLog)
    (large : 0 ≤ scalarLog → Real.exp (scalarOrder * scalarLog + heightOrder * heightLog) * value ≤ largeConstant)
    (small : scalarLog ≤ 0 → Real.exp (-scalarOrder * scalarLog + heightOrder * heightLog) * value ≤ smallConstant) :
    Real.exp (weight * (2 * scalarLog + heightLog - shift)) * value ≤
      ((largeConstant + smallConstant) * Real.exp (weightBound * |shift|)) *
        (Real.exp (-(scalarOrder - 2 * weightBound) * |scalarLog|) *
          Real.exp (-(heightOrder - weightBound) * heightLog)) := by
  have scalarBound : 2 * weight * scalarLog ≤ 2 * weightBound * |scalarLog| := by
    calc
      _ ≤ |2 * weight * scalarLog| := le_abs_self _
      _ = 2 * |weight| * |scalarLog| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ _ := by gcongr
  have heightBound : weight * heightLog ≤ weightBound * heightLog :=
    mul_le_mul_of_nonneg_right ((le_abs_self _).trans boundedWeight) heightNonnegative
  have shiftBound : -weight * shift ≤ weightBound * |shift| := by
    calc
      _ ≤ |-weight * shift| := le_abs_self _
      _ = |weight| * |shift| := by rw [abs_mul, abs_neg]
      _ ≤ _ := by gcongr
  have factorization : ((largeConstant + smallConstant) * Real.exp (weightBound * |shift|)) *
      (Real.exp (-(scalarOrder - 2 * weightBound) * |scalarLog|) *
        Real.exp (-(heightOrder - weightBound) * heightLog)) =
      (largeConstant + smallConstant) * Real.exp
        (weightBound * |shift| - (scalarOrder - 2 * weightBound) * |scalarLog| - (heightOrder - weightBound) * heightLog) := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  rw [factorization]
  by_cases sign : 0 ≤ scalarLog
  · apply (ExponentialWeights.reweight value largeConstant _ _ (large sign)).trans
    apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by linarith)
    rw [abs_of_nonneg sign] at scalarBound ⊢
    nlinarith
  · have negative : scalarLog ≤ 0 := (lt_of_not_ge sign).le
    apply (ExponentialWeights.reweight value smallConstant _ _ (small negative)).trans
    apply mul_le_mul (by linarith) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by linarith)
    rw [abs_of_nonpos negative] at scalarBound ⊢
    nlinarith

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformExponentialWeights
