module

public import TernaryPeriodPolynomials.ModularForm.Periods.ExampleDegreeTenCuspBridge
public import TernaryPeriodPolynomials.ModularForm.Periods.EvenPeriodEval

@[expose] public section



/-!
# Axis evaluations of the even period, and the bridge to `evenPeriodPart`

`eval ![0,y] (period f)` and `eval ![x,0] (period f)` each collapse to the single surviving
term of the defining sum `period_eq_sum_CXX` (every other term carries a `0 ^ j` factor with
`j ≠ 0`), giving the clean monomials `periodCoefficient f 0 * y ^ d` and
`periodCoefficient f d * x ^ d`. Combined with `two_mul_eval_evenPeriod` this gives the same
shape for `evenPeriod`, and `eval_evenPeriod_boundary_reflection` then forces
`periodCoefficient f d = - periodCoefficient f 0`: the fact that ultimately makes the axis
corrections in `normalizedEvenPeriodPart` cancel. We also record that `evenPeriod` (defined in
`EvenPeriodEval.lean`) literally equals the `evenPeriodPart`, via the existing
`period_eq_periodPolynomial` bridge.
-/

noncomputable section
open MvPolynomial

namespace TernaryPeriodPolynomials.Argument.CuspForms

open TernaryPoly.BinaryCuspPeriod

theorem eval_period_axis_zero {d : ℕ} (f : Forms d) (y : ℂ) :
    eval ![0, y] (period f) = periodCoefficient f 0 * y ^ d := by
  rw [period_eq_sum_CXX, map_sum, Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    simp [zero_pow hj0]
  · intro h0
    exact absurd (Finset.mem_range.mpr (by omega)) h0

theorem eval_period_axis_last {d : ℕ} (f : Forms d) (x : ℂ) :
    eval ![x, 0] (period f) = periodCoefficient f d * x ^ d := by
  rw [period_eq_sum_CXX, map_sum, Finset.sum_eq_single d]
  · simp
  · intro j hj hjd
    simp only [Finset.mem_range] at hj
    have hne : d - j ≠ 0 := by omega
    simp [zero_pow hne]
  · intro hd
    exact absurd (Finset.mem_range.mpr (by omega)) hd

theorem eval_evenPeriod_axis_zero {d : ℕ} (f : Forms d) (y : ℂ) :
    eval ![0, y] (evenPeriod f) = periodCoefficient f 0 * y ^ d := by
  have h := two_mul_eval_evenPeriod f 0 y
  rw [neg_zero, eval_period_axis_zero] at h
  linear_combination h / 2

theorem eval_evenPeriod_axis_last {d : ℕ} (hd : Even d) (f : Forms d) (x : ℂ) :
    eval ![x, 0] (evenPeriod f) = periodCoefficient f d * x ^ d := by
  have h := two_mul_eval_evenPeriod f x 0
  rw [eval_period_axis_last, eval_period_axis_last, hd.neg_pow] at h
  linear_combination h / 2

theorem periodCoefficient_boundary {d : ℕ} (hd : Even d) (f : Forms d) :
    periodCoefficient f d = - periodCoefficient f 0 := by
  have h := eval_evenPeriod_boundary_reflection hd f
  rw [eval_evenPeriod_axis_last hd f 1, eval_evenPeriod_axis_zero f 1] at h
  simpa using h

theorem evenPeriod_eq_evenPeriodPart {d : ℕ} (f : Forms d) :
    evenPeriod f = TernaryPeriodPolynomials.Argument.evenPeriodPart d f := by
  rw [evenPeriod, TernaryPeriodPolynomials.Argument.evenPeriodPart, period_eq_periodPolynomial]

end TernaryPeriodPolynomials.Argument.CuspForms
