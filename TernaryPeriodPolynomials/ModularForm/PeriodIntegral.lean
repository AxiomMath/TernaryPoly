module

public import TernaryPeriodPolynomials.PeriodPolynomial.Defs
public import TernaryPeriodPolynomials.ModularForm.Endpoint.Ray

@[expose] public section


/-!
# The period polynomial is the contour integral

The definition `periodPolynomial n h` (`Revision/Defs/Periods.lean`) is given by its
coefficients, `binom(n,j) (-1)^{n-j} i^{j+1} ∫₀^∞ h(iy) y^j dy` at `X^{n-j} Y^j`
(`eq:period-critical-coefficients`). The paper defines `r_h(X,Y) = ∫_0^{i∞} h(τ)(τY - X)^n dτ`.
This module proves that the two agree: for every evaluation point `(X, Y) = (x, y)` the
polynomial equals the absolutely convergent integral along the imaginary axis `τ = i t`,
`dτ = i dt`.

Written by Claude Opus 5.5.
-/

open MvPolynomial MeasureTheory Complex
open UpperHalfPlane hiding I

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.PeriodIntegral

open TernaryPeriodPolynomials.Argument

/-- The imaginary-axis moment with the differential `d(it) = i dt` is `i^{m+1}` times
`periodMoment`. -/
theorem axisMoment_eq_periodMoment (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2)) (m : ℕ) :
    TernaryPoly.BinaryCuspPeriod.axisMoment (d := n) h m = I ^ (m + 1) * periodMoment h m := by
  rw [TernaryPoly.BinaryCuspPeriod.axisMoment, periodMoment, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [Set.mem_Ioi] at ht
  dsimp only
  rw [imaginaryAxisValue, dite_eq_left ht,
    UpperHalfPlane.ofComplex_apply_of_im_pos (z := I * (t : ℂ)) (by simpa using ht)]
  simp only [mul_pow, pow_succ]
  ring

/-- **The period polynomial is the period integral.** For every `x, y`,
`r_h(x, y) = ∫_0^{i∞} h(τ)(τ y - x)^n dτ`, parametrized by `τ = i t`; the integral converges
absolutely (`TernaryPoly.BinaryCuspPeriod.rayIntegrand_integrable`). -/
theorem periodPolynomial_eval_eq_integral (n : ℕ) (h : CuspForm levelOne ((n : ℤ) + 2))
    (x y : ℂ) :
    eval ![x, y] (periodPolynomial n h) =
      ∫ t : ℝ in Set.Ioi 0, h (ofComplex (I * t)) * (I * t * y - x) ^ n * I := by
  have hray : (fun t : ℝ => h (ofComplex (I * t)) * (I * t * y - x) ^ n * I) =
      TernaryPoly.BinaryCuspPeriod.rayIntegrand (d := n) h x y := by
    funext t
    rfl
  rw [hray, ← TernaryPoly.BinaryCuspPeriod.eval_period_eq_integral,
    TernaryPoly.BinaryCuspPeriod.eval_period]
  simp only [periodPolynomial, map_sum, map_mul, eval_C, map_pow, eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [TernaryPoly.BinaryCuspPeriod.periodCoefficient_eq_axisMoment, axisMoment_eq_periodMoment]
  have h1 : n + 1 - 1 - j = n - j := by omega
  have h2 : n - (n - j) = j := by omega
  rw [h1, h2, Nat.choose_symm hjn]
  ring

end TernaryPeriodPolynomials.Argument.Statements.PeriodIntegral
