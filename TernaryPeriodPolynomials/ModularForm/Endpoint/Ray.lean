module

public import TernaryPeriodPolynomials.ModularForm.ModularPeriod.Symmetry
public import TernaryPeriodPolynomials.ModularForm.ModularPeriod.Segments

@[expose] public section


noncomputable section
open Complex MvPolynomial MeasureTheory
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspPeriod

/-- Actual differential of the m-th imaginary-axis moment, including dz=i dt. -/
def axisIntegrand {d : ℕ} (f : Forms d) (m : ℕ) (t : ℝ) : ℂ :=
  f (ofComplex (I*t)) * (I*(t : ℂ))^m * I

/-- Each actual axis moment is absolutely integrable, by the genuine cusp Mellin theorem. -/
theorem axisIntegrand_integrable {d : ℕ} (f : Forms d) (m : ℕ) :
    IntegrableOn (axisIntegrand f m) (Set.Ioi 0) := by
  have hm := moment_convergent f (m+1 : ℕ)
  simp only [MellinConvergent, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    cpow_natCast, smul_eq_mul] at hm
  have he : axisIntegrand f m = (fun t : ℝ => I^(m+1) * ((t : ℂ)^m * f (ofComplex (I*t)))) := by
    funext t
    simp only [axisIntegrand, mul_pow, pow_succ]
    ring
  rw [he]
  exact hm.const_mul _

/-- Actual vertical differential of the evaluated period polynomial. -/
def rayIntegrand {d : ℕ} (f : Forms d) (x y : ℂ) (t : ℝ) : ℂ :=
  periodIntegrand f x y (I*t) * I

/-- Exact finite binomial expansion of the actual vertical differential. -/
theorem rayIntegrand_binomial {d : ℕ} (f : Forms d) (x y : ℂ) (t : ℝ) :
    rayIntegrand f x y t = ∑ j ∈ Finset.range (d+1),
      ((d.choose j : ℂ) * (-1)^j * x^j * y^(d-j)) * axisIntegrand f (d-j) t := by
  unfold rayIntegrand periodIntegrand
  rw [show I*(t : ℂ)*y-x = -x+(I*t)*y by ring, add_pow,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [neg_pow]
  simp only [axisIntegrand, mul_pow]
  ring

/-- The full vertical period integral is absolutely convergent for all evaluations x,y. -/
theorem rayIntegrand_integrable {d : ℕ} (f : Forms d) (x y : ℂ) :
    IntegrableOn (rayIntegrand f x y) (Set.Ioi 0) := by
  have he : rayIntegrand f x y = (fun t => ∑ j ∈ Finset.range (d+1),
      ((d.choose j : ℂ) * (-1)^j * x^j * y^(d-j)) * axisIntegrand f (d-j) t) :=
    funext (rayIntegrand_binomial f x y)
  rw [he]
  exact integrable_finsetSum _ (fun j _ => (axisIntegrand_integrable f (d-j)).const_mul _)

/-- Literal evaluation of the finite full period polynomial. -/
theorem eval_period {d : ℕ} (f : Forms d) (x y : ℂ) :
    eval ![x,y] (period f) = ∑ j ∈ Finset.range (d+1),
      periodCoefficient f j * x^j * y^(d-j) := by
  simp [period, monomial_exponent]

/-- The finite Mellin polynomial is exactly the actual improper vertical integral. -/
theorem eval_period_eq_integral {d : ℕ} (f : Forms d) (x y : ℂ) :
    eval ![x,y] (period f) = ∫ t : ℝ in Set.Ioi 0, rayIntegrand f x y t := by
  rw [eval_period]
  simp_rw [rayIntegrand_binomial]
  rw [integral_finsetSum _ (fun j _ => (axisIntegrand_integrable f (d-j)).const_mul _)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul, periodCoefficient_eq_axisMoment]
  change ((d.choose j : ℂ) * (-1)^j * axisMoment f (d-j)) * x^j * y^(d-j) =
    ((d.choose j : ℂ) * (-1)^j * x^j * y^(d-j)) * axisMoment f (d-j)
  ring

end TernaryPoly.BinaryCuspPeriod
