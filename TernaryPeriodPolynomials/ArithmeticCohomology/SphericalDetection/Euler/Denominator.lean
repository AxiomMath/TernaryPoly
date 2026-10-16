module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.SphereEulerSeries

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem quadraticEulerDenominator_ne_zero_of_identity (prime trace central scale value integral : ℂ)
    (prime_nonzero : prime ≠ 0) (prime_not_one : prime ≠ 1)
    (central_unitary : ‖central‖ = 1) (scale_small : ‖scale‖ < 1) (value_nonzero : value ≠ 0)
    (identity : (1 - trace * scale + prime * central * scale ^ 2) * integral =
      (1 - trace / prime * scale + central / prime * scale ^ 2) * value) :
    1 - trace * scale + prime * central * scale ^ 2 ≠ 0 := by
  intro zero
  have numerator : 1 - trace / prime * scale + central / prime * scale ^ 2 = 0 := by
    rw [zero, zero_mul] at identity
    exact (mul_eq_zero.mp identity.symm).resolve_right value_nonzero
  have product : (prime - 1) * (central * scale ^ 2 - 1) = 0 := by
    have multiplied := congrArg (fun number : ℂ => prime * number) numerator
    field_simp at multiplied
    linear_combination zero - multiplied
  have unit : central * scale ^ 2 = 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left (sub_ne_zero.mpr prime_not_one))
  have norm_unit := congrArg norm unit
  rw [norm_mul, norm_pow, central_unitary, one_mul, norm_one] at norm_unit
  have small : ‖scale‖ ^ 2 < 1 := by nlinarith [norm_nonneg scale]
  linarith

end TernaryPeriodPolynomials.SphericalDetection.Helpers
