module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem polynomial_coeff_eq_scaled_derivative (polynomial : Polynomial R) (index : ℕ) :
    polynomial.coeff index = (index.factorial : ℚ)⁻¹ •
      Polynomial.eval 0 ((Polynomial.derivative : Polynomial R → Polynomial R)^[index] polynomial) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative,
    Nat.zero_add, Nat.descFactorial_self, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  have nonzero : (index.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero index)
  rw [inv_mul_cancel₀ nonzero, one_smul]

theorem polynomial_coeff_zero_of_iterated_derivative_zero (polynomial : Polynomial R)
    (cutoff : ℕ)
    (vanishes : (Polynomial.derivative : Polynomial R → Polynomial R)^[cutoff] polynomial = 0)
    (index : ℕ) (large : cutoff ≤ index) : polynomial.coeff index = 0 := by
  have higher : (Polynomial.derivative : Polynomial R → Polynomial R)^[index] polynomial = 0 := by
    rw [← Nat.sub_add_cancel large, Function.iterate_add_apply, vanishes, Polynomial.iterate_derivative_zero]
  rw [polynomial_coeff_eq_scaled_derivative polynomial index, higher, Polynomial.eval_zero, smul_zero]

theorem polynomial_finite_taylor_one (polynomial : Polynomial R) (cutoff : ℕ)
    (positive : 0 < cutoff)
    (vanishes : (Polynomial.derivative : Polynomial R → Polynomial R)^[cutoff] polynomial = 0) :
    Polynomial.eval 1 polynomial = ∑ index ∈ Finset.range cutoff,
      (index.factorial : ℚ)⁻¹ •
        Polynomial.eval 0 ((Polynomial.derivative : Polynomial R → Polynomial R)^[index] polynomial) := by
  have bound : polynomial.natDegree < cutoff := by
    by_contra failed
    have large := Nat.le_of_not_gt failed
    have zero := polynomial_coeff_zero_of_iterated_derivative_zero polynomial cutoff vanishes
      polynomial.natDegree large
    have polynomial_zero := Polynomial.leadingCoeff_eq_zero.mp zero
    rw [polynomial_zero, Polynomial.natDegree_zero] at large
    omega
  rw [Polynomial.eval_eq_sum_range' bound]
  apply Finset.sum_congr rfl
  intro index _
  rw [one_pow, mul_one, polynomial_coeff_eq_scaled_derivative]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
