module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.RingTheory.Nilpotent.Exp

@[expose] public section


open Finset

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The finite average of the nilpotent exponential along a unit interval. -/
def nilpotentExponentialAverage (operator : A) (cutoff : ℕ) : A :=
  ∑ index ∈ range cutoff, ((index + 1).factorial : ℚ)⁻¹ • operator ^ index

theorem nilpotentExponentialAverage_commute (operator : A) (cutoff : ℕ) :
    Commute operator (nilpotentExponentialAverage operator cutoff) := by
  apply Commute.sum_right
  intro index _
  exact (Commute.refl operator).pow_right index |>.smul_right _

theorem nilpotentExponentialAverage_commute_of_commute (first second : A)
    (commute : Commute first second) (cutoff : ℕ) :
    Commute first (nilpotentExponentialAverage second cutoff) := by
  apply Commute.sum_right
  intro index _
  exact (commute.pow_right index).smul_right _

theorem nilpotentExponentialAverage_remainder (operator : A) (cutoff : ℕ) :
    nilpotentExponentialAverage operator (cutoff + 1) - 1 =
      operator * ∑ index ∈ range cutoff, ((index + 2).factorial : ℚ)⁻¹ • operator ^ index := by
  rw [nilpotentExponentialAverage, Finset.sum_range_succ']
  simp only [zero_add, Nat.factorial_one, Nat.cast_one, inv_one, pow_zero, one_smul, add_sub_cancel_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [mul_smul_comm, ← pow_succ']

theorem nilpotentExponentialAverage_isUnit (operator : A) (nilpotent : IsNilpotent operator)
    (cutoff : ℕ) : IsUnit (nilpotentExponentialAverage operator (cutoff + 1)) := by
  have commutes : Commute operator
      (∑ index ∈ range cutoff, ((index + 2).factorial : ℚ)⁻¹ • operator ^ index) := by
    apply Commute.sum_right
    intro index _
    exact (Commute.refl operator).pow_right index |>.smul_right _
  have remainder_nilpotent : IsNilpotent (nilpotentExponentialAverage operator (cutoff + 1) - 1) := by
    rw [nilpotentExponentialAverage_remainder]
    exact commutes.isNilpotent_mul_right nilpotent
  simpa only [sub_add_cancel] using remainder_nilpotent.isUnit_add_one

theorem nilpotent_exponential_sub_one (operator : A) (cutoff : ℕ)
    (nilpotent : operator ^ (cutoff + 1) = 0) :
    IsNilpotent.exp operator - 1 = operator * nilpotentExponentialAverage operator (cutoff + 1) := by
  have next : operator ^ (cutoff + 1 + 1) = 0 := by rw [pow_succ, nilpotent, zero_mul]
  rw [IsNilpotent.exp_eq_sum next, Finset.sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, add_sub_cancel_right]
  rw [nilpotentExponentialAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [mul_smul_comm, ← pow_succ']

end TernaryPeriodPolynomials.SphericalDetection.Helpers
