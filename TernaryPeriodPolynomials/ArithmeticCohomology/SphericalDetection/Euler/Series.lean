module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.EulerValues
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.ModularForms.LFunction
public import Mathlib.NumberTheory.LSeries.Basic

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem quadraticRecurrence_tsum_mul_factor
    (coefficients : ℕ → ℂ) (trace determinant : ℂ)
    (initial : coefficients 0 = 1) (first : coefficients 1 = trace)
    (recurrence : ∀ exponent,
      coefficients (exponent + 2) = trace * coefficients (exponent + 1) -
        determinant * coefficients exponent)
    (summable : Summable coefficients) :
    (1 - trace + determinant) * (∑' exponent, coefficients exponent) = 1 := by
  have successor_summable : Summable (fun exponent => coefficients (exponent + 1)) :=
    (summable_nat_add_iff 1).mpr summable
  have initial_sum := summable.tsum_eq_zero_add
  have successor_sum := successor_summable.tsum_eq_zero_add
  have recurrence_sum :
      (∑' exponent, coefficients (exponent + 2)) =
        trace * (∑' exponent, coefficients (exponent + 1)) -
          determinant * (∑' exponent, coefficients exponent) := by
    simp_rw [recurrence]
    rw [(successor_summable.mul_left trace).tsum_sub
      (summable.mul_left determinant), successor_summable.tsum_mul_left,
      summable.tsum_mul_left]
  simp only [initial, first] at initial_sum successor_sum
  have shifted :
      (∑' exponent, coefficients (exponent + 1 + 1)) =
        (∑' exponent, coefficients (exponent + 2)) := by
    simp only [Nat.add_assoc]
  rw [shifted, recurrence_sum] at successor_sum
  linear_combination
    (1 - trace) * initial_sum + successor_sum

theorem quadraticRecurrence_tsum_eq_inverse
    (coefficients : ℕ → ℂ) (trace determinant : ℂ)
    (initial : coefficients 0 = 1) (first : coefficients 1 = trace)
    (recurrence : ∀ exponent,
      coefficients (exponent + 2) = trace * coefficients (exponent + 1) -
        determinant * coefficients exponent)
    (summable : Summable coefficients) :
    (∑' exponent, coefficients exponent) = (1 - trace + determinant)⁻¹ := by
  exact (inv_eq_of_mul_eq_one_right
    (quadraticRecurrence_tsum_mul_factor coefficients trace determinant
      initial first recurrence summable)).symm

theorem quadraticRecurrence_weighted_tsum_eq_inverse
    (coefficients : ℕ → ℂ) (trace determinant scale : ℂ)
    (initial : coefficients 0 = 1) (first : coefficients 1 = trace)
    (recurrence : ∀ exponent,
      coefficients (exponent + 2) = trace * coefficients (exponent + 1) -
        determinant * coefficients exponent)
    (summable : Summable (fun exponent => coefficients exponent * scale ^ exponent)) :
    (∑' exponent, coefficients exponent * scale ^ exponent) =
      (1 - trace * scale + determinant * scale ^ 2)⁻¹ := by
  apply quadraticRecurrence_tsum_eq_inverse
    (fun exponent => coefficients exponent * scale ^ exponent)
    (trace * scale) (determinant * scale ^ 2)
  · simp [initial]
  · simp [first]
  · intro exponent
    rw [recurrence, pow_add, pow_succ]
    ring
  · exact summable

theorem quadraticEulerSeries_eq_product
    (coefficients : ℕ → ℂ) (argument : ℂ)
    (trace determinant first_root second_root : Nat.Primes → ℂ)
    (initial : coefficients 1 = 1)
    (multiplicative : ∀ first_index second_index : ℕ,
      first_index.Coprime second_index →
        coefficients (first_index * second_index) =
          coefficients first_index * coefficients second_index)
    (first : ∀ place : Nat.Primes, coefficients place.val = trace place)
    (recurrence : ∀ (place : Nat.Primes) (exponent : ℕ),
      coefficients (place.val ^ (exponent + 2)) =
        trace place * coefficients (place.val ^ (exponent + 1)) -
          determinant place * coefficients (place.val ^ exponent))
    (root_sum : ∀ place, first_root place + second_root place = trace place)
    (root_product : ∀ place, first_root place * second_root place = determinant place)
    (summable : Summable (fun index => ‖LSeries.term coefficients argument index‖)) :
    LSeries coefficients argument =
      ∏' place, ((1 - first_root place * (place.val : ℂ) ^ (-argument)) *
        (1 - second_root place * (place.val : ℂ) ^ (-argument)))⁻¹ := by
  have term_summable : Summable (LSeries.term coefficients argument) :=
    summable.of_norm
  have prime_terms (place : Nat.Primes) (exponent : ℕ) :
      LSeries.term coefficients argument (place.val ^ exponent) =
        coefficients (place.val ^ exponent) *
          ((place.val : ℂ) ^ (-argument)) ^ exponent := by
    have prime_power_nonzero : place.val ^ exponent ≠ 0 :=
      pow_ne_zero _ place.property.ne_zero
    rw [LSeries.term_def, ite_eq_right prime_power_nonzero, div_eq_mul_inv,
      ← Complex.cpow_neg, Nat.cast_pow,
      ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  have local_sum (place : Nat.Primes) :
      (∑' exponent, LSeries.term coefficients argument (place.val ^ exponent)) =
        ((1 - first_root place * (place.val : ℂ) ^ (-argument)) *
          (1 - second_root place * (place.val : ℂ) ^ (-argument)))⁻¹ := by
    have local_summable := term_summable.comp_injective
      (Nat.pow_right_injective place.property.two_le)
    have weighted_summable : Summable (fun exponent =>
        coefficients (place.val ^ exponent) *
          ((place.val : ℂ) ^ (-argument)) ^ exponent) :=
      local_summable.congr (prime_terms place)
    simp_rw [prime_terms]
    rw [quadraticRecurrence_weighted_tsum_eq_inverse
      (fun exponent => coefficients (place.val ^ exponent))
      (trace place) (determinant place) ((place.val : ℂ) ^ (-argument))
      (by simpa using initial) (by simpa using first place)
      (recurrence place) weighted_summable]
    congr 1
    rw [← root_sum place, ← root_product place]
    ring
  have term_initial : LSeries.term coefficients argument 1 = 1 := by
    simp [initial]
  have term_multiplicative {first_index second_index : ℕ}
      (coprime : first_index.Coprime second_index) :
      LSeries.term coefficients argument (first_index * second_index) =
        LSeries.term coefficients argument first_index *
          LSeries.term coefficients argument second_index := by
    by_cases first_zero : first_index = 0
    · simp [first_zero, LSeries.term_def]
    by_cases second_zero : second_index = 0
    · simp [second_zero, LSeries.term_def]
    rw [LSeries.term_def, ite_eq_right (mul_ne_zero first_zero second_zero),
      LSeries.term_def, ite_eq_right first_zero, LSeries.term_def, ite_eq_right second_zero,
      multiplicative first_index second_index coprime, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, mul_div_mul_comm]
  have euler := EulerProduct.eulerProduct_tprod term_initial
    (fun {_ _} coprime => term_multiplicative coprime) summable
    (by simp [LSeries.term_def])
  change (∑' index, LSeries.term coefficients argument index) = _
  rw [← euler]
  exact tprod_congr local_sum

end TernaryPeriodPolynomials.SphericalDetection.Helpers
