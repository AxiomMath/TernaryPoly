module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.SphereEulerSeries

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem crossRecurrence_tsum_relation (first second : ℕ → ℂ) (scale determinant : ℂ)
    (recurrence : ∀ index, scale * second (index + 1) = first (index + 2) + determinant * first index)
    (first_summable : Summable first) (second_summable : Summable second) :
    scale * (∑' index, second index) = scale * second 0 +
      (1 + determinant) * (∑' index, first index) - first 0 - first 1 := by
  have first_shift : Summable (fun index => first (index + 1)) := (summable_nat_add_iff 1).mpr first_summable
  have second_shift : Summable (fun index => second (index + 1)) := (summable_nat_add_iff 1).mpr second_summable
  have first_twice : Summable (fun index => first (index + 2)) := (summable_nat_add_iff 2).mpr first_summable
  have identity : scale * (∑' index, second (index + 1)) =
      (∑' index, first (index + 2)) + determinant * (∑' index, first index) := by
    rw [← second_shift.tsum_mul_left]
    simp_rw [recurrence]
    rw [first_twice.tsum_add (first_summable.mul_left determinant), first_summable.tsum_mul_left]
  have first_sum := first_summable.tsum_eq_zero_add
  have shifted_sum := first_shift.tsum_eq_zero_add
  have second_sum := second_summable.tsum_eq_zero_add
  simp only [Nat.zero_add, Nat.add_assoc] at shifted_sum
  linear_combination scale * second_sum + identity - first_sum - shifted_sum

theorem sphereSeries_operator_relation (first second : ℕ → ℂ) (prime central scale : ℂ)
    (prime_nonzero : prime ≠ 0) (initial : second 0 = first 1)
    (next : second 1 = first 2 + (prime + 1) * central * first 0)
    (recurrence : ∀ index, second (index + 2) = first (index + 3) + prime * central * first (index + 1))
    (first_summable : Summable (fun index => (1 - prime⁻¹) * first (index + 1) * scale ^ (index + 1)))
    (second_summable : Summable (fun index => (1 - prime⁻¹) * second (index + 1) * scale ^ (index + 1))) :
    (1 + prime * central * scale ^ 2) *
        (first 0 + ∑' index, (1 - prime⁻¹) * first (index + 1) * scale ^ (index + 1)) -
      scale * (second 0 + ∑' index, (1 - prime⁻¹) * second (index + 1) * scale ^ (index + 1)) =
      (1 + central / prime * scale ^ 2) * first 0 - scale / prime * first 1 := by
  have identity := crossRecurrence_tsum_relation
    (fun index => (1 - prime⁻¹) * first (index + 1) * scale ^ (index + 1))
    (fun index => (1 - prime⁻¹) * second (index + 1) * scale ^ (index + 1))
    scale (prime * central * scale ^ 2) (fun index => by
      simp only [Nat.add_assoc, recurrence, pow_add, pow_one]
      ring) first_summable second_summable
  simp only [Nat.zero_add, Nat.reduceAdd, pow_one, next] at identity
  rw [initial]
  calc
    _ = (1 + prime * central * scale ^ 2) * first 0 - scale * first 1 +
        (1 - prime⁻¹) * first 1 * scale - (1 - prime⁻¹) * (prime + 1) * central * first 0 * scale ^ 2 := by
      linear_combination -identity
    _ = _ := by field_simp; ring

end TernaryPeriodPolynomials.SphericalDetection.Helpers
