module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.OuterEulerValues

@[expose] public section


namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem le_of_uniform_pow_bound {value radius constant : ℝ}
    (radius_positive : 0 < radius)
    (power_bound : ∀ exponent : ℕ, value ^ exponent ≤ constant * radius ^ exponent) :
    value ≤ radius := by
  by_contra outside
  have large : 1 < value / radius := (lt_div_iff₀ radius_positive).mpr (by
    simpa using lt_of_not_ge outside)
  obtain ⟨exponent, too_large⟩ := pow_unbounded_of_one_lt constant large
  have normalized_bound : (value / radius) ^ exponent ≤ constant := by
    rw [div_pow]
    exact (div_le_iff₀ (pow_pos radius_positive exponent)).mpr (power_bound exponent)
  exact (not_lt_of_ge normalized_bound) too_large

theorem quadraticRecurrence_root_pow_identity
    (coefficients : ℕ → ℂ) (trace determinant root : ℂ)
    (initial : coefficients 0 = 1)
    (first : coefficients 1 = trace)
    (recurrence : ∀ exponent,
      coefficients (exponent + 2) = trace * coefficients (exponent + 1) -
        determinant * coefficients exponent)
    (root_equation : root ^ 2 - trace * root + determinant = 0) :
    ∀ exponent : ℕ,
      coefficients (exponent + 1) - (trace - root) * coefficients exponent =
        root ^ (exponent + 1) := by
  intro exponent
  induction exponent with
  | zero => simp [initial, first]
  | succ exponent induction_hypothesis =>
    have determinant_identity : determinant = trace * root - root ^ 2 := by
      linear_combination root_equation
    rw [show exponent + 1 + 1 = exponent + 2 by omega, recurrence,
      determinant_identity]
    calc
      trace * coefficients (exponent + 1) - (trace * root - root ^ 2) *
          coefficients exponent - (trace - root) * coefficients (exponent + 1) =
        root * (coefficients (exponent + 1) - (trace - root) * coefficients exponent) :=
          by ring
      _ = root * root ^ (exponent + 1) := by rw [induction_hypothesis]
      _ = root ^ (exponent + 2) := by ring

theorem quadraticRecurrence_root_norm_le
    (coefficients : ℕ → ℂ) (trace determinant root : ℂ) (radius constant : ℝ)
    (radius_positive : 0 < radius)
    (initial : coefficients 0 = 1)
    (first : coefficients 1 = trace)
    (recurrence : ∀ exponent,
      coefficients (exponent + 2) = trace * coefficients (exponent + 1) -
        determinant * coefficients exponent)
    (root_equation : root ^ 2 - trace * root + determinant = 0)
    (coefficient_bound : ∀ exponent,
      ‖coefficients exponent‖ ≤ constant * radius ^ exponent) :
    ‖root‖ ≤ radius := by
  let enlarged := max 1 (constant * (radius + ‖trace - root‖) / radius)
  apply le_of_uniform_pow_bound radius_positive
  intro exponent
  cases exponent with
  | zero =>
    simpa only [pow_zero, mul_one] using le_max_left 1
      (constant * (radius + ‖trace - root‖) / radius)
  | succ exponent =>
    have identity := quadraticRecurrence_root_pow_identity coefficients trace determinant
      root initial first recurrence root_equation exponent
    have power_bound : ‖root‖ ^ (exponent + 1) ≤
        constant * (radius + ‖trace - root‖) * radius ^ exponent := by
      calc
        ‖root‖ ^ (exponent + 1) =
            ‖coefficients (exponent + 1) - (trace - root) * coefficients exponent‖ := by
          rw [identity, norm_pow]
        _ ≤ ‖coefficients (exponent + 1)‖ +
            ‖trace - root‖ * ‖coefficients exponent‖ := by
          simpa only [norm_mul] using norm_sub_le
            (coefficients (exponent + 1)) ((trace - root) * coefficients exponent)
        _ ≤ constant * radius ^ (exponent + 1) +
            ‖trace - root‖ * (constant * radius ^ exponent) :=
          add_le_add (coefficient_bound (exponent + 1))
            (mul_le_mul_of_nonneg_left (coefficient_bound exponent) (norm_nonneg _))
        _ = constant * (radius + ‖trace - root‖) * radius ^ exponent := by
          rw [pow_succ]
          ring
    calc
      ‖root‖ ^ (exponent + 1) ≤
          constant * (radius + ‖trace - root‖) * radius ^ exponent := power_bound
      _ = (constant * (radius + ‖trace - root‖) / radius) *
          radius ^ (exponent + 1) := by
        rw [pow_succ]
        field_simp
      _ ≤ enlarged * radius ^ (exponent + 1) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg radius_positive.le _)

theorem primePowerRecurrence_root_norm_le
    (coefficients : ℕ → ℂ) (trace determinant root : ℂ)
    (place : Nat.Primes) (weight constant : ℝ)
    (initial : coefficients 0 = 1)
    (first : coefficients 1 = trace)
    (recurrence : ∀ exponent,
      coefficients (exponent + 2) = trace * coefficients (exponent + 1) -
        determinant * coefficients exponent)
    (root_equation : root ^ 2 - trace * root + determinant = 0)
    (coefficient_bound : ∀ exponent,
      ‖coefficients exponent‖ ≤ constant * ((place.val : ℝ) ^ exponent) ^ (weight / 2)) :
    ‖root‖ ≤ (place.val : ℝ) ^ (weight / 2) := by
  have prime_positive : (0 : ℝ) < place.val := by exact_mod_cast place.property.pos
  apply quadraticRecurrence_root_norm_le coefficients trace determinant root
    ((place.val : ℝ) ^ (weight / 2)) constant
    (Real.rpow_pos_of_pos prime_positive _) initial first recurrence root_equation
  intro exponent
  have bound := coefficient_bound exponent
  rwa [← Real.rpow_natCast_mul prime_positive.le,
    mul_comm (exponent : ℝ) (weight / 2),
    Real.rpow_mul_natCast prime_positive.le] at bound

theorem outerCriticalEulerProducts_ne_zero_of_primePowerRecurrences
    (coefficients : Nat.Primes → ℕ → ℂ)
    (trace determinant first_root second_root : Nat.Primes → ℂ)
    (weight : ℝ) (constant : Nat.Primes → ℝ)
    (weight_bound : 6 < weight)
    (initial : ∀ place, coefficients place 0 = 1)
    (first : ∀ place, coefficients place 1 = trace place)
    (recurrence : ∀ place exponent,
      coefficients place (exponent + 2) = trace place * coefficients place (exponent + 1) -
        determinant place * coefficients place exponent)
    (first_equation : ∀ place,
      first_root place ^ 2 - trace place * first_root place + determinant place = 0)
    (second_equation : ∀ place,
      second_root place ^ 2 - trace place * second_root place + determinant place = 0)
    (coefficient_bound : ∀ place exponent,
      ‖coefficients place exponent‖ ≤
        constant place * ((place.val : ℝ) ^ exponent) ^ (weight / 2)) :
    (∏' place : {place : Nat.Primes // place.val ≠ 3},
      ((1 - scaledEulerRoot first_root (weight - 2) place.val) *
        (1 - scaledEulerRoot second_root (weight - 2) place.val))⁻¹) ≠ 0 ∧
    (∏' place : {place : Nat.Primes // place.val ≠ 3},
      ((1 - scaledEulerRoot first_root (weight - 1) place.val) *
        (1 - scaledEulerRoot second_root (weight - 1) place.val))⁻¹) ≠ 0 := by
  apply outerCriticalEulerProducts_away_three_ne_zero first_root second_root weight
    weight_bound
  · intro place
    exact primePowerRecurrence_root_norm_le (coefficients place) (trace place)
      (determinant place) (first_root place) place weight (constant place)
      (initial place) (first place) (recurrence place) (first_equation place)
      (coefficient_bound place)
  · intro place
    exact primePowerRecurrence_root_norm_le (coefficients place) (trace place)
      (determinant place) (second_root place) place weight (constant place)
      (initial place) (first place) (recurrence place) (second_equation place)
      (coefficient_bound place)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
