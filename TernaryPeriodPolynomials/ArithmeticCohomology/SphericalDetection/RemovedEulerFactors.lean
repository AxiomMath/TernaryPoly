module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.LValues

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Deleting the Euler factors at primes dividing `modulus`, on the series side. -/
def removeEulerCoefficients (coefficients : ℕ → ℂ) (modulus : ℕ) : ℕ → ℂ :=
  fun index => if index.Coprime modulus then coefficients index else 0

theorem removeEulerCoefficients_multiplicative
    (coefficients : ℕ → ℂ) (modulus : ℕ)
    (multiplicative : ∀ first second : ℕ, first.Coprime second →
      coefficients (first * second) = coefficients first * coefficients second)
    (first second : ℕ) (coprime : first.Coprime second) :
    removeEulerCoefficients coefficients modulus (first * second) =
      removeEulerCoefficients coefficients modulus first *
        removeEulerCoefficients coefficients modulus second := by
  by_cases first_kept : first.Coprime modulus <;>
    by_cases second_kept : second.Coprime modulus <;>
    simp only [removeEulerCoefficients, Nat.coprime_mul_iff_left, Nat.Coprime, first_kept, second_kept,
      and_self, and_false, false_and, ite_true, ite_false, mul_zero, zero_mul,
      multiplicative first second coprime]

theorem removeEulerCoefficients_norm_summable
    (coefficients : ℕ → ℂ) (modulus : ℕ) (argument : ℂ)
    (summable : Summable (fun index => ‖LSeries.term coefficients argument index‖)) :
    Summable (fun index =>
      ‖LSeries.term (removeEulerCoefficients coefficients modulus) argument index‖) := by
  apply Summable.of_nonneg_of_le (fun index => norm_nonneg _) _ summable
  intro index
  by_cases kept : index.Coprime modulus <;>
    simp only [LSeries.term_def, removeEulerCoefficients, Nat.Coprime, kept, ite_true, ite_false,
      zero_div, ite_self, norm_zero, le_refl, norm_nonneg]

theorem quadraticEulerSeries_removeFactors_eq_product
    (coefficients : ℕ → ℂ) (modulus : ℕ) (argument : ℂ)
    (trace determinant first_root second_root : Nat.Primes → ℂ)
    (initial : coefficients 1 = 1)
    (multiplicative : ∀ first second : ℕ, first.Coprime second →
      coefficients (first * second) = coefficients first * coefficients second)
    (first : ∀ place : Nat.Primes, coefficients place.val = trace place)
    (recurrence : ∀ (place : Nat.Primes) (exponent : ℕ),
      coefficients (place.val ^ (exponent + 2)) =
        trace place * coefficients (place.val ^ (exponent + 1)) -
          determinant place * coefficients (place.val ^ exponent))
    (root_sum : ∀ place, first_root place + second_root place = trace place)
    (root_product : ∀ place, first_root place * second_root place = determinant place)
    (summable : Summable (fun index => ‖LSeries.term coefficients argument index‖)) :
    LSeries (removeEulerCoefficients coefficients modulus) argument =
      ∏' place : {place : Nat.Primes // place.val.Coprime modulus},
        ((1 - first_root place.val * (place.val.val : ℂ) ^ (-argument)) *
          (1 - second_root place.val * (place.val.val : ℂ) ^ (-argument)))⁻¹ := by
  let keep : (Nat.Primes → ℂ) → Nat.Primes → ℂ :=
    fun values place => if place.val.Coprime modulus then values place else 0
  have removed_recurrence (place : Nat.Primes) (exponent : ℕ) :
      removeEulerCoefficients coefficients modulus (place.val ^ (exponent + 2)) =
        keep trace place *
            removeEulerCoefficients coefficients modulus (place.val ^ (exponent + 1)) -
          keep determinant place *
            removeEulerCoefficients coefficients modulus (place.val ^ exponent) := by
    by_cases kept : place.val.Coprime modulus
    · simpa only [removeEulerCoefficients, keep, ite_eq_left kept,
        ite_eq_left (kept.pow_left (exponent + 2)), ite_eq_left (kept.pow_left (exponent + 1)),
        ite_eq_left (kept.pow_left exponent)] using recurrence place exponent
    · have removed : ¬ (place.val ^ (exponent + 2)).Coprime modulus := by
        simpa only [Nat.coprime_pow_left_iff (by omega : 0 < exponent + 2)] using kept
      simp [removeEulerCoefficients, keep, kept, removed]
  rw [quadraticEulerSeries_eq_product
    (removeEulerCoefficients coefficients modulus) argument
    (keep trace) (keep determinant) (keep first_root) (keep second_root)
    (by simpa [removeEulerCoefficients] using initial)
    (removeEulerCoefficients_multiplicative coefficients modulus multiplicative)
    (by intro place; simp [removeEulerCoefficients, keep, first place])
    removed_recurrence
    (by intro place; by_cases kept : place.val.Coprime modulus
        · simpa only [keep, ite_eq_left kept] using root_sum place
        · simp only [keep, ite_eq_right kept, add_zero])
    (by intro place; by_cases kept : place.val.Coprime modulus
        · simpa only [keep, ite_eq_left kept] using root_product place
        · simp only [keep, ite_eq_right kept, mul_zero])
    (removeEulerCoefficients_norm_summable coefficients modulus argument summable)]
  let factors : Nat.Primes → ℂ := fun place =>
    ((1 - first_root place * (place.val : ℂ) ^ (-argument)) *
      (1 - second_root place * (place.val : ℂ) ^ (-argument)))⁻¹
  change _ = ∏' place : {place : Nat.Primes // place.val.Coprime modulus}, factors place.val
  apply Eq.trans _ (tprod_subtype {place : Nat.Primes | place.val.Coprime modulus} factors).symm
  apply tprod_congr
  intro place
  by_cases kept : place.val.Coprime modulus <;>
    simp only [keep, Set.mulIndicator, Set.mem_ofPred_eq, Nat.Coprime, kept, ite_true, ite_false,
      factors, zero_mul, sub_zero, mul_one, inv_one]

theorem scaledEulerRoot_eq_cpow (root : Nat.Primes → ℂ) (argument : ℝ)
    (place : Nat.Primes) :
    scaledEulerRoot root argument place = root place * (place.val : ℂ) ^ (-(argument : ℂ)) := by
  unfold scaledEulerRoot
  rw [← Complex.ofReal_neg]
  have real_power := Complex.ofReal_cpow
    (x := (place.val : ℝ)) (by exact_mod_cast place.property.pos.le) (-argument)
  exact congrArg (fun value : ℂ => root place * value)
    (by simpa only [Complex.ofReal_natCast] using real_power)

theorem quadraticEulerSeries_removeFactors_ne_zero
    (coefficients : ℕ → ℂ) (modulus : ℕ) (weight argument : ℝ)
    (trace determinant first_root second_root : Nat.Primes → ℂ)
    (initial : coefficients 1 = 1)
    (multiplicative : ∀ first second : ℕ, first.Coprime second →
      coefficients (first * second) = coefficients first * coefficients second)
    (first : ∀ place : Nat.Primes, coefficients place.val = trace place)
    (recurrence : ∀ (place : Nat.Primes) (exponent : ℕ),
      coefficients (place.val ^ (exponent + 2)) =
        trace place * coefficients (place.val ^ (exponent + 1)) -
          determinant place * coefficients (place.val ^ exponent))
    (root_sum : ∀ place, first_root place + second_root place = trace place)
    (root_product : ∀ place, first_root place * second_root place = determinant place)
    (summable : Summable (fun index => ‖LSeries.term coefficients argument index‖))
    (first_bound : ∀ place, ‖first_root place‖ ≤ (place.val : ℝ) ^ (weight / 2))
    (second_bound : ∀ place, ‖second_root place‖ ≤ (place.val : ℝ) ^ (weight / 2))
    (argument_bound : weight / 2 + 1 < argument) :
    LSeries (removeEulerCoefficients coefficients modulus) argument ≠ 0 := by
  rw [quadraticEulerSeries_removeFactors_eq_product coefficients modulus argument
    trace determinant first_root second_root initial multiplicative first recurrence
    root_sum root_product summable]
  simpa only [scaledEulerRoot_eq_cpow] using
    outerEulerProduct_restricted_ne_zero first_root second_root weight argument
      (fun place => place.val.Coprime modulus) first_bound second_bound argument_bound

end TernaryPeriodPolynomials.SphericalDetection.Helpers
