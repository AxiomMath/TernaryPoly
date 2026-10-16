module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.RationalNorm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem integralAdeles_nat_decomposition (modulus : ℕ) (nonzero : modulus ≠ 0) :
    ∀ value : IntegralAdeles, ∃ (representative : ℕ) (quotient : IntegralAdeles),
      value = representative + (modulus : IntegralAdeles) * quotient := by
  let property (modulus : ℕ) : Prop :=
    ∀ value : IntegralAdeles, ∃ (representative : ℕ) (quotient : IntegralAdeles),
      value = representative + (modulus : IntegralAdeles) * quotient
  have one_property : property 1 := by
    intro value
    exact ⟨0, value, by simp⟩
  have prime_property (prime : Nat.Primes) : property prime.val := by
    intro value
    let representative := (primeIntegralReduction prime value).val
    have reduction_zero : primeIntegralReduction prime (value - representative) = 0 := by
      simp [representative]
    obtain ⟨quotient, quotient_spec⟩ :=
      (primeIntegralReduction_eq_zero_iff prime _).mp reduction_zero
    exact ⟨representative, quotient, by rw [← quotient_spec]; ring⟩
  have product_property (first second : ℕ)
      (first_property : property first) (second_property : property second) :
      property (first * second) := by
    intro value
    obtain ⟨first_representative, first_quotient, first_spec⟩ := first_property value
    obtain ⟨second_representative, second_quotient, second_spec⟩ := second_property first_quotient
    refine ⟨first_representative + first * second_representative, second_quotient, ?_⟩
    rw [first_spec, second_spec]
    push_cast
    ring
  have power_property (prime : Nat.Primes) (power : ℕ) : property (prime.val ^ power) := by
    induction power with
    | zero => simpa only [pow_zero] using one_property
    | succ power induction_hypothesis =>
      rw [pow_succ]
      exact product_property _ _ induction_hypothesis (prime_property prime)
  change property modulus
  revert nonzero
  refine Nat.recOnPrimePow ?_ ?_ ?_ modulus
  · intro zero_nonzero
    exact (zero_nonzero rfl).elim
  · intro _
    exact one_property
  · intro remaining prime power prime_spec _ _ induction_hypothesis product_nonzero
    have remaining_nonzero : remaining ≠ 0 := by
      intro remaining_zero
      simp only [remaining_zero, mul_zero, ne_eq, not_true_eq_false] at product_nonzero
    exact product_property _ _ (power_property ⟨prime, prime_spec⟩ power)
      (induction_hypothesis remaining_nonzero)

theorem integralAdeles_bounded_nat_decomposition
    (modulus : ℕ) (positive : 0 < modulus) (value : IntegralAdeles) :
    ∃ (representative : ℕ) (quotient : IntegralAdeles),
      representative < modulus ∧ value = representative + (modulus : IntegralAdeles) * quotient := by
  obtain ⟨representative, quotient, decomposition⟩ :=
    integralAdeles_nat_decomposition modulus positive.ne' value
  refine ⟨representative % modulus, quotient + (representative / modulus : ℕ),
    Nat.mod_lt _ positive, ?_⟩
  have division : ((representative % modulus : ℕ) : IntegralAdeles) +
      (modulus : IntegralAdeles) * (representative / modulus : ℕ) = representative := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      congrArg (fun natural : ℕ => (natural : IntegralAdeles))
        (Nat.mod_add_div representative modulus)
  rw [decomposition, ← division]
  ring

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
