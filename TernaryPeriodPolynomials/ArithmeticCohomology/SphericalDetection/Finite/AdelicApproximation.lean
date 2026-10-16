module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PrimeReduction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Every integral adele has an integer representative modulo any nonzero integer. -/
theorem integralAdeles_exists_integer_residue (modulus : ℕ) (positive : 0 < modulus)
    (value : IntegralAdeles) : ∃ representative : ℤ,
      (modulus : IntegralAdeles) ∣ value - representative := by
  induction modulus using Nat.strong_induction_on generalizing value with
  | h modulus induction =>
    by_cases one : modulus = 1
    · exact ⟨0, by simp [one]⟩
    obtain ⟨prime, prime_property, factor, equality⟩ := Nat.exists_prime_and_dvd one
    subst modulus
    have factor_positive : 0 < factor := by nlinarith [prime_property.pos]
    have factor_small : factor < prime * factor := by nlinarith [prime_property.two_le]
    let prime_index : Nat.Primes := ⟨prime, prime_property⟩
    let : NeZero prime := ⟨prime_property.ne_zero⟩
    let residue : ℤ := (integralPrimeReduction prime_index value).val
    have prime_divides : (prime : IntegralAdeles) ∣ value - residue := by
      apply (integralPrimeReduction_zero_iff_dvd prime_index _).mp
      simp only [residue, Int.cast_natCast, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    obtain ⟨quotient, quotient_eq⟩ := prime_divides
    obtain ⟨other, remainder, remainder_eq⟩ := induction factor factor_small factor_positive quotient
    refine ⟨residue + prime * other, remainder, ?_⟩
    push_cast
    linear_combination quotient_eq + (prime : IntegralAdeles) * remainder_eq

theorem finiteAdeles_integral_iff (value : FiniteAdeles) :
    value ∈ Set.range integralEmbedding ↔ ∀ place : FinitePlace,
      value place ∈ place.adicCompletionIntegers ℚ := by
  constructor
  · rintro ⟨integral, rfl⟩ place
    exact (integral place).property
  · intro integral
    exact ⟨fun place => ⟨value place, integral place⟩, rfl⟩

/-- A single nonzero integer clears all the finitely many local denominators of a finite adele. -/
theorem finiteAdeles_exists_integer_denominator (value : FiniteAdeles) :
    ∃ denominator : ℤ, denominator ≠ 0 ∧
      value * (denominator : FiniteAdeles) ∈ Set.range integralEmbedding := by
  classical
  have locally (place : FinitePlace) : ∃ denominator : ℤ, denominator ≠ 0 ∧
      value place * (denominator : place.adicCompletion ℚ) ∈ place.adicCompletionIntegers ℚ := by
    obtain ⟨denominator, regular, integral⟩ :=
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers place (value place)
    refine ⟨denominator, mem_nonZeroDivisors_iff_ne_zero.mp regular, ?_⟩
    simpa only [Algebra.cast, eq_intCast] using integral
  choose denominators nonzero integral using locally
  let bad := {place : FinitePlace | value place ∉ place.adicCompletionIntegers ℚ}
  have bad_finite : bad.Finite := Filter.eventually_cofinite.mp value.property
  let places := bad_finite.toFinset
  refine ⟨∏ place ∈ places, denominators place, Finset.prod_ne_zero_iff.mpr (fun place _ => nonzero place), ?_⟩
  apply (finiteAdeles_integral_iff _).mpr
  intro place
  change value place * ((∏ place ∈ places, denominators place : ℤ) : place.adicCompletion ℚ) ∈ _
  by_cases bad_place : place ∈ places
  · obtain ⟨factor, factor_eq⟩ := Finset.dvd_prod_of_mem denominators bad_place
    rw [factor_eq, Int.cast_mul, ← mul_assoc]
    exact (place.adicCompletionIntegers ℚ).toSubring.mul_mem (integral place)
      (intCast_mem _ factor)
  · have value_integral : value place ∈ place.adicCompletionIntegers ℚ := by
      simpa only [places, Set.Finite.mem_toFinset, bad, Set.mem_ofPred_eq, not_not] using bad_place
    exact (place.adicCompletionIntegers ℚ).toSubring.mul_mem value_integral
      (intCast_mem _ _)

theorem finiteAdeles_exists_nat_denominator (value : FiniteAdeles) :
    ∃ denominator : ℕ, 0 < denominator ∧
      value * (denominator : FiniteAdeles) ∈ Set.range integralEmbedding := by
  obtain ⟨denominator, nonzero, integral, equality⟩ := finiteAdeles_exists_integer_denominator value
  refine ⟨denominator.natAbs ^ 2, pow_pos (Int.natAbs_pos.mpr nonzero) _,
    integral * (denominator : IntegralAdeles), ?_⟩
  rw [map_mul, map_intCast, equality, mul_assoc]
  congr 1
  have square : (denominator.natAbs : ℤ) ^ 2 = denominator * denominator := by
    rw [Int.natCast_natAbs, sq_abs, pow_two]
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, Nat.cast_pow] using
    congrArg (fun integer : ℤ => (integer : FiniteAdeles)) square.symm

theorem finiteAdeles_exists_common_denominator {index : Type*} [Fintype index]
    (values : index → FiniteAdeles) : ∃ denominator : ℕ, 0 < denominator ∧
      ∀ position, values position * (denominator : FiniteAdeles) ∈ Set.range integralEmbedding := by
  classical
  choose denominators positive integral using fun position => finiteAdeles_exists_nat_denominator (values position)
  refine ⟨∏ position, denominators position, Finset.prod_pos (fun position _ => positive position), ?_⟩
  intro position
  obtain ⟨factor, factor_eq⟩ := Finset.dvd_prod_of_mem denominators (Finset.mem_univ position)
  obtain ⟨original, original_eq⟩ := integral position
  refine ⟨original * (factor : IntegralAdeles), ?_⟩
  rw [map_mul, map_natCast, original_eq, factor_eq, Nat.cast_mul, mul_assoc]

/-- Additive strong approximation modulo the full integral lattice. -/
theorem finiteAdeles_exists_rational_add_integral (value : FiniteAdeles) :
    ∃ (rational : ℚ) (integral : IntegralAdeles),
      value = algebraMap ℚ FiniteAdeles rational + integralEmbedding integral := by
  obtain ⟨denominator, positive, integral, integral_eq⟩ := finiteAdeles_exists_nat_denominator value
  obtain ⟨numerator, remainder, remainder_eq⟩ := integralAdeles_exists_integer_residue denominator positive integral
  refine ⟨(numerator : ℚ) / denominator, remainder, ?_⟩
  have denominator_unit : IsUnit (denominator : FiniteAdeles) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (ne_of_gt positive)) : IsUnit (denominator : ℚ)).map
        (algebraMap ℚ FiniteAdeles)
  apply denominator_unit.mul_right_cancel
  have mapped := congrArg integralEmbedding remainder_eq
  simp only [map_sub, map_mul, map_intCast, map_natCast, integral_eq] at mapped
  have rational_cancel : algebraMap ℚ FiniteAdeles ((numerator : ℚ) / denominator) * denominator = numerator := by
    rw [← map_natCast (algebraMap ℚ FiniteAdeles) denominator, ← map_mul,
      div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (ne_of_gt positive)), map_intCast]
  rw [add_mul, rational_cancel]
  linear_combination mapped

end TernaryPeriodPolynomials.SphericalDetection.Helpers
