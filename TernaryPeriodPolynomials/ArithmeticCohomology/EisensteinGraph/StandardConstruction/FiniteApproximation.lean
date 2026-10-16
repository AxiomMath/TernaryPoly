module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RationalNorm

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic IsDedekindDomain

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FiniteApproximation

theorem lattice_mem_iff (value : FiniteAdeles) :
    value ∈ Set.range integralEmbedding ↔
      ∀ place : FinitePlace, value place ∈ place.adicCompletionIntegers ℚ := by
  constructor
  · rintro ⟨integral, rfl⟩ place
    exact (integral place).property
  · intro integral
    exact ⟨fun place => ⟨value place, integral place⟩, rfl⟩

theorem integral_residue (number : ℕ) (nonzero : number ≠ 0)
    (value : IntegralAdeles) :
    ∃ remainder : ℕ, ∃ quotient : IntegralAdeles,
      value = (remainder : IntegralAdeles) + (number : IntegralAdeles) * quotient := by
  have induction : ∀ number : ℕ, number ≠ 0 → ∀ value : IntegralAdeles,
      ∃ remainder : ℕ, ∃ quotient : IntegralAdeles,
        value = (remainder : IntegralAdeles) + (number : IntegralAdeles) * quotient := by
    apply Nat.prime_composite_induction
    · intro nonzero
      exact False.elim (nonzero rfl)
    · intro _ value
      exact ⟨0, value, by simp⟩
    · intro prime isPrime _ value
      let : NeZero prime := ⟨isPrime.ne_zero⟩
      let residue := PrimeLattice.residue prime isPrime value
      have vanishes : PrimeLattice.residue prime isPrime
          (value - (residue.val : IntegralAdeles)) = 0 := by
        rw [map_sub, map_natCast, ZMod.natCast_zmod_val]
        exact sub_self _
      obtain ⟨quotient, equality⟩ :=
        (PrimeLattice.residue_zero_iff prime isPrime _).mp vanishes
      exact ⟨residue.val, quotient, by rw [equality]; ring⟩
    · intro first firstBound firstInduction second secondBound secondInduction _ value
      obtain ⟨firstRemainder, firstQuotient, firstEquality⟩ :=
        firstInduction (by omega) value
      obtain ⟨secondRemainder, secondQuotient, secondEquality⟩ :=
        secondInduction (by omega) firstQuotient
      refine ⟨firstRemainder + first * secondRemainder, secondQuotient, ?_⟩
      rw [firstEquality, secondEquality]
      push_cast
      ring
  exact induction number nonzero value

theorem local_denominator (place : FinitePlace) (value : place.adicCompletion ℚ) :
    ∃ denominator : ℤ, denominator ≠ 0 ∧
      value * (denominator : place.adicCompletion ℚ) ∈ place.adicCompletionIntegers ℚ := by
  obtain ⟨denominator, nonzero, integral⟩ :=
    HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers
      (K := ℚ) place value
  refine ⟨denominator, mem_nonZeroDivisors_iff_ne_zero.mp nonzero, ?_⟩
  change value * (algebraMap ℤ (place.adicCompletion ℚ)) denominator ∈ _ at integral
  rw [RingHom.eq_intCast' (algebraMap ℤ (place.adicCompletion ℚ))] at integral
  exact integral

theorem common_denominator (value : FiniteAdeles) :
    ∃ denominator : ℤ, denominator ≠ 0 ∧
      value * (denominator : FiniteAdeles) ∈ Set.range integralEmbedding := by
  classical
  have finite := value.eventually
  change Set.Finite {place : FinitePlace |
    value place ∉ place.adicCompletionIntegers ℚ} at finite
  have clears : ∀ places : Finset FinitePlace,
      ∃ denominator : ℤ, denominator ≠ 0 ∧ ∀ place ∈ places,
        value place * (denominator : place.adicCompletion ℚ) ∈
          place.adicCompletionIntegers ℚ := by
    intro places
    induction places using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | @insert place places _ induction =>
      obtain ⟨first, firstNonzero, firstIntegral⟩ := local_denominator place (value place)
      obtain ⟨second, secondNonzero, secondIntegral⟩ := induction
      refine ⟨first * second, mul_ne_zero firstNonzero secondNonzero, ?_⟩
      intro other membership
      rcases Finset.mem_insert.mp membership with rfl | membership
      · simpa only [Int.cast_mul, ← mul_assoc] using
          (other.adicCompletionIntegers ℚ).mul_mem _ _ firstIntegral
            (intCast_mem _ second)
      · have integral := (other.adicCompletionIntegers ℚ).mul_mem _ _
          (secondIntegral other membership)
          (intCast_mem _ first)
        convert integral using 1
        push_cast
        ring
  obtain ⟨denominator, nonzero, integral⟩ := clears finite.toFinset
  refine ⟨denominator, nonzero, (lattice_mem_iff _).mpr ?_⟩
  intro place
  change (finiteEvaluation place) (value * (denominator : FiniteAdeles)) ∈ _
  rw [map_mul, map_intCast]
  by_cases membership : value place ∈ place.adicCompletionIntegers ℚ
  · exact (place.adicCompletionIntegers ℚ).mul_mem _ _ membership
      (intCast_mem _ denominator)
  · exact integral place (finite.mem_toFinset.mpr membership)

theorem common_natural_denominator (value : FiniteAdeles) :
    ∃ denominator : ℕ, denominator ≠ 0 ∧
      value * (denominator : FiniteAdeles) ∈ Set.range integralEmbedding := by
  obtain ⟨denominator, nonzero, integral, equality⟩ := common_denominator value
  have square : ((denominator.natAbs ^ 2 : ℕ) : ℤ) = denominator * denominator := by
    simp [pow_two]
  refine ⟨denominator.natAbs ^ 2,
    pow_ne_zero _ (Int.natAbs_ne_zero.mpr nonzero),
    integral * (denominator : IntegralAdeles), ?_⟩
  rw [map_mul, map_intCast, equality, mul_assoc]
  congr 1
  simpa only [Int.cast_mul, Int.cast_natCast] using
    congrArg (Int.cast : ℤ → FiniteAdeles) square.symm

theorem rational_translate_integral (value : FiniteAdeles) :
    ∃ rational : ℚ, value - algebraMap ℚ FiniteAdeles rational ∈
      Set.range integralEmbedding := by
  obtain ⟨denominator, nonzero, integral, equality⟩ := common_natural_denominator value
  obtain ⟨remainder, quotient, residueEquality⟩ := integral_residue denominator nonzero integral
  have cancellation : (denominator : FiniteAdeles) *
      algebraMap ℚ FiniteAdeles (denominator : ℚ)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ FiniteAdeles), ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr nonzero), map_one]
  have scaled : value * (denominator : FiniteAdeles) =
      (remainder : FiniteAdeles) + (denominator : FiniteAdeles) *
        integralEmbedding quotient := by
    rw [← equality, residueEquality, map_add, map_mul, map_natCast, map_natCast]
  refine ⟨(remainder : ℚ) / denominator, quotient, ?_⟩
  have evaluated := congrArg (fun v : FiniteAdeles =>
    v * algebraMap ℚ FiniteAdeles (denominator : ℚ)⁻¹) scaled
  rw [mul_assoc, cancellation, mul_one, add_mul, mul_assoc,
    mul_left_comm (denominator : FiniteAdeles), cancellation, mul_one] at evaluated
  rw [div_eq_mul_inv, map_mul, map_natCast, evaluated]
  ring

theorem rational_integral_iff (rational : ℚ) :
    algebraMap ℚ FiniteAdeles rational ∈ Set.range integralEmbedding ↔
      ∃ integer : ℤ, rational = integer := by
  constructor
  · rintro ⟨integral, equality⟩
    have denominatorEquality : integral * (rational.den : IntegralAdeles) =
        (rational.num : IntegralAdeles) := by
      apply integralEmbedding_injective
      rw [map_mul, map_natCast, map_intCast, equality,
        ← map_natCast (algebraMap ℚ FiniteAdeles), ← map_mul,
        rational.mul_den_eq_num, map_intCast]
    have denominatorOne : rational.den = 1 := by
      by_contra notOne
      obtain ⟨prime, isPrime, divides⟩ := Nat.exists_prime_and_dvd notOne
      have zeroDenominator : (rational.den : ZMod prime) = 0 := by
        obtain ⟨factor, factorEquality⟩ := divides
        rw [factorEquality, Nat.cast_mul]
        simp
      have residueEquality := congrArg (PrimeLattice.residue prime isPrime)
        denominatorEquality
      rw [map_mul, map_natCast, map_intCast, zeroDenominator, mul_zero] at residueEquality
      have numeratorDivides : prime ∣ rational.num.natAbs :=
        Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp residueEquality.symm)
      have dividesOne : prime ∣ 1 := by
        rw [← rational.reduced]
        exact Nat.dvd_gcd numeratorDivides divides
      exact isPrime.not_dvd_one dividesOne
    exact ⟨rational.num, (Rat.coe_int_num_of_den_eq_one denominatorOne).symm⟩
  · rintro ⟨integer, rfl⟩
    refine ⟨integer, ?_⟩
    rw [map_intCast, map_intCast]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.FiniteApproximation
