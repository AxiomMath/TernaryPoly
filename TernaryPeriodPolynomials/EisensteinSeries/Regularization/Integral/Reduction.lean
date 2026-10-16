module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Adelic.Norm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

instance prime_val_fact (prime : Nat.Primes) : Fact prime.val.Prime := ⟨prime.property⟩

noncomputable def primeIntegralEquiv (prime : Nat.Primes) :
    ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm prime).adicCompletionIntegers ℚ ≃+* ℤ_[prime.val] :=
  (@AlgEquiv.toRingEquiv _ _ _ _ _ _ _ (Ring.toIntAlgebra _)
    (@ContinuousAlgEquiv.toAlgEquiv _ _ _ _ _ _ _ _ _ (Ring.toIntAlgebra _)
      (PadicInt.adicCompletionIntegersEquiv ℤ prime))).symm

noncomputable def primeIntegralReduction (prime : Nat.Primes) :
    IntegralAdeles →+* ZMod prime.val :=
  PadicInt.toZMod.comp ((primeIntegralEquiv prime).toRingHom.comp
    (Pi.evalRingHom _ ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm prime)))

theorem primeIntegralReduction_natCast (prime : Nat.Primes) (value : ℕ) :
    primeIntegralReduction prime (value : IntegralAdeles) = (value : ZMod prime.val) :=
  map_natCast _ _

theorem padicInt_other_prime_isUnit (prime otherPrime : Nat.Primes)
    (different : prime ≠ otherPrime) : IsUnit (prime.val : ℤ_[otherPrime.val]) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro in_maximal
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast] at in_maximal
  have divides := (ZMod.natCast_eq_zero_iff prime.val otherPrime.val).mp in_maximal
  have primes_equal := (Nat.prime_dvd_prime_iff_eq otherPrime.property prime.property).mp divides
  exact different (Subtype.ext primes_equal.symm)

theorem primeIntegralReduction_eq_zero_iff (prime : Nat.Primes) (value : IntegralAdeles) :
    primeIntegralReduction prime value = 0 ↔ (prime.val : IntegralAdeles) ∣ value := by
  constructor
  · intro reduction_zero
    have local_divisibility (otherPrime : Nat.Primes) :
        (prime.val : ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm otherPrime).adicCompletionIntegers ℚ) ∣
          value ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm otherPrime) := by
      by_cases same_prime : prime = otherPrime
      · subst otherPrime
        have local_zero : PadicInt.toZMod
            (primeIntegralEquiv prime (value ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm prime))) = 0 :=
          reduction_zero
        have local_divides := (RingHom.mem_ker).mpr local_zero
        rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
          Ideal.mem_span_singleton] at local_divides
        obtain ⟨quotient, quotient_spec⟩ := local_divides
        refine ⟨(primeIntegralEquiv prime).symm quotient, ?_⟩
        apply (primeIntegralEquiv prime).injective
        simpa only [map_mul, map_natCast, RingEquiv.apply_symm_apply] using quotient_spec
      · obtain ⟨unit, unit_spec⟩ := padicInt_other_prime_isUnit prime otherPrime same_prime
        refine ⟨(primeIntegralEquiv otherPrime).symm
          (unit⁻¹ * primeIntegralEquiv otherPrime
            (value ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm otherPrime))), ?_⟩
        apply (primeIntegralEquiv otherPrime).injective
        simp only [map_mul, map_natCast, RingEquiv.apply_symm_apply, ← unit_spec]
        simp
    have all_places (place : FinitePlace) :
        (prime.val : place.adicCompletionIntegers ℚ) ∣ value place := by
      obtain ⟨otherPrime, rfl⟩ :=
        (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.surjective place
      exact local_divisibility otherPrime
    choose quotients quotients_spec using all_places
    refine ⟨quotients, ?_⟩
    funext place
    exact quotients_spec place
  · rintro ⟨quotient, rfl⟩
    simp only [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem primeIntegralReduction_surjective (prime : Nat.Primes) :
    Function.Surjective (primeIntegralReduction prime) := by
  intro residue
  refine ⟨(residue.val : IntegralAdeles), ?_⟩
  rw [primeIntegralReduction_natCast, ZMod.natCast_zmod_val]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
