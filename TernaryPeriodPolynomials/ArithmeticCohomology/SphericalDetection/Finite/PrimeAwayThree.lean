module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.ClassicalEulerFactor

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem finitePlace_ne_three_iff_prime_coprime (place : FinitePlace) :
    place ≠ placeThree ↔ (Rat.HeightOneSpectrum.primesEquiv place).val.Coprime 3 := by
  rw [Nat.coprime_primes (Rat.HeightOneSpectrum.primesEquiv place).property (by decide)]
  have equality : (Rat.HeightOneSpectrum.primesEquiv place).val = 3 ↔ place = placeThree := by
    constructor
    · intro same
      apply (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).injective
      change Rat.HeightOneSpectrum.primesEquiv place = Rat.HeightOneSpectrum.primesEquiv
        ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm primeThree)
      rw [Equiv.apply_symm_apply]
      exact Subtype.ext same
    · intro same
      subst place
      exact congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).apply_symm_apply primeThree)
  exact not_congr equality.symm

def finitePlaceAwayThreeEquivPrime : {place : FinitePlace // place ≠ placeThree} ≃
    {prime : Nat.Primes // prime.val.Coprime 3} :=
  (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).subtypeEquiv finitePlace_ne_three_iff_prime_coprime

theorem finitePlaceAwayThreeEquivPrime_val (place : {place : FinitePlace // place ≠ placeThree}) :
    (finitePlaceAwayThreeEquivPrime place).val = Rat.HeightOneSpectrum.primesEquiv place.val := rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
