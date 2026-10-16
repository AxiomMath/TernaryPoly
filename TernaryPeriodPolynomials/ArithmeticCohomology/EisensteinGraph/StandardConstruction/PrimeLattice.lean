module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ContinuationUniqueness
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.GroupTheory.Index
public import Mathlib.MeasureTheory.Group.FundamentalDomain

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic IsDedekindDomain

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PrimeLattice

def primePlace (prime : ℕ) (isPrime : prime.Prime) : FinitePlace :=
  Rat.HeightOneSpectrum.primesEquiv.symm ⟨prime, isPrime⟩

theorem primePlace_generator (prime : ℕ) (isPrime : prime.Prime) :
    (Rat.HeightOneSpectrum.primesEquiv (primePlace prime isPrime)).val = prime := by
  exact congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply
    ⟨prime, isPrime⟩)

def padicIntegerEquiv (place : FinitePlace)
    [Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime] :
    place.adicCompletionIntegers ℚ ≃+* ℤ_[(Rat.HeightOneSpectrum.primesEquiv place).val] := by
  letI : Algebra ℤ (place.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv place).toRingEquiv

def residue (prime : ℕ) (isPrime : prime.Prime) : IntegralAdeles →+* ZMod prime := by
  let place := primePlace prime isPrime
  let generator := (Rat.HeightOneSpectrum.primesEquiv place).val
  letI : Fact generator.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  exact (ZMod.ringEquivCongr (primePlace_generator prime isPrime)).toRingHom.comp
    (PadicInt.toZMod.comp ((padicIntegerEquiv place).toRingHom.comp
      (Pi.evalRingHom _ place)))

theorem residue_surjective (prime : ℕ) (isPrime : prime.Prime) :
    Function.Surjective (residue prime isPrime) := by
  let : NeZero prime := ⟨isPrime.ne_zero⟩
  intro value
  refine ⟨value.val, ?_⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem prime_isUnit_at_other_place (prime : ℕ) (isPrime : prime.Prime)
    (place : FinitePlace) (different : place ≠ primePlace prime isPrime) :
    IsUnit (prime : place.adicCompletionIntegers ℚ) := by
  let generator := (Rat.HeightOneSpectrum.primesEquiv place).val
  let : Fact generator.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have generatorDifferent : generator ≠ prime := by
    intro equality
    apply different
    apply Rat.HeightOneSpectrum.primesEquiv.injective
    apply Subtype.ext
    exact equality.trans (primePlace_generator prime isPrime).symm
  have padicUnit : IsUnit (prime : ℤ_[generator]) := by
    apply PadicInt.isUnit_iff.mpr
    apply PadicInt.norm_natCast_eq_one_iff.mpr
    exact (Nat.coprime_primes (Rat.HeightOneSpectrum.primesEquiv place).property
      isPrime).mpr generatorDifferent
  simpa only [map_natCast] using padicUnit.map
    (padicIntegerEquiv place).symm.toRingHom

theorem residue_zero_iff (prime : ℕ) (isPrime : prime.Prime) (value : IntegralAdeles) :
    residue prime isPrime value = 0 ↔ ∃ quotient : IntegralAdeles,
      (prime : IntegralAdeles) * quotient = value := by
  classical
  let place := primePlace prime isPrime
  let generator := (Rat.HeightOneSpectrum.primesEquiv place).val
  let : Fact generator.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  let padicEquiv := padicIntegerEquiv place
  constructor
  · intro vanishes
    have padicVanishes : PadicInt.toZMod (padicEquiv (value place)) = 0 := by
      apply (ZMod.ringEquivCongr (primePlace_generator prime isPrime)).injective
      exact vanishes.trans (map_zero _).symm
    have divisible : (generator : ℤ_[generator]) ∣ padicEquiv (value place) := by
      apply Ideal.mem_span_singleton.mp
      rw [← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod]
      exact padicVanishes
    obtain ⟨padicQuotient, padicEquality⟩ := divisible
    let quotient : IntegralAdeles := fun other => if equality : other = place then
      equality.symm ▸ padicEquiv.symm padicQuotient
      else ((prime_isUnit_at_other_place prime isPrime other equality).unit.inv * value other)
    refine ⟨quotient, ?_⟩
    funext other
    by_cases equality : other = place
    · subst other
      change (prime : place.adicCompletionIntegers ℚ) * quotient place = value place
      simp only [quotient, dite_eq_left rfl]
      apply padicEquiv.injective
      rw [map_mul, map_natCast, padicEquiv.apply_symm_apply]
      rw [← primePlace_generator prime isPrime]
      exact padicEquality.symm
    · change (prime : other.adicCompletionIntegers ℚ) * quotient other = value other
      simp only [quotient, dite_eq_right equality]
      have cancellation : (prime : other.adicCompletionIntegers ℚ) *
          (prime_isUnit_at_other_place prime isPrime other equality).unit.inv = 1 := by
        calc
          _ = (prime_isUnit_at_other_place prime isPrime other equality).unit.val *
              (prime_isUnit_at_other_place prime isPrime other equality).unit.inv :=
            congrArg (fun scalar => scalar *
              (prime_isUnit_at_other_place prime isPrime other equality).unit.inv)
              (prime_isUnit_at_other_place prime isPrime other equality).unit_spec.symm
          _ = 1 := (prime_isUnit_at_other_place prime isPrime other equality).unit.val_inv
      rw [← mul_assoc, cancellation, one_mul]
  · rintro ⟨quotient, rfl⟩
    rw [map_mul, map_natCast]
    simp

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PrimeLattice
