module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.IntegralLevel
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarHecke

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem atFinite_mul {dimension : ℕ}
    (first second : GeneralLinearGroup (Fin dimension) FiniteAdeles) :
    atFinite (first * second) = atFinite first * atFinite second := by
  apply Units.ext
  funext row column
  apply Prod.ext
  · simp only [atFinite, combineGL, pairMatrix, GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Prod.fst_sum, Prod.fst_mul, GeneralLinearGroup.coe_one]
    simp only [← Matrix.mul_apply, one_mul]
  · simp [atFinite, combineGL, pairMatrix, Matrix.mul_apply, Prod.snd_sum]

theorem atFinite_one {dimension : ℕ} :
    atFinite (1 : GeneralLinearGroup (Fin dimension) FiniteAdeles) = 1 := by
  apply Units.ext
  funext row column
  by_cases equal : row = column <;> simp [atFinite, combineGL, pairMatrix, equal]

def atFiniteMonoidHom (dimension : ℕ) :
    GeneralLinearGroup (Fin dimension) FiniteAdeles →* GeneralLinearGroup (Fin dimension) Adeles where
  toFun := atFinite
  map_one' := atFinite_one
  map_mul' := atFinite_mul

theorem atFinite_inv {dimension : ℕ} (matrix : GeneralLinearGroup (Fin dimension) FiniteAdeles) :
    atFinite matrix⁻¹ = (atFinite matrix)⁻¹ := map_inv (atFiniteMonoidHom dimension) matrix

local instance finitePrimeReductionFact (prime : Nat.Primes) : Fact prime.val.Prime := ⟨prime.property⟩

def integralPrimePlace (prime : Nat.Primes) : FinitePlace :=
  Rat.HeightOneSpectrum.primesEquiv.symm prime

def integralPrimeEquiv (prime : Nat.Primes) :
    (integralPrimePlace prime).adicCompletionIntegers ℚ ≃+* ℤ_[prime.val] :=
  (@AlgEquiv.toRingEquiv _ _ _ _ _ _ _ (Ring.toIntAlgebra _)
    (@ContinuousAlgEquiv.toAlgEquiv _ _ _ _ _ _ _ _ _ (Ring.toIntAlgebra _)
      (PadicInt.adicCompletionIntegersEquiv ℤ prime))).symm

def integralPrimeReduction (prime : Nat.Primes) : IntegralAdeles →+* ZMod prime.val :=
  PadicInt.toZMod.comp ((integralPrimeEquiv prime).toRingHom.comp (Pi.evalRingHom _ (integralPrimePlace prime)))

theorem padicInt_toZMod_zero_iff_dvd (prime : Nat.Primes) (value : ℤ_[prime.val]) :
    PadicInt.toZMod value = 0 ↔ (prime.val : ℤ_[prime.val]) ∣ value := by
  rw [← PadicInt.zmodRepr_eq_zero_iff_dvd, ← PadicInt.val_toZMod_eq_zmodRepr, ZMod.val_eq_zero]

theorem padicInt_prime_isUnit_of_ne (prime other : Nat.Primes) (distinct : prime ≠ other) :
    IsUnit (prime.val : ℤ_[other.val]) := by
  by_contra nonunit
  have small := (PadicInt.not_isUnit_iff).mp nonunit
  have integer_divides : (other.val : ℤ) ∣ (prime.val : ℤ) :=
    (PadicInt.norm_int_lt_one_iff_dvd (prime.val : ℤ)).mp (by simpa using small)
  have divides : other.val ∣ prime.val := by exact_mod_cast integer_divides
  have equal : other.val = prime.val :=
    (prime.property.eq_one_or_self_of_dvd other.val divides).resolve_left other.property.ne_one
  exact distinct (Subtype.ext equal.symm)

theorem integralPrimeReduction_zero_iff_dvd (prime : Nat.Primes) (value : IntegralAdeles) :
    integralPrimeReduction prime value = 0 ↔ (prime.val : IntegralAdeles) ∣ value := by
  constructor
  · intro zero
    have local_divides (place : FinitePlace) : (prime.val : place.adicCompletionIntegers ℚ) ∣ value place := by
      by_cases same : place = integralPrimePlace prime
      · subst place
        have divides : (prime.val : ℤ_[prime.val]) ∣ integralPrimeEquiv prime (value (integralPrimePlace prime)) :=
          (padicInt_toZMod_zero_iff_dvd prime _).mp zero
        obtain ⟨quotient, equality⟩ := divides
        refine ⟨(integralPrimeEquiv prime).symm quotient, ?_⟩
        apply (integralPrimeEquiv prime).injective
        simpa only [map_mul, map_natCast, RingEquiv.apply_symm_apply] using equality
      · let other := Rat.HeightOneSpectrum.primesEquiv place
        have distinct : prime ≠ other := by
          intro equal
          apply same
          change place = Rat.HeightOneSpectrum.primesEquiv.symm prime
          rw [equal]
          exact (Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply place).symm
        let : Algebra ℤ (place.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
        let equivalence : place.adicCompletionIntegers ℚ ≃+* ℤ_[other.val] :=
          (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv place).toAlgEquiv.toRingEquiv
        have divides : (prime.val : ℤ_[other.val]) ∣ equivalence (value place) :=
          (padicInt_prime_isUnit_of_ne prime other distinct).dvd
        obtain ⟨quotient, equality⟩ := divides
        refine ⟨equivalence.symm quotient, ?_⟩
        apply equivalence.injective
        simpa only [map_mul, map_natCast, RingEquiv.apply_symm_apply] using equality
    choose quotient equality using local_divides
    refine ⟨quotient, ?_⟩
    funext place
    exact equality place
  · rintro ⟨quotient, rfl⟩
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem integralPrimeReduction_surjective (prime : Nat.Primes) : Function.Surjective (integralPrimeReduction prime) := by
  intro residue
  refine ⟨(residue.val : IntegralAdeles), ?_⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem integralPrime_natCast_isUnit_of_ne (prime : Nat.Primes) (place : FinitePlace)
    (distinct : place ≠ integralPrimePlace prime) :
    IsUnit (prime.val : place.adicCompletionIntegers ℚ) := by
  let other := Rat.HeightOneSpectrum.primesEquiv place
  have primes_distinct : prime ≠ other := by
    intro equal
    apply distinct
    change place = Rat.HeightOneSpectrum.primesEquiv.symm prime
    rw [equal]
    exact (Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply place).symm
  let : Algebra ℤ (place.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  let equivalence : place.adicCompletionIntegers ℚ ≃+* ℤ_[other.val] :=
    (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv place).toAlgEquiv.toRingEquiv
  simpa only [map_natCast] using (padicInt_prime_isUnit_of_ne prime other primes_distinct).map equivalence.symm

theorem finiteIntegralGLLevel_mem_of_entries_det {dimension : ℕ}
    (matrix : GeneralLinearGroup (Fin dimension) FiniteAdeles)
    (entries : ∀ row column, matrix.val row column ∈ Set.range integralEmbedding)
    (determinant : IntegralAdelesˣ)
    (det_eq : matrix.val.det = integralEmbedding determinant.val) :
    matrix ∈ finiteIntegralGLLevel dimension := by
  choose original_values original_eq using entries
  let original : Matrix (Fin dimension) (Fin dimension) IntegralAdeles := original_values
  have mapped : integralEmbedding.mapMatrix original = matrix.val := by
    funext row column
    exact original_eq row column
  have original_det : Matrix.det original = determinant.val := by
    apply integralEmbedding_injective
    rw [RingHom.map_det, mapped, det_eq]
  have invertible : IsUnit original := (Matrix.isUnit_iff_isUnit_det original).mpr
    (original_det ▸ determinant.isUnit)
  obtain ⟨unit, unit_value⟩ := invertible
  refine ⟨unit, ?_⟩
  apply Units.ext
  change integralEmbedding.mapMatrix unit.val = matrix.val
  rw [unit_value, mapped]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
