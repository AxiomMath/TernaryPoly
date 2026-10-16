module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SphericalHecke

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance heckeLocalizationFinitePlaceDecidableEq : DecidableEq FinitePlace := Classical.decEq _

def binaryHeckeOutsideMatrix (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    Matrix (Fin 2) (Fin 2) IntegralAdeles :=
  fun row column place => if place = integralPrimePlace prime then
    (1 : Matrix (Fin 2) (Fin 2) (place.adicCompletionIntegers ℚ)) row column
  else binaryHeckeIntegralMatrix prime index row column place

theorem binaryHeckeOutsideMatrix_eval (prime : Nat.Primes) (index : Option (Fin prime.val))
    (place : FinitePlace) :
    (Pi.evalRingHom _ place).mapMatrix (binaryHeckeOutsideMatrix prime index) =
      if place = integralPrimePlace prime then 1 else
        (Pi.evalRingHom _ place).mapMatrix (binaryHeckeIntegralMatrix prime index) := by
  split_ifs with same
  · ext row column
    simp [binaryHeckeOutsideMatrix, same]
  · ext row column
    simp [binaryHeckeOutsideMatrix, same]

theorem binaryHeckeOutsideMatrix_isUnit (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    IsUnit (binaryHeckeOutsideMatrix prime index) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply Pi.isUnit_iff.mpr
  intro place
  have determinant : (binaryHeckeOutsideMatrix prime index).det place =
      if place = integralPrimePlace prime then 1 else (prime.val : place.adicCompletionIntegers ℚ) := by
    change (Pi.evalRingHom _ place) (binaryHeckeOutsideMatrix prime index).det = _
    rw [RingHom.map_det, binaryHeckeOutsideMatrix_eval]
    split_ifs
    · exact Matrix.det_one
    · rw [← RingHom.map_det, binaryHeckeIntegralMatrix_det, map_natCast]
  rw [determinant]
  split_ifs with same
  · exact isUnit_one
  · exact integralPrime_natCast_isUnit_of_ne prime place same

def binaryHeckeOutsideCompact (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    GeneralLinearGroup (Fin 2) IntegralAdeles := (binaryHeckeOutsideMatrix_isUnit prime index).unit

theorem binaryHeckeOutsideCompact_val (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    (binaryHeckeOutsideCompact prime index).val = binaryHeckeOutsideMatrix prime index :=
  (binaryHeckeOutsideMatrix_isUnit prime index).unit_spec

def binaryHeckeLocalized (prime : Nat.Primes) (index : Option (Fin prime.val)) : BinaryFiniteGL :=
  (GeneralLinearGroup.map integralEmbedding (binaryHeckeOutsideCompact prime index))⁻¹ *
    GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (binaryHeckeRepresentative prime index)

theorem binaryHeckeOutsideCompact_away (prime : Nat.Primes) (index : Option (Fin prime.val))
    (place : FinitePlace) (away : place ≠ integralPrimePlace prime) :
    GeneralLinearGroup.map (finiteEvaluation place)
        (GeneralLinearGroup.map integralEmbedding (binaryHeckeOutsideCompact prime index)) =
      GeneralLinearGroup.map (finiteEvaluation place)
        (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (binaryHeckeRepresentative prime index)) := by
  apply Units.ext
  funext row column
  rw [GeneralLinearGroup.map_apply, GeneralLinearGroup.map_apply, GeneralLinearGroup.map_apply,
    binaryHeckeOutsideCompact_val, ← binaryHeckeIntegralMatrix_map]
  change (binaryHeckeOutsideMatrix prime index row column place).val =
    (binaryHeckeIntegralMatrix prime index row column place).val
  rw [binaryHeckeOutsideMatrix, ite_eq_right away]

theorem binaryHeckeLocalized_away (prime : Nat.Primes) (index : Option (Fin prime.val))
    (place : FinitePlace) (away : place ≠ integralPrimePlace prime) :
    GeneralLinearGroup.map (finiteEvaluation place) (binaryHeckeLocalized prime index) = 1 := by
  rw [binaryHeckeLocalized, map_mul, map_inv, binaryHeckeOutsideCompact_away prime index place away,
    inv_mul_cancel]

theorem binaryFiniteGL_ext (first second : BinaryFiniteGL)
    (equal : ∀ place : FinitePlace,
      GeneralLinearGroup.map (finiteEvaluation place) first = GeneralLinearGroup.map (finiteEvaluation place) second) :
    first = second := by
  apply Units.ext
  funext row column
  apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
  intro place
  exact congrArg (fun matrix : GeneralLinearGroup (Fin 2) (place.adicCompletion ℚ) => matrix.val row column)
    (equal place)

theorem binaryHeckeLocalized_commute (first second : Nat.Primes) (distinct : first ≠ second)
    (first_index : Option (Fin first.val)) (second_index : Option (Fin second.val)) :
    Commute (binaryHeckeLocalized first first_index) (binaryHeckeLocalized second second_index) := by
  apply binaryFiniteGL_ext
  intro place
  rw [map_mul, map_mul]
  by_cases away_first : place ≠ integralPrimePlace first
  · rw [binaryHeckeLocalized_away first first_index place away_first, one_mul, mul_one]
  · have away_second : place ≠ integralPrimePlace second := by
      intro same_second
      apply distinct
      apply (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.injective
      exact (not_ne_iff.mp away_first).symm.trans same_second
    rw [binaryHeckeLocalized_away second second_index place away_second, one_mul, mul_one]

theorem cuspHeckeLocalized_eq (cusp : CuspidalRepresentation) (prime : Nat.Primes)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) (index : Option (Fin prime.val)) :
    cusp.π (atFinite (binaryHeckeLocalized prime index)⁻¹) vector.val =
      (cuspFiniteRationalSlash cusp (binaryHeckeRepresentative prime index) vector).val := by
  rw [binaryHeckeLocalized, _root_.mul_inv_rev, inv_inv, atFinite_mul, map_mul, Module.End.mul_apply,
    spherical (binaryHeckeOutsideCompact prime index)]
  change _ = cusp.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
    (binaryHeckeRepresentative prime index)⁻¹)) vector.val
  rw [map_inv]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
