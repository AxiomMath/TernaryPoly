module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineSourceLocalSeries
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Commutativity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryHeckeOutsideCompact_same (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    GeneralLinearGroup.map (finiteEvaluation (integralPrimePlace prime))
      (GeneralLinearGroup.map integralEmbedding (binaryHeckeOutsideCompact prime index)) = 1 := by
  apply Units.ext
  funext row column
  rw [GeneralLinearGroup.map_apply, GeneralLinearGroup.map_apply, binaryHeckeOutsideCompact_val]
  change (binaryHeckeOutsideMatrix prime index row column (integralPrimePlace prime)).val =
    (1 : Matrix (Fin 2) (Fin 2) ((integralPrimePlace prime).adicCompletion ℚ)) row column
  simp only [binaryHeckeOutsideMatrix, Matrix.one_apply]
  split_ifs <;> rfl

theorem binaryHeckeLocalized_same (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    GeneralLinearGroup.map (finiteEvaluation (integralPrimePlace prime)) (binaryHeckeLocalized prime index) =
      GeneralLinearGroup.map (finiteEvaluation (integralPrimePlace prime))
        (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (binaryHeckeRepresentative prime index)) := by
  rw [binaryHeckeLocalized, map_mul, map_inv, binaryHeckeOutsideCompact_same, inv_one, one_mul]

theorem binaryHeckeLocalized_eq_finiteAtPlaceGL (prime : Nat.Primes) (index : Option (Fin prime.val)) :
    binaryHeckeLocalized prime index = finiteAtPlaceGL 2 (integralPrimePlace prime)
      (GeneralLinearGroup.map (finiteEvaluation (integralPrimePlace prime))
        (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (binaryHeckeRepresentative prime index))) := by
  apply finiteGeneralLinearGroup_ext
  intro other
  by_cases same : other = integralPrimePlace prime
  · subst other
    rw [binaryHeckeLocalized_same, finiteAtPlaceGL_same]
  · rw [binaryHeckeLocalized_away _ _ _ same, finiteAtPlaceGL_away _ _ _ _ same]

theorem finiteAtPadicGL_map_completion (dimension : ℕ) (place : FinitePlace)
    (matrix : GeneralLinearGroup (Fin dimension) (place.adicCompletion ℚ)) :
    finiteAtPadicGL dimension place (GeneralLinearGroup.map (finiteCompletionPadicEquiv place).toRingHom matrix) =
      finiteAtPlaceGL dimension place matrix := by
  have equality : GeneralLinearGroup.map (finiteCompletionPadicEquiv place).symm.toRingHom
      (GeneralLinearGroup.map (finiteCompletionPadicEquiv place).toRingHom matrix) = matrix := by
    apply Units.ext
    funext row column
    exact (finiteCompletionPadicEquiv place).symm_apply_apply _
  exact congrArg (finiteAtPlaceGL dimension place) equality

theorem binaryHeckeLocalized_eq_finiteAtPadicGL (place : FinitePlace)
    (index : Option (Fin (Rat.HeightOneSpectrum.primesEquiv place).val)) :
    binaryHeckeLocalized (Rat.HeightOneSpectrum.primesEquiv place) index =
      finiteAtPadicGL 2 place (GeneralLinearGroup.map (finitePadicEvaluation place)
        (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
          (binaryHeckeRepresentative (Rat.HeightOneSpectrum.primesEquiv place) index))) := by
  have same : integralPrimePlace (Rat.HeightOneSpectrum.primesEquiv place) = place :=
    (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm_apply_apply place
  rw [binaryHeckeLocalized_eq_finiteAtPlaceGL, same]
  exact (finiteAtPadicGL_map_completion 2 place _).symm

theorem finitePadicGL_map_rational (dimension : ℕ) (place : FinitePlace)
    (matrix : GeneralLinearGroup (Fin dimension) ℚ) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    GeneralLinearGroup.map (finitePadicEvaluation place) (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) matrix) =
      GeneralLinearGroup.map (algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) matrix := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  apply Units.ext
  funext row column
  have equality : (finitePadicEvaluation place).comp (algebraMap ℚ FiniteAdeles) =
      algebraMap ℚ ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] := Subsingleton.elim _ _
  exact congrArg (fun hom : ℚ →+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] => hom (matrix.val row column)) equality

def padicHeckeRepresentative {prime : ℕ} [Fact prime.Prime] (index : Option (Fin prime)) :
    GeneralLinearGroup (Fin 2) ℚ_[prime] :=
  GeneralLinearGroup.map (algebraMap ℚ ℚ_[prime]) (binaryHeckeRepresentative ⟨prime, Fact.out⟩ index)

theorem binaryHeckeLocalized_eq_padicRepresentative (place : FinitePlace)
    (index : Option (Fin (Rat.HeightOneSpectrum.primesEquiv place).val)) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    binaryHeckeLocalized (Rat.HeightOneSpectrum.primesEquiv place) index =
      finiteAtPadicGL 2 place (padicHeckeRepresentative index) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  rw [binaryHeckeLocalized_eq_finiteAtPadicGL, finitePadicGL_map_rational]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
