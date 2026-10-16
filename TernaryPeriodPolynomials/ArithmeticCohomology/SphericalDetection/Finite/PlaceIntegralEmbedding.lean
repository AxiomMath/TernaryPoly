module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaceMatrixEmbedding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance finiteIntegralPlaceDecidableEq : DecidableEq FinitePlace := Classical.decEq _

theorem finiteAtPlaceScalar_integral (place : FinitePlace) (integer : place.adicCompletionIntegers ℚ) :
    finiteAtPlaceScalar place integer.val ∈ Set.range integralEmbedding := by
  refine ⟨Pi.single place integer, ?_⟩
  apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
  intro other
  change ((Pi.single place integer : IntegralAdeles) other).val = finiteEvaluation other (finiteAtPlaceScalar place integer.val)
  by_cases same : other = place
  · subst other
    rw [Pi.single_eq_same, finiteAtPlaceScalar_same]
  · rw [Pi.single_eq_of_ne same, finiteAtPlaceScalar_away _ _ other same]
    rfl

theorem finiteAtPlaceMatrix_integral (dimension : ℕ) (place : FinitePlace)
    (matrix : Matrix (Fin dimension) (Fin dimension) (place.adicCompletionIntegers ℚ))
    (row column : Fin dimension) :
    (finiteAtPlaceMatrix dimension place ((place.adicCompletionIntegers ℚ).toSubring.subtype.mapMatrix matrix))
      row column ∈ Set.range integralEmbedding := by
  change (1 : Matrix (Fin dimension) (Fin dimension) FiniteAdeles) row column +
      finiteAtPlaceScalar place ((matrix row column).val -
        (1 : Matrix (Fin dimension) (Fin dimension) (place.adicCompletion ℚ)) row column) ∈ integralEmbedding.range
  apply integralEmbedding.range.add_mem
  · refine ⟨(1 : Matrix (Fin dimension) (Fin dimension) IntegralAdeles) row column, ?_⟩
    by_cases same : row = column <;> simp [Matrix.one_apply, same]
  · have difference : (matrix row column).val -
        (1 : Matrix (Fin dimension) (Fin dimension) (place.adicCompletion ℚ)) row column =
      (matrix row column - (1 : Matrix (Fin dimension) (Fin dimension) (place.adicCompletionIntegers ℚ)) row column).val := by
      by_cases same : row = column <;> simp [Matrix.one_apply, same]
    rw [difference]
    exact finiteAtPlaceScalar_integral place _

theorem finiteAtPlaceGL_integral (dimension : ℕ) (place : FinitePlace)
    (matrix : GeneralLinearGroup (Fin dimension) (place.adicCompletionIntegers ℚ)) :
    finiteAtPlaceGL dimension place (GeneralLinearGroup.map (place.adicCompletionIntegers ℚ).toSubring.subtype matrix) ∈
      finiteIntegralGLLevel dimension := by
  apply (finiteIntegralGLLevel_mem_iff _).mpr
  constructor
  · exact finiteAtPlaceMatrix_integral dimension place matrix.val
  · rw [← map_inv, ← map_inv]
    exact finiteAtPlaceMatrix_integral dimension place matrix⁻¹.val

theorem finiteGeneralLinearGroup_ext {dimension : ℕ}
    (first second : GeneralLinearGroup (Fin dimension) FiniteAdeles)
    (equal : ∀ place, GeneralLinearGroup.map (finiteEvaluation place) first =
      GeneralLinearGroup.map (finiteEvaluation place) second) : first = second := by
  apply Units.ext
  apply finiteMatrix_ext
  intro place
  exact congrArg Units.val (equal place)

theorem finiteAtPlaceGL_commute {dimension : ℕ} (first second : FinitePlace) (distinct : first ≠ second)
    (left : GeneralLinearGroup (Fin dimension) (first.adicCompletion ℚ))
    (right : GeneralLinearGroup (Fin dimension) (second.adicCompletion ℚ)) :
    Commute (finiteAtPlaceGL dimension first left) (finiteAtPlaceGL dimension second right) := by
  apply finiteGeneralLinearGroup_ext
  intro place
  rw [map_mul, map_mul]
  by_cases away_first : place ≠ first
  · rw [finiteAtPlaceGL_away _ _ _ place away_first, one_mul, mul_one]
  · have away_second : place ≠ second := by
      intro same
      exact distinct ((not_ne_iff.mp away_first).symm.trans same)
    rw [finiteAtPlaceGL_away _ _ _ place away_second, one_mul, mul_one]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
