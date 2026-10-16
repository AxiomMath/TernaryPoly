module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFinitePadicValues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance finitePlaceEmbeddingDecidableEq : DecidableEq FinitePlace := Classical.decEq _

def finiteAtPlaceScalar (place : FinitePlace) (value : place.adicCompletion ℚ) : FiniteAdeles :=
  RestrictedProduct.single (fun place : FinitePlace => place.adicCompletionIntegers ℚ) place value

theorem finiteAtPlaceScalar_same (place : FinitePlace) (value : place.adicCompletion ℚ) :
    finiteEvaluation place (finiteAtPlaceScalar place value) = value :=
  RestrictedProduct.single_eq_same (fun place : FinitePlace => place.adicCompletionIntegers ℚ) place value

theorem finiteAtPlaceScalar_away (place : FinitePlace) (value : place.adicCompletion ℚ)
    (other : FinitePlace) (away : other ≠ place) :
    finiteEvaluation other (finiteAtPlaceScalar place value) = 0 :=
  RestrictedProduct.single_eq_of_ne (fun place : FinitePlace => place.adicCompletionIntegers ℚ) value away

def finiteAtPlaceMatrix (dimension : ℕ) (place : FinitePlace)
    (matrix : Matrix (Fin dimension) (Fin dimension) (place.adicCompletion ℚ)) :
    Matrix (Fin dimension) (Fin dimension) FiniteAdeles :=
  fun row column => (1 : Matrix (Fin dimension) (Fin dimension) FiniteAdeles) row column +
    finiteAtPlaceScalar place (matrix row column -
      (1 : Matrix (Fin dimension) (Fin dimension) (place.adicCompletion ℚ)) row column)

theorem finiteAtPlaceMatrix_same (dimension : ℕ) (place : FinitePlace)
    (matrix : Matrix (Fin dimension) (Fin dimension) (place.adicCompletion ℚ)) :
    (finiteEvaluation place).mapMatrix (finiteAtPlaceMatrix dimension place matrix) = matrix := by
  funext row column
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, finiteAtPlaceMatrix, map_add,
    finiteAtPlaceScalar_same, Matrix.one_apply]
  split_ifs <;> simp

theorem finiteAtPlaceMatrix_away (dimension : ℕ) (place : FinitePlace)
    (matrix : Matrix (Fin dimension) (Fin dimension) (place.adicCompletion ℚ))
    (other : FinitePlace) (away : other ≠ place) :
    (finiteEvaluation other).mapMatrix (finiteAtPlaceMatrix dimension place matrix) = 1 := by
  funext row column
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, finiteAtPlaceMatrix, map_add,
    finiteAtPlaceScalar_away _ _ other away, add_zero, Matrix.one_apply]
  split_ifs <;> simp

theorem finiteMatrix_ext {dimension : ℕ}
    (first second : Matrix (Fin dimension) (Fin dimension) FiniteAdeles)
    (equal : ∀ place, (finiteEvaluation place).mapMatrix first = (finiteEvaluation place).mapMatrix second) :
    first = second := by
  funext row column
  apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
  intro place
  exact congrArg (fun matrix => matrix row column) (equal place)

def finiteAtPlaceMatrixHom (dimension : ℕ) (place : FinitePlace) :
    Matrix (Fin dimension) (Fin dimension) (place.adicCompletion ℚ) →*
      Matrix (Fin dimension) (Fin dimension) FiniteAdeles where
  toFun := finiteAtPlaceMatrix dimension place
  map_one' := by
    apply finiteMatrix_ext
    intro other
    by_cases same : other = place
    · subst other
      rw [finiteAtPlaceMatrix_same, map_one]
    · rw [finiteAtPlaceMatrix_away _ _ _ other same, map_one]
  map_mul' first second := by
    apply finiteMatrix_ext
    intro other
    by_cases same : other = place
    · subst other
      rw [finiteAtPlaceMatrix_same, map_mul, finiteAtPlaceMatrix_same, finiteAtPlaceMatrix_same]
    · rw [finiteAtPlaceMatrix_away _ _ _ other same, map_mul,
        finiteAtPlaceMatrix_away _ _ _ other same, finiteAtPlaceMatrix_away _ _ _ other same, one_mul]

def finiteAtPlaceGL (dimension : ℕ) (place : FinitePlace) :
    GeneralLinearGroup (Fin dimension) (place.adicCompletion ℚ) →*
      GeneralLinearGroup (Fin dimension) FiniteAdeles :=
  Units.map (finiteAtPlaceMatrixHom dimension place)

theorem finiteAtPlaceGL_same (dimension : ℕ) (place : FinitePlace)
    (matrix : GeneralLinearGroup (Fin dimension) (place.adicCompletion ℚ)) :
    GeneralLinearGroup.map (finiteEvaluation place) (finiteAtPlaceGL dimension place matrix) = matrix :=
  Units.ext (finiteAtPlaceMatrix_same dimension place matrix.val)

theorem finiteAtPlaceGL_away (dimension : ℕ) (place : FinitePlace)
    (matrix : GeneralLinearGroup (Fin dimension) (place.adicCompletion ℚ))
    (other : FinitePlace) (away : other ≠ place) :
    GeneralLinearGroup.map (finiteEvaluation other) (finiteAtPlaceGL dimension place matrix) = 1 :=
  Units.ext (finiteAtPlaceMatrix_away dimension place matrix.val other away)

theorem finiteAtPlaceGL_injective (dimension : ℕ) (place : FinitePlace) :
    Function.Injective (finiteAtPlaceGL dimension place) := by
  intro first second equal
  have evaluated := congrArg (GeneralLinearGroup.map (finiteEvaluation place)) equal
  simpa only [finiteAtPlaceGL_same] using evaluated

end TernaryPeriodPolynomials.SphericalDetection.Helpers
