module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.BadPlaneSupport

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance threePlaceDecidableEq : DecidableEq FinitePlace := Classical.decEq _

def finiteAtThreeScalar (value : ℚ_[3]) : FiniteAdeles :=
  RestrictedProduct.single (fun place : FinitePlace => place.adicCompletionIntegers ℚ)
    placeThree (threeCompletionEquiv.symm value)

theorem finiteAtThreeScalar_three (value : ℚ_[3]) :
    finiteThree (finiteAtThreeScalar value) = value := by
  change threeCompletionEquiv
    ((RestrictedProduct.single (fun place : FinitePlace => place.adicCompletionIntegers ℚ)
      placeThree (threeCompletionEquiv.symm value)) placeThree) = value
  rw [RestrictedProduct.single_eq_same, ContinuousAlgEquiv.apply_symm_apply]

theorem finiteAtThreeScalar_away (value : ℚ_[3]) (place : FinitePlace) (away : place ≠ placeThree) :
    finiteEvaluation place (finiteAtThreeScalar value) = 0 :=
  RestrictedProduct.single_eq_of_ne
    (fun place : FinitePlace => place.adicCompletionIntegers ℚ) _ away

theorem finiteAdeles_eq_of_three_and_away (first second : FiniteAdeles)
    (three : finiteThree first = finiteThree second)
    (away : ∀ place, place ≠ placeThree → finiteEvaluation place first = finiteEvaluation place second) :
    first = second := by
  apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
  intro place
  by_cases same : place = placeThree
  · subst place
    exact threeCompletionEquiv.injective three
  · exact away place same

theorem ringHom_add_section_sub {source target : Type*} [CommRing source] [CommRing target]
    (hom : source →+* target) (sectionMap : target → source)
    (section_eq : ∀ value, hom (sectionMap value) = value) (base : source) (value : target) :
    hom (base + sectionMap (value - hom base)) = value := by
  rw [map_add, section_eq]
  ring

theorem ringHom_mapMatrix_section {source target : Type*} [CommRing source] [CommRing target]
    (hom : source →+* target) (sectionMap : target → source)
    (section_eq : ∀ value, hom (sectionMap value) = value)
    (matrix : Matrix (Fin 3) (Fin 3) target) :
    hom.mapMatrix (fun row column => (1 : Matrix (Fin 3) (Fin 3) source) row column +
      sectionMap (matrix row column - hom ((1 : Matrix (Fin 3) (Fin 3) source) row column))) = matrix := by
  funext row column
  exact ringHom_add_section_sub hom sectionMap section_eq _ _

def finiteAtThreeMatrix (matrix : Matrix (Fin 3) (Fin 3) ℚ_[3]) : Matrix (Fin 3) (Fin 3) FiniteAdeles :=
  fun row column => (1 : Matrix (Fin 3) (Fin 3) FiniteAdeles) row column +
    finiteAtThreeScalar (matrix row column - finiteThree ((1 : Matrix (Fin 3) (Fin 3) FiniteAdeles) row column))

theorem finiteAtThreeMatrix_three (matrix : Matrix (Fin 3) (Fin 3) ℚ_[3]) :
    finiteThree.mapMatrix (finiteAtThreeMatrix matrix) = matrix :=
  ringHom_mapMatrix_section finiteThree finiteAtThreeScalar finiteAtThreeScalar_three matrix

theorem finiteAtThreeMatrix_away (matrix : Matrix (Fin 3) (Fin 3) ℚ_[3])
    (place : FinitePlace) (away : place ≠ placeThree) :
    (finiteEvaluation place).mapMatrix (finiteAtThreeMatrix matrix) = 1 := by
  funext row column
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, finiteAtThreeMatrix, map_add,
    finiteAtThreeScalar_away _ place away, add_zero, Matrix.one_apply]
  split_ifs <;> simp

theorem ringHom_mapMatrix_entry_congr {source target : Type*} [CommRing source] [CommRing target]
    (hom : source →+* target) (first second : Matrix (Fin 3) (Fin 3) source)
    (equal : hom.mapMatrix first = hom.mapMatrix second) (row column : Fin 3) :
    hom (first row column) = hom (second row column) :=
  congrArg (fun matrix => matrix row column) equal

theorem finiteMatrix_eq_of_three_and_away (first second : Matrix (Fin 3) (Fin 3) FiniteAdeles)
    (three : finiteThree.mapMatrix first = finiteThree.mapMatrix second)
    (away : ∀ place, place ≠ placeThree →
      (finiteEvaluation place).mapMatrix first = (finiteEvaluation place).mapMatrix second) :
    first = second := by
  funext row column
  apply finiteAdeles_eq_of_three_and_away
  · exact ringHom_mapMatrix_entry_congr finiteThree first second three row column
  · intro place distinct
    exact ringHom_mapMatrix_entry_congr (finiteEvaluation place) first second (away place distinct) row column

def finiteAtThreeMatrixHom : Matrix (Fin 3) (Fin 3) ℚ_[3] →* Matrix (Fin 3) (Fin 3) FiniteAdeles where
  toFun := finiteAtThreeMatrix
  map_one' := by
    apply finiteMatrix_eq_of_three_and_away
    · rw [finiteAtThreeMatrix_three, map_one]
    · intro place away
      rw [finiteAtThreeMatrix_away _ place away, map_one]
  map_mul' first second := by
    apply finiteMatrix_eq_of_three_and_away
    · rw [finiteAtThreeMatrix_three, map_mul, finiteAtThreeMatrix_three, finiteAtThreeMatrix_three]
    · intro place away
      rw [finiteAtThreeMatrix_away _ place away, map_mul,
        finiteAtThreeMatrix_away _ place away, finiteAtThreeMatrix_away _ place away, one_mul]

def finiteAtThree : LocalThreeGL →* FiniteGL := Units.map finiteAtThreeMatrixHom

def atThree : LocalThreeGL →* AdelicGL := (atFiniteMonoidHom 3).comp finiteAtThree

theorem finiteAtThree_three (matrix : LocalThreeGL) :
    GeneralLinearGroup.map finiteThree (finiteAtThree matrix) = matrix := by
  apply Units.ext
  exact finiteAtThreeMatrix_three matrix.val

theorem finiteAtThree_away (matrix : LocalThreeGL) (place : FinitePlace) (away : place ≠ placeThree) :
    GeneralLinearGroup.map (finiteEvaluation place) (finiteAtThree matrix) = 1 := by
  apply Units.ext
  exact finiteAtThreeMatrix_away matrix.val place away

theorem atThree_three (matrix : LocalThreeGL) : adelicThreeGroup (atThree matrix) = matrix := by
  change adelicThreeGroup (atFinite (finiteAtThree matrix)) = matrix
  rw [adelicThreeGroup_atFinite, finiteAtThree_three]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
