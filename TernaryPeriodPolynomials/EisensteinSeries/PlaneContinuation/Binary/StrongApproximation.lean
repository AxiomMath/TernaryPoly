module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.FiniteTriangular

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteIdeleReduction

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryStrongApproximation

def diagonal {ring : Type*} [CommRing ring] (first second : ringˣ) : GeneralLinearGroup (Fin 2) ring :=
  ⟨!![first.val, 0; 0, second.val], !![first.inv, 0; 0, second.inv], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem diagonal_mul {ring : Type*} [CommRing ring] (first second third fourth : ringˣ) :
    diagonal (first * third) (second * fourth) = diagonal first second * diagonal third fourth := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [diagonal, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagonal_map {source target : Type*} [CommRing source] [CommRing target]
    (hom : source →+* target) (first second : sourceˣ) :
    GeneralLinearGroup.map hom (diagonal first second) =
      diagonal (Units.map hom.toMonoidHom first) (Units.map hom.toMonoidHom second) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [diagonal, GeneralLinearGroup.map_apply]

theorem unipotent_map {source target : Type*} [CommRing source] [CommRing target]
    (hom : source →+* target) (parameter : source) :
    GeneralLinearGroup.map hom (binaryUnipotent parameter) = binaryUnipotent (hom parameter) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [binaryUnipotent, GeneralLinearGroup.map_apply]

theorem unipotent_add {ring : Type*} [CommRing ring] (first second : ring) :
    binaryUnipotent (first + second) = binaryUnipotent first * binaryUnipotent second := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem diagonal_unipotent {ring : Type*} [CommRing ring] (first second : ringˣ) (parameter : ring) :
    diagonal first second * binaryUnipotent parameter =
      binaryUnipotent (first.val * parameter * second.inv) * diagonal first second := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [diagonal, binaryUnipotent,
    Matrix.mul_apply, Fin.sum_univ_two, mul_assoc]

theorem triangular_diagonal_units {ring : Type*} [CommRing ring]
    (matrix : GeneralLinearGroup (Fin 2) ring) (triangular : matrix.val 1 0 = 0) :
    ∃ first second : ringˣ, first.val = matrix.val 0 0 ∧ second.val = matrix.val 1 1 := by
  have determinant : IsUnit (matrix.val 0 0 * matrix.val 1 1) := by
    have unit := (GeneralLinearGroup.det matrix).isUnit
    simpa only [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, triangular, mul_zero, sub_zero] using unit
  obtain ⟨⟨first, firstEquality⟩, ⟨second, secondEquality⟩⟩ := IsUnit.mul_iff.mp determinant
  exact ⟨first, second, firstEquality, secondEquality⟩

theorem triangular_factor {ring : Type*} [CommRing ring]
    (matrix : GeneralLinearGroup (Fin 2) ring) (triangular : matrix.val 1 0 = 0)
    (first second : ringˣ) (firstEquality : first.val = matrix.val 0 0)
    (secondEquality : second.val = matrix.val 1 1) :
    matrix = diagonal first second * binaryUnipotent (first.inv * matrix.val 0 1) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [diagonal, binaryUnipotent,
    Matrix.mul_apply, Fin.sum_univ_two, ← firstEquality, ← secondEquality, triangular, ← mul_assoc]

theorem triangular_rational_integral (matrix : BinaryFiniteGL) (triangular : matrix.val 1 0 = 0) :
    ∃ rational : BinaryRationalGL, ∃ integral : IntegralBinaryGL,
      matrix = GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
        GeneralLinearGroup.map integralEmbedding integral := by
  obtain ⟨first, second, firstEquality, secondEquality⟩ := triangular_diagonal_units matrix triangular
  obtain ⟨firstRational, firstIntegral, firstFactor⟩ := exists_rational_mul_integral first
  obtain ⟨secondRational, secondIntegral, secondFactor⟩ := exists_rational_mul_integral second
  let firstImage := Units.map integralEmbedding.toMonoidHom firstIntegral
  let secondImage := Units.map integralEmbedding.toMonoidHom secondIntegral
  let parameter := first.inv * matrix.val 0 1
  obtain ⟨rationalParameter, integralParameter, parameterFactor⟩ :=
    AdelicAdditiveReduction.exists_rational_add_integral (firstImage.val * parameter * secondImage.inv)
  refine ⟨diagonal firstRational secondRational * binaryUnipotent rationalParameter,
    binaryUnipotent integralParameter * diagonal firstIntegral secondIntegral, ?_⟩
  calc
    matrix = diagonal first second * binaryUnipotent parameter :=
      triangular_factor matrix triangular first second firstEquality secondEquality
    _ = diagonal (rationalUnit firstRational) (rationalUnit secondRational) *
        (diagonal firstImage secondImage * binaryUnipotent parameter) := by
      rw [firstFactor, secondFactor, diagonal_mul, mul_assoc]
    _ = diagonal (rationalUnit firstRational) (rationalUnit secondRational) *
        ((binaryUnipotent (algebraMap ℚ FiniteAdeles rationalParameter) *
          binaryUnipotent (integralEmbedding integralParameter)) * diagonal firstImage secondImage) := by
      rw [diagonal_unipotent, parameterFactor, unipotent_add]
    _ = _ := by
      simp only [map_mul, diagonal_map, unipotent_map]
      simp only [rationalUnit, firstImage, secondImage, mul_assoc]

theorem exists_rational_integral (matrix : BinaryFiniteGL) :
    ∃ rational : BinaryRationalGL, ∃ integral : IntegralBinaryGL,
      matrix = GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational *
        GeneralLinearGroup.map integralEmbedding integral := by
  obtain ⟨compactPart, triangular⟩ := BinaryFiniteTriangular.exists_triangular_integral matrix
  obtain ⟨rational, integral, equality⟩ := triangular_rational_integral _ triangular
  refine ⟨rational, integral * compactPart, ?_⟩
  rw [map_mul, ← mul_assoc, ← equality, inv_mul_cancel_right]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryStrongApproximation
