module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.IdeleReduction
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Binary.Level
public import Mathlib.LinearAlgebra.Matrix.Swap

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryFiniteTriangular

def lower {ring : Type*} [CommRing ring] (parameter : ring) : GeneralLinearGroup (Fin 2) ring :=
  ⟨!![1, 0; parameter, 1], !![1, 0; -parameter, 1], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def swap {ring : Type*} [CommRing ring] (first second : Fin 2) : GeneralLinearGroup (Fin 2) ring :=
  ⟨Matrix.swap ring first second, Matrix.swap ring first second,
    Matrix.swap_mul_self first second, Matrix.swap_mul_self first second⟩

theorem lastRow_nonzero {field : Type*} [Field field] (matrix : GeneralLinearGroup (Fin 2) field) :
    (fun column => matrix.val 1 column) ≠ 0 := by
  intro vanishing
  have product := congrArg (fun value : Matrix (Fin 2) (Fin 2) field => value 1 1) matrix.val_inv
  simp only [Matrix.mul_apply, show ∀ column, matrix.val 1 column = 0 from congrFun vanishing,
    zero_mul, Finset.sum_const_zero, Matrix.one_apply_eq] at product
  exact zero_ne_one product

theorem local_lastRow {field : Type*} [Field field]
    {valueGroup : Type*} [LinearOrderedCommGroupWithZero valueGroup]
    (valuation : Valuation field valueGroup) (matrix : GeneralLinearGroup (Fin 2) field) :
    ∃ integral : GeneralLinearGroup (Fin 2) valuation.valuationSubring, ∃ scalar : field,
      scalar ≠ 0 ∧ ∀ column, matrix.val 1 column = scalar *
        (GeneralLinearGroup.map valuation.valuationSubring.subtype integral).val 1 column := by
  classical
  obtain ⟨pivot, _, maximality⟩ := Finset.exists_max_image Finset.univ
    (fun column : Fin 2 => valuation (matrix.val 1 column)) Finset.univ_nonempty
  have pivotNonzero : matrix.val 1 pivot ≠ 0 := by
    intro zeroPivot
    apply lastRow_nonzero matrix
    funext column
    apply valuation.zero_iff.mp
    apply le_antisymm _ zero_le
    simpa only [zeroPivot, map_zero] using maximality column (Finset.mem_univ column)
  let normalized : Fin 2 → valuation.valuationSubring := fun column =>
    ⟨matrix.val 1 (Equiv.swap pivot 1 column) / matrix.val 1 pivot, by
      apply (valuation.mem_valuationSubring_iff _).mpr
      rw [valuation.map_div]
      exact (div_le_one₀ (valuation.pos_iff.mpr pivotNonzero)).mpr
        (maximality _ (Finset.mem_univ _))⟩
  have normalizedLast : normalized 1 = 1 := by
    apply Subtype.ext
    simp [normalized, pivotNonzero]
  have lowerProperty (column : Fin 2) : (lower (normalized 0)).val 1 column = normalized column := by
    fin_cases column <;> simp [lower, normalizedLast]
  let integral := lower (normalized 0) * (swap pivot 1 : GeneralLinearGroup (Fin 2) valuation.valuationSubring)
  have rowProperty (column : Fin 2) : integral.val 1 column = normalized (Equiv.swap pivot 1 column) := by
    change ((fun index => (lower (normalized 0)).val 1 index) ᵥ*
      Matrix.swap valuation.valuationSubring pivot 1) column = _
    rw [Matrix.vecMul_swap]
    exact lowerProperty _
  refine ⟨integral, matrix.val 1 pivot, pivotNonzero, fun column => ?_⟩
  change matrix.val 1 column = matrix.val 1 pivot * (integral.val 1 column).val
  rw [rowProperty]
  simp only [normalized, Equiv.swap_apply_self]
  exact (mul_div_cancel₀ (matrix.val 1 column) pivotNonzero).symm

theorem local_triangular {field : Type*} [Field field]
    {valueGroup : Type*} [LinearOrderedCommGroupWithZero valueGroup]
    (valuation : Valuation field valueGroup) (matrix : GeneralLinearGroup (Fin 2) field) :
    ∃ integral : GeneralLinearGroup (Fin 2) valuation.valuationSubring,
      (matrix * (GeneralLinearGroup.map valuation.valuationSubring.subtype integral)⁻¹).val 1 0 = 0 := by
  obtain ⟨integral, scalar, _, rowProperty⟩ := local_lastRow valuation matrix
  refine ⟨integral, ?_⟩
  let embedded := GeneralLinearGroup.map valuation.valuationSubring.subtype integral
  calc
    (matrix * embedded⁻¹).val 1 0 = scalar * (embedded.val * embedded.inv) 1 0 := by
      simp only [Units.val_mul, Matrix.mul_apply, rowProperty, Finset.mul_sum, mul_assoc]
      rfl
    _ = 0 := by rw [embedded.val_inv]; simp

def assemble (localMatrices : ∀ place : FinitePlace, GeneralLinearGroup (Fin 2) (place.adicCompletionIntegers ℚ)) :
    IntegralBinaryGL where
  val row column place := (localMatrices place).val row column
  inv row column place := (localMatrices place).inv row column
  val_inv := by
    apply Matrix.ext
    intro row column
    funext place
    change (∑ index : Fin 2, (localMatrices place).val row index * (localMatrices place).inv index column) =
      (1 : Matrix (Fin 2) (Fin 2) IntegralAdeles) row column place
    have equality := congrArg (fun matrix => matrix row column) (localMatrices place).val_inv
    simpa only [Matrix.mul_apply, Matrix.one_apply, ite_apply, Pi.one_apply, Pi.zero_apply] using equality
  inv_val := by
    apply Matrix.ext
    intro row column
    funext place
    change (∑ index : Fin 2, (localMatrices place).inv row index * (localMatrices place).val index column) =
      (1 : Matrix (Fin 2) (Fin 2) IntegralAdeles) row column place
    have equality := congrArg (fun matrix => matrix row column) (localMatrices place).inv_val
    simpa only [Matrix.mul_apply, Matrix.one_apply, ite_apply, Pi.one_apply, Pi.zero_apply] using equality

theorem assemble_evaluation
    (localMatrices : ∀ place : FinitePlace, GeneralLinearGroup (Fin 2) (place.adicCompletionIntegers ℚ))
    (place : FinitePlace) :
    GeneralLinearGroup.map (finiteEvaluation place) (GeneralLinearGroup.map integralEmbedding (assemble localMatrices)) =
      GeneralLinearGroup.map (place.adicCompletionIntegers ℚ).subtype (localMatrices place) := by
  apply Units.ext
  rfl

theorem exists_triangular_integral (matrix : BinaryFiniteGL) :
    ∃ integral : IntegralBinaryGL,
      (matrix * (GeneralLinearGroup.map integralEmbedding integral)⁻¹).val 1 0 = 0 := by
  have localExistence (place : FinitePlace) :
      ∃ integral : GeneralLinearGroup (Fin 2) (place.adicCompletionIntegers ℚ),
        (GeneralLinearGroup.map (finiteEvaluation place) matrix *
          (GeneralLinearGroup.map (place.adicCompletionIntegers ℚ).subtype integral)⁻¹).val 1 0 = 0 := local_triangular
    (Valued.v : Valuation (place.adicCompletion ℚ) (WithZero (Multiplicative ℤ)))
    (GeneralLinearGroup.map (finiteEvaluation place) matrix)
  choose localMatrices localProperty using localExistence
  refine ⟨assemble localMatrices, ?_⟩
  apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
  intro place
  change (GeneralLinearGroup.map (finiteEvaluation place)
    (matrix * (GeneralLinearGroup.map integralEmbedding (assemble localMatrices))⁻¹)).val 1 0 = 0
  rw [map_mul, map_inv, assemble_evaluation]
  exact localProperty place

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryFiniteTriangular
