module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Finite.Level
public import Mathlib.LinearAlgebra.Matrix.Swap

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteDecomposition

def lowerRow {ring : Type*} [CommRing ring] (first second : ring) : GL3 ring :=
  ⟨!![1, 0, 0; 0, 1, 0; first, second, 1],
    !![1, 0, 0; 0, 1, 0; -first, -second, 1], by
      ext row column
      fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
      ext row column
      fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def swapGL {ring : Type*} [CommRing ring] (first second : Fin 3) : GL3 ring :=
  ⟨Matrix.swap ring first second, Matrix.swap ring first second,
    Matrix.swap_mul_self first second, Matrix.swap_mul_self first second⟩

theorem exists_integral_lastRow {field : Type*} [Field field]
    {valueGroup : Type*} [LinearOrderedCommGroupWithZero valueGroup]
    (valuation : Valuation field valueGroup) (matrix : GL3 field) :
    ∃ integralMatrix : GL3 valuation.valuationSubring, ∃ scalar : field,
      scalar ≠ 0 ∧ ∀ column,
      matrix.val 2 column = scalar *
        (GeneralLinearGroup.map valuation.valuationSubring.subtype integralMatrix).val 2 column := by
  classical
  obtain ⟨pivot, _, maximality⟩ := Finset.exists_max_image Finset.univ
    (fun column : Fin 3 => valuation (matrix.val 2 column)) Finset.univ_nonempty
  have pivotNonzero : matrix.val 2 pivot ≠ 0 := by
    intro zeroPivot
    apply TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlagRows.lastRow_ne_zero matrix
    funext column
    apply valuation.zero_iff.mp
    apply le_antisymm _ zero_le
    simpa only [zeroPivot, map_zero] using maximality column (Finset.mem_univ column)
  let normalized : Fin 3 → valuation.valuationSubring := fun column =>
    ⟨matrix.val 2 (Equiv.swap pivot 2 column) / matrix.val 2 pivot, by
      apply (valuation.mem_valuationSubring_iff _).mpr
      rw [valuation.map_div]
      exact (div_le_one₀ (valuation.pos_iff.mpr pivotNonzero)).mpr
        (maximality _ (Finset.mem_univ _))⟩
  have normalizedLast : normalized 2 = 1 := by
    apply Subtype.ext
    simp [normalized, pivotNonzero]
  have lowerRowProperty (column : Fin 3) :
      (lowerRow (normalized 0) (normalized 1)).val 2 column = normalized column := by
    fin_cases column <;> simp [lowerRow, normalizedLast]
  let integralMatrix := lowerRow (normalized 0) (normalized 1) *
    (swapGL pivot 2 : GL3 valuation.valuationSubring)
  have rowProperty (column : Fin 3) :
      integralMatrix.val 2 column = normalized (Equiv.swap pivot 2 column) := by
    change ((fun index => (lowerRow (normalized 0) (normalized 1)).val 2 index) ᵥ*
      Matrix.swap valuation.valuationSubring pivot 2) column = _
    rw [Matrix.vecMul_swap]
    exact lowerRowProperty _
  refine ⟨integralMatrix, matrix.val 2 pivot, pivotNonzero, fun column => ?_⟩
  change matrix.val 2 column = matrix.val 2 pivot * (integralMatrix.val 2 column).val
  rw [rowProperty]
  simp only [normalized, Equiv.swap_apply_self]
  exact (mul_div_cancel₀ (matrix.val 2 column) pivotNonzero).symm

theorem exists_local_plane_integral {field : Type*} [Field field]
    {valueGroup : Type*} [LinearOrderedCommGroupWithZero valueGroup]
    (valuation : Valuation field valueGroup) (matrix : GL3 field) :
    ∃ integralMatrix : GL3 valuation.valuationSubring,
      matrix * (GeneralLinearGroup.map valuation.valuationSubring.subtype integralMatrix)⁻¹ ∈
        planeParabolic field := by
  obtain ⟨integralMatrix, scalar, _, rowProperty⟩ := exists_integral_lastRow valuation matrix
  refine ⟨integralMatrix, ?_⟩
  let embedded := GeneralLinearGroup.map valuation.valuationSubring.subtype integralMatrix
  have productRow (column : Fin 3) :
      (matrix * embedded⁻¹).val 2 column = scalar * (1 : Matrix (Fin 3) (Fin 3) field) 2 column := by
    calc
      (matrix * embedded⁻¹).val 2 column = scalar * (embedded.val * embedded.inv) 2 column := by
        simp only [Units.val_mul, Matrix.mul_apply, rowProperty, Finset.mul_sum, mul_assoc]
        rfl
      _ = _ := by rw [embedded.val_inv]
  constructor
  · simpa only [Matrix.one_apply, show (2 : Fin 3) ≠ 0 by decide, ite_false, mul_zero]
      using productRow 0
  · simpa only [Matrix.one_apply, show (2 : Fin 3) ≠ 1 by decide, ite_false, mul_zero]
      using productRow 1

def integralMatrixOfLocals
    (localMatrices : ∀ place : FinitePlace, GL3 (place.adicCompletionIntegers ℚ)) :
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL where
  val row column place := (localMatrices place).val row column
  inv row column place := (localMatrices place).inv row column
  val_inv := by
    apply Matrix.ext
    intro row column
    funext place
    change (∑ index : Fin 3,
      (localMatrices place).val row index * (localMatrices place).inv index column) =
        (1 : Matrix (Fin 3) (Fin 3) IntegralAdeles) row column place
    have equality := congrArg (fun matrix => matrix row column) (localMatrices place).val_inv
    simpa only [Matrix.mul_apply, Matrix.one_apply, ite_apply, Pi.one_apply, Pi.zero_apply] using equality
  inv_val := by
    apply Matrix.ext
    intro row column
    funext place
    change (∑ index : Fin 3,
      (localMatrices place).inv row index * (localMatrices place).val index column) =
        (1 : Matrix (Fin 3) (Fin 3) IntegralAdeles) row column place
    have equality := congrArg (fun matrix => matrix row column) (localMatrices place).inv_val
    simpa only [Matrix.mul_apply, Matrix.one_apply, ite_apply, Pi.one_apply, Pi.zero_apply] using equality

theorem integralMatrixOfLocals_evaluation
    (localMatrices : ∀ place : FinitePlace, GL3 (place.adicCompletionIntegers ℚ))
    (place : FinitePlace) :
    GeneralLinearGroup.map (finiteEvaluation place)
        (GeneralLinearGroup.map integralEmbedding (integralMatrixOfLocals localMatrices)) =
      GeneralLinearGroup.map (place.adicCompletionIntegers ℚ).subtype (localMatrices place) := by
  apply Units.ext
  rfl

theorem exists_finite_plane_integral (matrix : FiniteGL) :
    ∃ integralMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL,
      matrix * (GeneralLinearGroup.map integralEmbedding integralMatrix)⁻¹ ∈
        planeParabolic FiniteAdeles := by
  have localExistence (place : FinitePlace) :
      ∃ localMatrix : GL3 (place.adicCompletionIntegers ℚ),
        finiteGLAt place matrix *
          (GeneralLinearGroup.map (place.adicCompletionIntegers ℚ).subtype localMatrix)⁻¹ ∈
            planeParabolic (place.adicCompletion ℚ) :=
    exists_local_plane_integral
      (Valued.v : Valuation (place.adicCompletion ℚ) (WithZero (Multiplicative ℤ)))
      (finiteGLAt place matrix)
  choose localMatrices localProperty using localExistence
  let integralMatrix := integralMatrixOfLocals localMatrices
  have localEquality (place : FinitePlace) :
      GeneralLinearGroup.map (finiteEvaluation place)
          (matrix * (GeneralLinearGroup.map integralEmbedding integralMatrix)⁻¹) =
        finiteGLAt place matrix *
          (GeneralLinearGroup.map (place.adicCompletionIntegers ℚ).subtype (localMatrices place))⁻¹ := by
    dsimp only [integralMatrix]
    rw [map_mul, map_inv, integralMatrixOfLocals_evaluation]
    rfl
  refine ⟨integralMatrix, ?_, ?_⟩
  · apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
    intro place
    change (GeneralLinearGroup.map (finiteEvaluation place)
      (matrix * (GeneralLinearGroup.map integralEmbedding integralMatrix)⁻¹)).val 2 0 = 0
    rw [localEquality]
    exact (localProperty place).1
  · apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
    intro place
    change (GeneralLinearGroup.map (finiteEvaluation place)
      (matrix * (GeneralLinearGroup.map integralEmbedding integralMatrix)⁻¹)).val 2 1 = 0
    rw [localEquality]
    exact (localProperty place).2

theorem finite_plane_integral_factorization (matrix : FiniteGL) :
    ∃ parabolicElement : planeParabolic FiniteAdeles,
      ∃ integralMatrix : TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteLevel.IntegralFiniteGL,
      matrix = parabolicElement.val * GeneralLinearGroup.map integralEmbedding integralMatrix := by
  obtain ⟨integralMatrix, membership⟩ := exists_finite_plane_integral matrix
  refine ⟨⟨matrix * (GeneralLinearGroup.map integralEmbedding integralMatrix)⁻¹, membership⟩,
    integralMatrix, ?_⟩
  exact (inv_mul_cancel_right matrix _).symm

theorem combineGL_mul {size : ℕ}
    (firstReal secondReal : GeneralLinearGroup (Fin size) ℝ)
    (firstFinite secondFinite : GeneralLinearGroup (Fin size) FiniteAdeles) :
    combineGL (firstReal * secondReal) (firstFinite * secondFinite) =
      combineGL firstReal firstFinite * combineGL secondReal secondFinite := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  apply Prod.ext
  · simp only [combineGL, pairMatrix, Units.val_mul, Matrix.mul_apply, Prod.fst_sum, Prod.fst_mul]
  · simp only [combineGL, pairMatrix, Units.val_mul, Matrix.mul_apply, Prod.snd_sum, Prod.snd_mul]

theorem adelic_plane_compact_factorization (matrix : AdelicGL) :
    ∃ parabolicElement : planeParabolic Adeles, ∃ compactElement : AdelicGL,
      matrix = parabolicElement.val * compactElement ∧ inMaximalCompact compactElement := by
  obtain ⟨realParabolic, realCompact, realFactorization, orthogonality, _⟩ :=
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealDecomposition.exists_plane_orthogonal (realGroup matrix)
  obtain ⟨finiteParabolic, finiteCompact, finiteFactorization⟩ :=
    finite_plane_integral_factorization (finiteGroup matrix)
  let parabolicElement : planeParabolic Adeles :=
    ⟨combineGL realParabolic.val finiteParabolic.val, by
      constructor
      · change (realParabolic.val.val 2 0, finiteParabolic.val.val 2 0) = 0
        simp only [realParabolic.property.1, finiteParabolic.property.1, Prod.zero_eq_mk]
      · change (realParabolic.val.val 2 1, finiteParabolic.val.val 2 1) = 0
        simp only [realParabolic.property.2, finiteParabolic.property.2, Prod.zero_eq_mk]⟩
  refine ⟨parabolicElement, combineGL realCompact
    (GeneralLinearGroup.map integralEmbedding finiteCompact), ?_, orthogonality, finiteCompact, rfl⟩
  calc
    matrix = combineGL (realGroup matrix) (finiteGroup matrix) := by
      rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.combineGL_eq_mul, ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adelicGL_eq_mul]
    _ = _ := by rw [realFactorization, finiteFactorization, combineGL_mul]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteDecomposition
