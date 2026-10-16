module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.BalancedReduction

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers TernaryPeriodPolynomials.GoodApartmentFunctional.Presentation TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralReduction TernaryPeriodPolynomials.GoodApartmentFunctional.BalancedReduction
open TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralSymbols TernaryPeriodPolynomials.GoodApartmentFunctional.SmallInsertion TernaryPeriodPolynomials.GoodApartmentFunctional.FrameMoves

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.ReductionCompatibility

noncomputable section

def swapColumns (matrix : Matrix (Fin 3) (Fin 3) ℤ) (first second : Fin 3) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  matrix.submatrix id (Equiv.swap first second)

theorem swapColumns_normalized (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (first second : Fin 3) :
    normalizedIntegralMatrix (swapColumns matrix first second) :=
  fun column => normalized (Equiv.swap first second column)

theorem swapColumns_det (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (first second : Fin 3) (distinct : first ≠ second) :
    (swapColumns matrix first second).det = -matrix.det := by
  rw [swapColumns, Matrix.det_permute', Equiv.Perm.sign_swap distinct]
  simp

theorem swapColumns_updateCol (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (first second column : Fin 3) (vector : Fin 3 → ℤ) :
    (swapColumns matrix first second).updateCol column vector =
      swapColumns (matrix.updateCol (Equiv.swap first second column) vector) first second := by
  ext row candidate
  simp only [swapColumns, Matrix.submatrix_apply, id_eq, Matrix.updateCol_apply]
  congr 1
  exact propext (Equiv.apply_eq_iff_eq (Equiv.swap first second)).symm

theorem double_replacement_swap (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (first second : Fin 3) (distinct : first ≠ second) (firstVector secondVector : Fin 3 → ℤ) :
    (matrix.updateCol first firstVector).updateCol second secondVector =
      swapColumns ((matrix.updateCol second firstVector).updateCol first secondVector)
        first second := by
  ext row column
  by_cases firstEquality : column = first
  · subst column
    simp [swapColumns, distinct, Ne.symm distinct]
  · by_cases secondEquality : column = second
    · subst column
      simp [swapColumns]
    · simp [swapColumns, firstEquality, secondEquality,
        Equiv.swap_apply_of_ne_of_ne firstEquality secondEquality]

theorem matrixSymbol_swap (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix)
    (first second : Fin 3) (distinct : first ≠ second) :
    matrixSymbol (swapColumns matrix first second)
      (swapColumns_normalized matrix normalized first second) = -matrixSymbol matrix normalized := by
  classical
  by_cases unit : IsUnit matrix.det
  · let frame : NormalizedFrames := ⟨GeneralLinearGroup.mk'' matrix unit,
      by simpa only [GeneralLinearGroup.val_mk''] using
        (show ∀ column, (matrix 2 column : ZMod 3) = 1 from normalized)⟩
    have frameEquality : frame.val.val = matrix := GeneralLinearGroup.val_mk'' _ _
    have original : matrixSymbol matrix normalized = frameSymbol frame :=
      (matrixSymbol_eq_of_matrix_eq _ _ _ frame.property frameEquality.symm).trans
        (matrixSymbol_of_frame frame frame.property)
    rw [original]
    have firstSwap : swapColumns matrix 0 1 = (rightSwapFrame frame).val.val := by
      ext row column
      simp only [swapColumns, Matrix.submatrix_apply, id_eq, rightSwapFrame_entry, frameEquality]
    have lastSwap : swapColumns matrix 1 2 = (lastSwapFrame frame).val.val := by
      ext row column
      fin_cases column <;>
        simp [swapColumns, lastSwapFrame, rightSwapFrame_entry, rightCycleFrame_entry,
          frameEquality, Equiv.swap_apply_def]
    have outerSwap : swapColumns matrix 0 2 = (outerSwapFrame frame).val.val := by
      ext row column
      fin_cases column <;>
        simp [swapColumns, outerSwapFrame, rightSwapFrame_entry, rightCycleFrame_entry,
          frameEquality, Equiv.swap_apply_def]
    have firstIdentity := (matrixSymbol_eq_of_matrix_eq _ _
      (swapColumns_normalized matrix normalized 0 1) (rightSwapFrame frame).property firstSwap).trans
        ((matrixSymbol_of_frame _ _).trans (frameSymbol_swap frame))
    have lastIdentity := (matrixSymbol_eq_of_matrix_eq _ _
      (swapColumns_normalized matrix normalized 1 2) (lastSwapFrame frame).property lastSwap).trans
        ((matrixSymbol_of_frame _ _).trans (frameSymbol_lastSwap frame))
    have outerIdentity := (matrixSymbol_eq_of_matrix_eq _ _
      (swapColumns_normalized matrix normalized 0 2) (outerSwapFrame frame).property outerSwap).trans
        ((matrixSymbol_of_frame _ _).trans (frameSymbol_outerSwap frame))
    have firstReverse : matrixSymbol (swapColumns matrix 1 0)
        (swapColumns_normalized matrix normalized 1 0) = -frameSymbol frame := by
      exact (matrixSymbol_eq_of_matrix_eq _ _ _ _
        (congrArg (matrix.submatrix id) (congrArg Equiv.toFun
          (Equiv.swap_comm 1 0)))).trans firstIdentity
    have lastReverse : matrixSymbol (swapColumns matrix 2 1)
        (swapColumns_normalized matrix normalized 2 1) = -frameSymbol frame := by
      exact (matrixSymbol_eq_of_matrix_eq _ _ _ _
        (congrArg (matrix.submatrix id) (congrArg Equiv.toFun
          (Equiv.swap_comm 2 1)))).trans lastIdentity
    have outerReverse : matrixSymbol (swapColumns matrix 2 0)
        (swapColumns_normalized matrix normalized 2 0) = -frameSymbol frame := by
      exact (matrixSymbol_eq_of_matrix_eq _ _ _ _
        (congrArg (matrix.submatrix id) (congrArg Equiv.toFun
          (Equiv.swap_comm 2 0)))).trans outerIdentity
    fin_cases first <;> fin_cases second
    all_goals try exact False.elim (distinct rfl)
    all_goals first
      | exact firstIdentity
      | exact lastIdentity
      | exact outerIdentity
      | exact firstReverse
      | exact lastReverse
      | exact outerReverse
  · have notUnit : ¬IsUnit (swapColumns matrix first second).det := by
      rw [swapColumns_det matrix first second distinct]
      simpa only [IsUnit.neg_iff] using unit
    simp only [matrixSymbol, dite_eq_right unit, dite_eq_right notUnit, neg_zero]

theorem mixing_le_one (first second third fourth : ℚ)
    (balanced : |first| + |second| ≤ 1) (thirdBound : |third| ≤ 1)
    (fourthBound : |fourth| ≤ 1) : |first * fourth - second * third| ≤ 1 := by
  calc
    |first * fourth - second * third| ≤ |first| * |fourth| + |second| * |third| := by
      simpa only [abs_mul] using abs_sub (first * fourth) (second * third)
    _ ≤ |first| + |second| := by
      nlinarith [abs_nonneg first, abs_nonneg second]
    _ ≤ 1 := balanced

theorem mixing_eq_one_boundaries (first second third fourth : ℚ)
    (firstBound : |first| < 1) (secondBound : |second| < 1)
    (balanced : |first| + |second| ≤ 1) (thirdBound : |third| ≤ 1)
    (fourthBound : |fourth| ≤ 1) (equality : |first * fourth - second * third| = 1) :
    |third| = 1 ∧ |fourth| = 1 := by
  have estimate : |first| * |fourth| + |second| * |third| ≥ 1 := by
    calc
      1 = |first * fourth - second * third| := equality.symm
      _ ≤ |first| * |fourth| + |second| * |third| := by
        simpa only [abs_mul] using abs_sub (first * fourth) (second * third)
  have firstPositive : 0 < |first| := by
    by_contra notPositive
    have zero : |first| = 0 := le_antisymm (le_of_not_gt notPositive) (abs_nonneg first)
    nlinarith [abs_nonneg second, abs_nonneg third, abs_nonneg fourth]
  have secondPositive : 0 < |second| := by
    by_contra notPositive
    have zero : |second| = 0 := le_antisymm (le_of_not_gt notPositive) (abs_nonneg second)
    nlinarith [abs_nonneg first, abs_nonneg third, abs_nonneg fourth]
  constructor
  · nlinarith [abs_nonneg first, abs_nonneg second]
  · nlinarith [abs_nonneg first, abs_nonneg second]

theorem mixed_replacement_determinant_le (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (first second : Fin 3 → ℤ)
    (balanced : BalancedCoordinates (inverseCoordinates matrix nonzero first))
    (bounds : ∀ column, |inverseCoordinates matrix nonzero second column| ≤ 1)
    (firstColumn secondColumn : Fin 3) (distinct : firstColumn ≠ secondColumn) :
    ((matrix.updateCol firstColumn first).updateCol secondColumn second).det.natAbs ≤
      matrix.det.natAbs := by
  have determinant := congrArg abs
    (determinant_updateCol_updateCol matrix nonzero first second firstColumn secondColumn distinct)
  rw [abs_mul] at determinant
  have bound := mixing_le_one
    (inverseCoordinates matrix nonzero first firstColumn)
    (inverseCoordinates matrix nonzero first secondColumn)
    (inverseCoordinates matrix nonzero second firstColumn)
    (inverseCoordinates matrix nonzero second secondColumn)
    (balanced.2 firstColumn secondColumn distinct) (bounds firstColumn) (bounds secondColumn)
  have comparison := mul_le_mul_of_nonneg_right bound
    (abs_nonneg (matrix.det : ℚ))
  rw [one_mul, ← determinant] at comparison
  have castAbs (integer : ℤ) : (integer.natAbs : ℚ) = |(integer : ℚ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [← castAbs, ← castAbs] at comparison
  exact_mod_cast comparison

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.ReductionCompatibility
