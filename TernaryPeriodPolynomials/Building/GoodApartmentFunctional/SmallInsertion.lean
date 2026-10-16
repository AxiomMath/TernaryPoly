module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.FrameMoves

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers TernaryPeriodPolynomials.GoodApartmentFunctional.Presentation TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralReduction
open TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralSymbols TernaryPeriodPolynomials.GoodApartmentFunctional.FrameMoves

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.SmallInsertion

noncomputable section

def matrixSymbol (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) : SymbolSpace := by
  classical
  exact if unit : IsUnit matrix.det then
    frameSymbol ⟨GeneralLinearGroup.mk'' matrix unit,
      by simpa only [GeneralLinearGroup.val_mk''] using
        (show ∀ column, (matrix 2 column : ZMod 3) = 1 from normalized)⟩
    else 0

theorem matrixSymbol_of_frame (frame : NormalizedFrames)
    (normalized : normalizedIntegralMatrix frame.val.val) :
    matrixSymbol frame.val.val normalized = frameSymbol frame := by
  classical
  have unit : IsUnit frame.val.val.det := Matrix.isUnits_det_units frame.val
  rw [matrixSymbol, dite_eq_left unit]
  congr 1
  apply normalizedFrames_eq_of_matrix_eq
  exact GeneralLinearGroup.val_mk'' _ _

theorem matrixSymbol_eq_of_matrix_eq (first second : Matrix (Fin 3) (Fin 3) ℤ)
    (firstNormalized : normalizedIntegralMatrix first)
    (secondNormalized : normalizedIntegralMatrix second) (equality : first = second) :
    matrixSymbol first firstNormalized = matrixSymbol second secondNormalized := by
  subst second
  rfl

theorem matrixSymbol_eq_zero (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (zero : matrix.det = 0) :
    matrixSymbol matrix normalized = 0 := by
  classical
  rw [matrixSymbol, dite_eq_right]
  rw [zero]
  exact not_isUnit_zero

def replacementSymbol (frame : NormalizedFrames) (vector : Fin 3 → ℤ)
    (normalized : (vector 2 : ZMod 3) = 1) (column : Fin 3) : SymbolSpace :=
  matrixSymbol (frame.val.val.updateCol column vector)
    (normalized_updateCol frame.val.val frame.property vector normalized column)

theorem replacementSymbol_of_frame (original updated : NormalizedFrames)
    (vector : Fin 3 → ℤ) (normalized : (vector 2 : ZMod 3) = 1) (column : Fin 3)
    (equality : original.val.val.updateCol column vector = updated.val.val) :
    replacementSymbol original vector normalized column = frameSymbol updated := by
  unfold replacementSymbol
  exact (matrixSymbol_eq_of_matrix_eq _ _ _ updated.property equality).trans
    (matrixSymbol_of_frame updated updated.property)

def cycleMatrix (matrix : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  matrix * integralWeyl.val

theorem cycleMatrix_entry (matrix : Matrix (Fin 3) (Fin 3) ℤ) (row column : Fin 3) :
    cycleMatrix matrix row column = matrix row (column + 1) := by
  fin_cases column <;>
    simp [cycleMatrix, integralWeyl, Adelic.weyl, Matrix.mul_apply, Fin.sum_univ_three]

theorem cycleMatrix_det (matrix : Matrix (Fin 3) (Fin 3) ℤ) :
    (cycleMatrix matrix).det = matrix.det := by
  rw [cycleMatrix, Matrix.det_mul]
  have determinant : integralWeyl.val.det = 1 := by
    simp [integralWeyl, Adelic.weyl, Matrix.det_fin_three]
  rw [determinant, mul_one]

theorem cycleMatrix_normalized (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) :
    normalizedIntegralMatrix (cycleMatrix matrix) := by
  intro column
  rw [cycleMatrix_entry]
  exact normalized (column + 1)

theorem matrixSymbol_cycle (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) :
    matrixSymbol (cycleMatrix matrix) (cycleMatrix_normalized matrix normalized) =
      matrixSymbol matrix normalized := by
  classical
  by_cases unit : IsUnit matrix.det
  · let frame : NormalizedFrames := ⟨GeneralLinearGroup.mk'' matrix unit,
      by simpa only [GeneralLinearGroup.val_mk''] using
        (show ∀ column, (matrix 2 column : ZMod 3) = 1 from normalized)⟩
    have matrixEquality : frame.val.val = matrix := GeneralLinearGroup.val_mk'' _ _
    have rotatedEquality : (rightCycleFrame frame).val.val = cycleMatrix matrix := by
      change frame.val.val * integralWeyl.val = cycleMatrix matrix
      rw [matrixEquality]
      rfl
    exact (matrixSymbol_eq_of_matrix_eq _ _ _ (rightCycleFrame frame).property
      rotatedEquality.symm).trans
      ((matrixSymbol_of_frame _ _).trans ((frameSymbol_cycle frame).trans
        ((matrixSymbol_of_frame frame frame.property).symm.trans
          (matrixSymbol_eq_of_matrix_eq _ _ frame.property normalized matrixEquality))))
  · have rotatedNotUnit : ¬IsUnit (cycleMatrix matrix).det := by
      rwa [cycleMatrix_det]
    simp only [matrixSymbol, dite_eq_right unit, dite_eq_right rotatedNotUnit]

theorem replacementSymbol_cycle (frame : NormalizedFrames) (vector : Fin 3 → ℤ)
    (normalized : (vector 2 : ZMod 3) = 1) (column : Fin 3) :
    replacementSymbol (rightCycleFrame frame) vector normalized column =
      replacementSymbol frame vector normalized (column + 1) := by
  have equality : (rightCycleFrame frame).val.val.updateCol column vector =
      cycleMatrix (frame.val.val.updateCol (column + 1) vector) := by
    ext row candidate
    fin_cases column <;> fin_cases candidate <;>
      simp [Matrix.updateCol, cycleMatrix_entry, rightCycleFrame_entry]
  exact (matrixSymbol_eq_of_matrix_eq _ _ _ _ equality).trans (matrixSymbol_cycle _ _)

def SubdivisionIdentity (frame : NormalizedFrames) (vector : Fin 3 → ℤ)
    (normalized : (vector 2 : ZMod 3) = 1) : Prop :=
  frameSymbol frame = ∑ column, replacementSymbol frame vector normalized column

theorem subdivisionIdentity_cycle (frame : NormalizedFrames) (vector : Fin 3 → ℤ)
    (normalized : (vector 2 : ZMod 3) = 1) :
    SubdivisionIdentity (rightCycleFrame frame) vector normalized ↔
      SubdivisionIdentity frame vector normalized := by
  simp only [SubdivisionIdentity, Fin.sum_univ_three, frameSymbol_cycle,
    replacementSymbol_cycle, Fin.reduceAdd]
  constructor <;> intro equality <;> rw [equality] <;> abel

theorem subdivisionIdentity_column (frame : NormalizedFrames) (column : Fin 3) :
    SubdivisionIdentity frame (frame.val.val.col column) (frame.property column) := by
  have same : replacementSymbol frame (frame.val.val.col column) (frame.property column) column =
      frameSymbol frame := by
    apply replacementSymbol_of_frame
    exact Matrix.updateCol_eq_self _ _
  have other (candidate : Fin 3) (distinct : candidate ≠ column) :
      replacementSymbol frame (frame.val.val.col column) (frame.property column) candidate = 0 := by
    apply matrixSymbol_eq_zero
    exact Matrix.det_updateCol_eq_zero (Ne.symm distinct)
  unfold SubdivisionIdentity
  rw [Finset.sum_eq_single column]
  · exact same.symm
  · intro candidate _membership distinct
    exact other candidate distinct
  · simp

theorem subdivisionIdentity_augmented (frame : NormalizedFrames) :
    SubdivisionIdentity frame (augmentedVector frame) (augmentedVector_normalized frame) := by
  have first : replacementSymbol frame (augmentedVector frame) (augmentedVector_normalized frame) 0 =
      frameSymbol (augmentedFirstFrame frame) :=
    replacementSymbol_of_frame _ _ _ _ _ (augmentedFirstFrame_matrix frame).symm
  have second : replacementSymbol frame (augmentedVector frame) (augmentedVector_normalized frame) 1 =
      frameSymbol (augmentedSecondFrame frame) :=
    replacementSymbol_of_frame _ _ _ _ _ (augmentedSecondFrame_matrix frame).symm
  have third : replacementSymbol frame (augmentedVector frame) (augmentedVector_normalized frame) 2 = 0 := by
    apply matrixSymbol_eq_zero
    rw [augmentedVector, ← neg_one_smul ℤ, Matrix.det_updateCol_smul,
      Matrix.det_updateCol_add]
    have firstZero : (frame.val.val.updateCol 2 (frame.val.val.col 0)).det = 0 :=
      Matrix.det_updateCol_eq_zero (by decide : (0 : Fin 3) ≠ 2)
    have secondZero : (frame.val.val.updateCol 2 (frame.val.val.col 1)).det = 0 :=
      Matrix.det_updateCol_eq_zero (by decide : (1 : Fin 3) ≠ 2)
    rw [firstZero, secondZero, zero_add, mul_zero]
  unfold SubdivisionIdentity
  rw [Fin.sum_univ_three, first, second, third, add_zero]
  exact frameSymbol_augmented frame

theorem subdivisionIdentity_mixed (frame : NormalizedFrames) :
    SubdivisionIdentity frame (mixedVector frame) (mixedVector_normalized frame) := by
  have first : replacementSymbol frame (mixedVector frame) (mixedVector_normalized frame) 0 =
      frameSymbol (mixedFirstFrame frame) :=
    replacementSymbol_of_frame _ _ _ _ _ (mixedFirstFrame_matrix frame).symm
  have second : replacementSymbol frame (mixedVector frame) (mixedVector_normalized frame) 1 =
      frameSymbol (mixedSecondFrame frame) :=
    replacementSymbol_of_frame _ _ _ _ _ (mixedSecondFrame_matrix frame).symm
  have third : replacementSymbol frame (mixedVector frame) (mixedVector_normalized frame) 2 =
      frameSymbol (mixedThirdFrame frame) :=
    replacementSymbol_of_frame _ _ _ _ _ (mixedThirdFrame_matrix frame).symm
  unfold SubdivisionIdentity
  rw [Fin.sum_univ_three, first, second, third]
  exact frameSymbol_mixed frame

def integerCoordinates (frame : NormalizedFrames) (vector : Fin 3 → ℤ) : Fin 3 → ℤ :=
  frame.val⁻¹.val *ᵥ vector

theorem integerCoordinates_reconstruct (frame : NormalizedFrames) (vector : Fin 3 → ℤ) :
    frame.val.val *ᵥ integerCoordinates frame vector = vector := by
  rw [integerCoordinates, Matrix.mulVec_mulVec, ← GeneralLinearGroup.coe_mul,
    mul_inv_cancel, GeneralLinearGroup.coe_one, Matrix.one_mulVec]

theorem replacement_determinant (frame : NormalizedFrames) (vector : Fin 3 → ℤ)
    (column : Fin 3) :
    (frame.val.val.updateCol column vector).det =
      integerCoordinates frame vector column * frame.val.val.det := by
  conv_lhs => rw [← integerCoordinates_reconstruct frame vector]
  have decomposition : frame.val.val *ᵥ integerCoordinates frame vector =
      fun row => ∑ candidate, integerCoordinates frame vector candidate •
        frame.val.val row candidate := by
    ext row
    simp only [Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm]
  conv_lhs => rw [decomposition, Matrix.det_updateCol_sum, smul_eq_mul]

theorem replacement_determinant_abs (frame : NormalizedFrames) (vector : Fin 3 → ℤ)
    (column : Fin 3) :
    |(frame.val.val.updateCol column vector).det| = |integerCoordinates frame vector column| := by
  rw [replacement_determinant, abs_mul,
    Int.isUnit_iff_abs_eq.mp (Matrix.isUnits_det_units frame.val), mul_one]

theorem integerCoordinates_normalized (frame : NormalizedFrames) (vector : Fin 3 → ℤ)
    (normalized : (vector 2 : ZMod 3) = 1) :
    (integerCoordinates frame vector 0 + integerCoordinates frame vector 1 +
      integerCoordinates frame vector 2 : ZMod 3) = 1 := by
  have equality := normalizedIntegralMatrix_lastCoordinate frame.val.val frame.property
    (integerCoordinates frame vector)
  rw [integerCoordinates_reconstruct, normalized, Fin.sum_univ_three] at equality
  exact equality.symm

theorem subdivisionIdentity_of_vector_eq (frame : NormalizedFrames) (first second : Fin 3 → ℤ)
    (firstNormalized : (first 2 : ZMod 3) = 1) (secondNormalized : (second 2 : ZMod 3) = 1)
    (equality : first = second) (identity : SubdivisionIdentity frame second secondNormalized) :
    SubdivisionIdentity frame first firstNormalized := by
  subst second
  exact identity

theorem subdivisionIdentity_augmented_cycle (frame : NormalizedFrames) :
    SubdivisionIdentity frame (augmentedVector (rightCycleFrame frame))
      (augmentedVector_normalized (rightCycleFrame frame)) :=
  (subdivisionIdentity_cycle _ _ _).mp (subdivisionIdentity_augmented (rightCycleFrame frame))

theorem subdivisionIdentity_augmented_cycle_twice (frame : NormalizedFrames) :
    SubdivisionIdentity frame (augmentedVector (rightCycleFrame (rightCycleFrame frame)))
      (augmentedVector_normalized (rightCycleFrame (rightCycleFrame frame))) :=
  (subdivisionIdentity_cycle _ _ _).mp
    ((subdivisionIdentity_cycle _ _ _).mp
      (subdivisionIdentity_augmented (rightCycleFrame (rightCycleFrame frame))))

theorem subdivisionIdentity_mixed_cycle (frame : NormalizedFrames) :
    SubdivisionIdentity frame (mixedVector (rightCycleFrame frame))
      (mixedVector_normalized (rightCycleFrame frame)) :=
  (subdivisionIdentity_cycle _ _ _).mp (subdivisionIdentity_mixed (rightCycleFrame frame))

theorem subdivisionIdentity_mixed_cycle_twice (frame : NormalizedFrames) :
    SubdivisionIdentity frame (mixedVector (rightCycleFrame (rightCycleFrame frame)))
      (mixedVector_normalized (rightCycleFrame (rightCycleFrame frame))) :=
  (subdivisionIdentity_cycle _ _ _).mp
    ((subdivisionIdentity_cycle _ _ _).mp
      (subdivisionIdentity_mixed (rightCycleFrame (rightCycleFrame frame))))

theorem augmentedVector_cycle_entry (frame : NormalizedFrames) (row : Fin 3) :
    augmentedVector (rightCycleFrame frame) row =
      -(frame.val.val row 1 + frame.val.val row 2) := by
  change -((rightCycleFrame frame).val.val row 0 + (rightCycleFrame frame).val.val row 1) = _
  rw [rightCycleFrame_entry, rightCycleFrame_entry]
  rfl

theorem augmentedVector_cycle_twice_entry (frame : NormalizedFrames) (row : Fin 3) :
    augmentedVector (rightCycleFrame (rightCycleFrame frame)) row =
      -(frame.val.val row 2 + frame.val.val row 0) := by
  rw [augmentedVector_cycle_entry, rightCycleFrame_entry, rightCycleFrame_entry]
  rfl

theorem subdivisionIdentity_bounded (frame : NormalizedFrames) (vector : Fin 3 → ℤ)
    (normalized : (vector 2 : ZMod 3) = 1)
    (bounds : ∀ column, -1 ≤ integerCoordinates frame vector column ∧
      integerCoordinates frame vector column ≤ 1) :
    SubdivisionIdentity frame vector normalized := by
  obtain ⟨firstLower, firstUpper⟩ := bounds 0
  obtain ⟨secondLower, secondUpper⟩ := bounds 1
  obtain ⟨thirdLower, thirdUpper⟩ := bounds 2
  have residue := integerCoordinates_normalized frame vector normalized
  have modulus : (integerCoordinates frame vector 0 + integerCoordinates frame vector 1 +
      integerCoordinates frame vector 2) % 3 = 1 := by
    apply (ZMod.intCast_eq_intCast_iff' _ 1 3).mp
    simpa only [Int.cast_add, Int.cast_one] using residue
  have reconstruction := (integerCoordinates_reconstruct frame vector).symm
  have patterns :
      (integerCoordinates frame vector 0 = 1 ∧ integerCoordinates frame vector 1 = 0 ∧
        integerCoordinates frame vector 2 = 0) ∨
      (integerCoordinates frame vector 0 = 0 ∧ integerCoordinates frame vector 1 = 1 ∧
        integerCoordinates frame vector 2 = 0) ∨
      (integerCoordinates frame vector 0 = 0 ∧ integerCoordinates frame vector 1 = 0 ∧
        integerCoordinates frame vector 2 = 1) ∨
      (integerCoordinates frame vector 0 = -1 ∧ integerCoordinates frame vector 1 = -1 ∧
        integerCoordinates frame vector 2 = 0) ∨
      (integerCoordinates frame vector 0 = 0 ∧ integerCoordinates frame vector 1 = -1 ∧
        integerCoordinates frame vector 2 = -1) ∨
      (integerCoordinates frame vector 0 = -1 ∧ integerCoordinates frame vector 1 = 0 ∧
        integerCoordinates frame vector 2 = -1) ∨
      (integerCoordinates frame vector 0 = 1 ∧ integerCoordinates frame vector 1 = 1 ∧
        integerCoordinates frame vector 2 = -1) ∨
      (integerCoordinates frame vector 0 = -1 ∧ integerCoordinates frame vector 1 = 1 ∧
        integerCoordinates frame vector 2 = 1) ∨
      (integerCoordinates frame vector 0 = 1 ∧ integerCoordinates frame vector 1 = -1 ∧
        integerCoordinates frame vector 2 = 1) := by
    interval_cases integerCoordinates frame vector 0 <;>
      interval_cases integerCoordinates frame vector 1 <;>
      interval_cases integerCoordinates frame vector 2 <;> omega
  rcases patterns with ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩ | ⟨first, second, third⟩ | ⟨first, second, third⟩ |
    ⟨first, second, third⟩
  · apply subdivisionIdentity_of_vector_eq _ _ _ _ _ _ (subdivisionIdentity_column frame 0)
    rw [reconstruction]
    ext row
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col, first, second, third]
  · apply subdivisionIdentity_of_vector_eq _ _ _ _ _ _ (subdivisionIdentity_column frame 1)
    rw [reconstruction]
    ext row
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col, first, second, third]
  · apply subdivisionIdentity_of_vector_eq _ _ _ _ _ _ (subdivisionIdentity_column frame 2)
    rw [reconstruction]
    ext row
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col, first, second, third]
  · apply subdivisionIdentity_of_vector_eq _ _ _ _ _ _ (subdivisionIdentity_augmented frame)
    rw [reconstruction]
    ext row
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col, augmentedVector,
      first, second, third, add_comm]
  · apply subdivisionIdentity_of_vector_eq _ _ _ _ _ _ (subdivisionIdentity_augmented_cycle frame)
    rw [reconstruction]
    ext row
    rw [augmentedVector_cycle_entry]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, first, second, third, add_comm]
  · apply subdivisionIdentity_of_vector_eq _ _ _ _ _ _ (subdivisionIdentity_augmented_cycle_twice frame)
    rw [reconstruction]
    ext row
    rw [augmentedVector_cycle_twice_entry]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, first, second, third, add_comm]
  · apply subdivisionIdentity_of_vector_eq _ _ _ _ _ _ (subdivisionIdentity_mixed frame)
    rw [reconstruction]
    ext row
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col, mixedVector,
      first, second, third, sub_eq_add_neg]
  · apply subdivisionIdentity_of_vector_eq _ _ _ _ _ _ (subdivisionIdentity_mixed_cycle frame)
    rw [reconstruction]
    ext row
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col, mixedVector,
      Matrix.transpose_apply, rightCycleFrame_entry, first, second, third, sub_eq_add_neg,
      add_comm, add_assoc]
  · apply subdivisionIdentity_of_vector_eq _ _ _ _ _ _ (subdivisionIdentity_mixed_cycle_twice frame)
    rw [reconstruction]
    ext row
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col, mixedVector,
      Matrix.transpose_apply, rightCycleFrame_entry, first, second, third, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc]

theorem subdivisionIdentity_small_determinants (frame : NormalizedFrames) (vector : Fin 3 → ℤ)
    (normalized : (vector 2 : ZMod 3) = 1)
    (bounds : ∀ column, |(frame.val.val.updateCol column vector).det| ≤ 1) :
    SubdivisionIdentity frame vector normalized := by
  apply subdivisionIdentity_bounded frame vector normalized
  intro column
  have bound := bounds column
  rw [replacement_determinant_abs, abs_le] at bound
  exact bound

def matrixChain (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) : NormalizedFrames →₀ ℂ := by
  classical
  exact if unit : IsUnit matrix.det then
    Finsupp.single ⟨GeneralLinearGroup.mk'' matrix unit, by
      simpa only [GeneralLinearGroup.val_mk''] using
        (show ∀ column, (matrix 2 column : ZMod 3) = 1 from normalized)⟩ 1
    else 0

theorem matrixChain_symbol (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) :
    presentationRelations.mkQ (matrixChain matrix normalized) = matrixSymbol matrix normalized := by
  classical
  by_cases unit : IsUnit matrix.det
  · simp only [matrixChain, matrixSymbol, dite_eq_left unit, frameSymbol]
  · simp only [matrixChain, matrixSymbol, dite_eq_right unit, map_zero]

def insertionRelation (frame : NormalizedFrames) (vector : Fin 3 → ℤ)
    (normalized : (vector 2 : ZMod 3) = 1) : NormalizedFrames →₀ ℂ :=
  Finsupp.single frame 1 - ∑ column, matrixChain (frame.val.val.updateCol column vector)
    (normalized_updateCol frame.val.val frame.property vector normalized column)

theorem insertionRelation_mem (frame : NormalizedFrames) (vector : Fin 3 → ℤ)
    (normalized : (vector 2 : ZMod 3) = 1)
    (bounds : ∀ column, |(frame.val.val.updateCol column vector).det| ≤ 1) :
    insertionRelation frame vector normalized ∈ presentationRelations := by
  apply (Submodule.Quotient.mk_eq_zero presentationRelations).mp
  change presentationRelations.mkQ (insertionRelation frame vector normalized) = 0
  rw [insertionRelation, map_sub, map_sum]
  simp only [matrixChain_symbol]
  change frameSymbol frame - ∑ column, replacementSymbol frame vector normalized column = 0
  exact sub_eq_zero.mpr (subdivisionIdentity_small_determinants frame vector normalized bounds)

theorem insertionRelation_evaluation {degree : ℕ} (polynomial : HomogeneousPoly degree)
    (solution : SymmetricSolution polynomial) (frame : NormalizedFrames) (vector : Fin 3 → ℤ)
    (normalized : (vector 2 : ZMod 3) = 1)
    (bounds : ∀ column, |(frame.val.val.updateCol column vector).det| ≤ 1) :
    frameEvaluation polynomial (insertionRelation frame vector normalized) = 0 :=
  presentationRelations_evaluation polynomial solution
    (insertionRelation_mem frame vector normalized bounds)

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.SmallInsertion
