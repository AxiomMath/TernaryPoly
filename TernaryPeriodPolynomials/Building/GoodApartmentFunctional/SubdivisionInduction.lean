module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.ReductionCompatibility

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers TernaryPeriodPolynomials.GoodApartmentFunctional.Presentation TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralReduction
open TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralSymbols TernaryPeriodPolynomials.GoodApartmentFunctional.SmallInsertion TernaryPeriodPolynomials.GoodApartmentFunctional.BalancedReduction
open TernaryPeriodPolynomials.GoodApartmentFunctional.ReductionCompatibility

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.SubdivisionInduction

noncomputable section

def ReducedSubdivision (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (vector : Fin 3 → ℤ)
    (vectorNormalized : (vector 2 : ZMod 3) = 1) : Prop :=
  reducedSymbol matrix normalized = ∑ column, reducedSymbol (matrix.updateCol column vector)
    (normalized_updateCol matrix normalized vector vectorNormalized column)

def SubdivisionBelow (bound : ℕ) : Prop :=
  ∀ (matrix : Matrix (Fin 3) (Fin 3) ℤ) (normalized : normalizedIntegralMatrix matrix)
    (vector : Fin 3 → ℤ) (vectorNormalized : (vector 2 : ZMod 3) = 1),
    matrix.det.natAbs < bound →
    (∀ column, (matrix.updateCol column vector).det.natAbs < bound) →
    ReducedSubdivision matrix normalized vector vectorNormalized

def AlternatingBelow (bound : ℕ) : Prop :=
  ∀ (matrix : Matrix (Fin 3) (Fin 3) ℤ) (normalized : normalizedIntegralMatrix matrix)
    (first second : Fin 3), first ≠ second → matrix.det.natAbs < bound →
    reducedSymbol (swapColumns matrix first second)
      (swapColumns_normalized matrix normalized first second) = -reducedSymbol matrix normalized

theorem reducedSymbol_eq_of_matrix_eq (first second : Matrix (Fin 3) (Fin 3) ℤ)
    (firstNormalized : normalizedIntegralMatrix first)
    (secondNormalized : normalizedIntegralMatrix second) (equality : first = second) :
    reducedSymbol first firstNormalized = reducedSymbol second secondNormalized := by
  subst second
  rfl

theorem reducedSymbol_eq_matrixSymbol_small (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (bound : matrix.det.natAbs ≤ 1) :
    reducedSymbol matrix normalized = matrixSymbol matrix normalized := by
  by_cases zero : matrix.det = 0
  · rw [reducedSymbol_zero matrix normalized zero, matrixSymbol_eq_zero matrix normalized zero]
  · have positive : 0 < matrix.det.natAbs := Int.natAbs_pos.mpr zero
    exact reducedSymbol_unimodular matrix normalized (by omega)

theorem alternatingBelow_two : AlternatingBelow 2 := by
  intro matrix normalized first second distinct bound
  have swappedBound : (swapColumns matrix first second).det.natAbs ≤ 1 := by
    rw [swapColumns_det matrix first second distinct, Int.natAbs_neg]
    omega
  rw [reducedSymbol_eq_matrixSymbol_small _ _ swappedBound,
    reducedSymbol_eq_matrixSymbol_small matrix normalized (by omega)]
  exact matrixSymbol_swap matrix normalized first second distinct

theorem replacement_rebase_same (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (vector : Fin 3 → ℤ) (pivot : Fin 3) :
    (matrix.updateCol pivot vector).updateCol pivot (matrix.col pivot) = matrix := by
  ext row column
  by_cases equality : column = pivot
  · subst column
    simp [Matrix.col]
  · simp [equality]

theorem replacement_rebase_other (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (vector : Fin 3 → ℤ) (pivot column : Fin 3) (distinct : pivot ≠ column) :
    (matrix.updateCol pivot vector).updateCol column (matrix.col pivot) =
      swapColumns (matrix.updateCol column vector) pivot column := by
  ext row candidate
  by_cases pivotEquality : candidate = pivot
  · subst candidate
    simp [swapColumns, Matrix.col, distinct]
  · by_cases columnEquality : candidate = column
    · subst candidate
      simp [swapColumns, Matrix.col, distinct]
    · simp [swapColumns, Matrix.col, pivotEquality, columnEquality,
        Equiv.swap_apply_of_ne_of_ne pivotEquality columnEquality]

theorem reducedSubdivision_rebase (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (vector : Fin 3 → ℤ)
    (vectorNormalized : (vector 2 : ZMod 3) = 1) (pivot : Fin 3)
    (alternating : ∀ column, pivot ≠ column →
      reducedSymbol (swapColumns (matrix.updateCol column vector) pivot column)
        (swapColumns_normalized _
          (normalized_updateCol matrix normalized vector vectorNormalized column) pivot column) =
        -reducedSymbol (matrix.updateCol column vector)
          (normalized_updateCol matrix normalized vector vectorNormalized column)) :
    ReducedSubdivision matrix normalized vector vectorNormalized ↔
      ReducedSubdivision (matrix.updateCol pivot vector)
        (normalized_updateCol matrix normalized vector vectorNormalized pivot)
        (matrix.col pivot) (normalized pivot) := by
  have entry (column : Fin 3) :
      reducedSymbol ((matrix.updateCol pivot vector).updateCol column (matrix.col pivot))
        (normalized_updateCol _
          (normalized_updateCol matrix normalized vector vectorNormalized pivot)
          (matrix.col pivot) (normalized pivot) column) =
        if column = pivot then reducedSymbol matrix normalized
        else -reducedSymbol (matrix.updateCol column vector)
          (normalized_updateCol matrix normalized vector vectorNormalized column) := by
    by_cases equality : column = pivot
    · subst column
      rw [ite_eq_left rfl]
      congr 1
      exact replacement_rebase_same matrix vector pivot
    · rw [ite_eq_right equality]
      have distinct := Ne.symm equality
      exact (reducedSymbol_eq_of_matrix_eq _ _ _ _
        (replacement_rebase_other matrix vector pivot column distinct)).trans
          (alternating column distinct)
  unfold ReducedSubdivision
  simp_rw [entry]
  simp only [Fin.sum_univ_three]
  fin_cases pivot
  · change (reducedSymbol matrix normalized = reducedSymbol (matrix.updateCol 0 vector) _ +
      reducedSymbol (matrix.updateCol 1 vector) _ + reducedSymbol (matrix.updateCol 2 vector) _) ↔
      reducedSymbol (matrix.updateCol 0 vector) _ =
      reducedSymbol matrix normalized + -reducedSymbol (matrix.updateCol 1 vector) _ +
        -reducedSymbol (matrix.updateCol 2 vector) _
    constructor <;> intro identity <;> rw [identity] <;> module
  · change (reducedSymbol matrix normalized = reducedSymbol (matrix.updateCol 0 vector) _ +
      reducedSymbol (matrix.updateCol 1 vector) _ + reducedSymbol (matrix.updateCol 2 vector) _) ↔
      reducedSymbol (matrix.updateCol 1 vector) _ =
      -reducedSymbol (matrix.updateCol 0 vector) _ + reducedSymbol matrix normalized +
        -reducedSymbol (matrix.updateCol 2 vector) _
    constructor <;> intro identity <;> rw [identity] <;> module
  · change (reducedSymbol matrix normalized = reducedSymbol (matrix.updateCol 0 vector) _ +
      reducedSymbol (matrix.updateCol 1 vector) _ + reducedSymbol (matrix.updateCol 2 vector) _) ↔
      reducedSymbol (matrix.updateCol 2 vector) _ =
      -reducedSymbol (matrix.updateCol 0 vector) _ + -reducedSymbol (matrix.updateCol 1 vector) _ +
        reducedSymbol matrix normalized
    constructor <;> intro identity <;> rw [identity] <;> module

theorem reducedSubdivision_unimodular (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (vector : Fin 3 → ℤ)
    (vectorNormalized : (vector 2 : ZMod 3) = 1) (unit : IsUnit matrix.det)
    (replacementBounds : ∀ column, (matrix.updateCol column vector).det.natAbs ≤ 1) :
    ReducedSubdivision matrix normalized vector vectorNormalized := by
  let frame : NormalizedFrames := ⟨GeneralLinearGroup.mk'' matrix unit, by
    simpa only [GeneralLinearGroup.val_mk''] using
      (show ∀ column, (matrix 2 column : ZMod 3) = 1 from normalized)⟩
  have frameEquality : frame.val.val = matrix := GeneralLinearGroup.val_mk'' _ _
  have smallBounds : ∀ column, |(frame.val.val.updateCol column vector).det| ≤ 1 := by
    intro column
    rw [frameEquality, ← Int.natCast_natAbs]
    exact_mod_cast replacementBounds column
  have subdivision := subdivisionIdentity_small_determinants frame vector vectorNormalized smallBounds
  unfold SubdivisionIdentity replacementSymbol at subdivision
  unfold ReducedSubdivision
  calc
    reducedSymbol matrix normalized = frameSymbol frame :=
      (reducedSymbol_eq_of_matrix_eq _ _ _ _ frameEquality.symm).trans (reducedSymbol_frame frame)
    _ = ∑ column, matrixSymbol (frame.val.val.updateCol column vector)
        (normalized_updateCol frame.val.val frame.property vector vectorNormalized column) := subdivision
    _ = ∑ column, reducedSymbol (matrix.updateCol column vector)
        (normalized_updateCol matrix normalized vector vectorNormalized column) := by
      apply Finset.sum_congr rfl
      intro column _membership
      exact (matrixSymbol_eq_of_matrix_eq _ _ _ _
        (congrArg (fun candidate => candidate.updateCol column vector) frameEquality)).trans
          (reducedSymbol_eq_matrixSymbol_small _ _ (replacementBounds column)).symm

theorem subdivisionBelow_two : SubdivisionBelow 2 := by
  intro matrix normalized vector vectorNormalized bound replacementBounds
  by_cases zero : matrix.det = 0
  · by_cases allZero : ∀ column, (matrix.updateCol column vector).det = 0
    · unfold ReducedSubdivision
      rw [reducedSymbol_zero matrix normalized zero]
      apply Eq.symm
      apply Finset.sum_eq_zero
      intro column _membership
      exact reducedSymbol_zero _ _ (allZero column)
    · obtain ⟨pivot, pivotNonzero⟩ := not_forall.mp allZero
      have pivotUnit : IsUnit (matrix.updateCol pivot vector).det :=
        Int.isUnit_iff_natAbs_eq.mpr (by
          have positive := Int.natAbs_pos.mpr pivotNonzero
          have pivotBound := replacementBounds pivot
          omega)
      apply (reducedSubdivision_rebase matrix normalized vector vectorNormalized pivot
        (fun column distinct => alternatingBelow_two _ _ pivot column distinct
          (replacementBounds column))).mpr
      apply reducedSubdivision_unimodular _ _ _ _ pivotUnit
      intro column
      by_cases equality : column = pivot
      · subst column
        rw [replacement_rebase_same, zero, Int.natAbs_zero]
        exact zero_le_one
      · rw [replacement_rebase_other matrix vector pivot column (Ne.symm equality),
          swapColumns_det _ pivot column (Ne.symm equality), Int.natAbs_neg]
        have columnBound := replacementBounds column
        omega
  · have unit : IsUnit matrix.det := Int.isUnit_iff_natAbs_eq.mpr (by
      have positive := Int.natAbs_pos.mpr zero
      omega)
    exact reducedSubdivision_unimodular matrix normalized vector vectorNormalized unit
      (fun column => by have columnBound := replacementBounds column; omega)

theorem double_replacement_same (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (first second : Fin 3 → ℤ) (column : Fin 3) :
    (matrix.updateCol column first).updateCol column second = matrix.updateCol column second := by
  ext row candidate
  by_cases equality : candidate = column
  · subst candidate
    simp
  · simp [equality]

theorem double_replacement_commute (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (first second : Fin 3 → ℤ) (firstColumn secondColumn : Fin 3)
    (distinct : firstColumn ≠ secondColumn) :
    (matrix.updateCol firstColumn first).updateCol secondColumn second =
      (matrix.updateCol secondColumn second).updateCol firstColumn first := by
  ext row column
  by_cases firstEquality : column = firstColumn
  · subst column
    simp [distinct]
  · by_cases secondEquality : column = secondColumn
    · subst column
      simp [Ne.symm distinct]
    · simp [firstEquality, secondEquality]

theorem sum_antisymmetric_off_diagonal (values : Fin 3 → Fin 3 → SymbolSpace)
    (antisymmetric : ∀ first second, first ≠ second → values first second = -values second first) :
    ∑ first, ∑ second, values first second = ∑ column, values column column := by
  simp only [Fin.sum_univ_three]
  rw [antisymmetric 0 1 (by decide), antisymmetric 0 2 (by decide),
    antisymmetric 1 2 (by decide)]
  module

theorem subdivision_sum_comparison (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (first second : Fin 3 → ℤ)
    (firstNormalized : (first 2 : ZMod 3) = 1)
    (secondNormalized : (second 2 : ZMod 3) = 1)
    (subdivisions : ∀ column, ReducedSubdivision (matrix.updateCol column first)
      (normalized_updateCol matrix normalized first firstNormalized column) second secondNormalized)
    (alternating : ∀ firstColumn secondColumn, firstColumn ≠ secondColumn →
      reducedSymbol (((matrix.updateCol firstColumn first).updateCol secondColumn second))
        (normalized_updateCol _
          (normalized_updateCol matrix normalized first firstNormalized firstColumn)
          second secondNormalized secondColumn) =
        -reducedSymbol (((matrix.updateCol secondColumn first).updateCol firstColumn second))
          (normalized_updateCol _
            (normalized_updateCol matrix normalized first firstNormalized secondColumn)
            second secondNormalized firstColumn)) :
    (∑ column, reducedSymbol (matrix.updateCol column first)
      (normalized_updateCol matrix normalized first firstNormalized column)) =
      ∑ column, reducedSymbol (matrix.updateCol column second)
        (normalized_updateCol matrix normalized second secondNormalized column) := by
  calc
    _ = ∑ firstColumn, ∑ secondColumn,
        reducedSymbol ((matrix.updateCol firstColumn first).updateCol secondColumn second)
          (normalized_updateCol _
            (normalized_updateCol matrix normalized first firstNormalized firstColumn)
            second secondNormalized secondColumn) :=
      Finset.sum_congr rfl (fun column _membership => subdivisions column)
    _ = ∑ column, reducedSymbol ((matrix.updateCol column first).updateCol column second)
        (normalized_updateCol _
          (normalized_updateCol matrix normalized first firstNormalized column)
          second secondNormalized column) := sum_antisymmetric_off_diagonal _ alternating
    _ = _ := Finset.sum_congr rfl (fun column _membership =>
      reducedSymbol_eq_of_matrix_eq _ _ _ _ (double_replacement_same matrix first second column))

theorem strict_subdivision_of_below (bound : ℕ) (below : SubdivisionBelow bound)
    (alternating : AlternatingBelow bound) (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (nonzero : matrix.det ≠ 0)
    (determinant : matrix.det.natAbs = bound) (notUnimodular : bound ≠ 1)
    (vector : Fin 3 → ℤ) (vectorNormalized : (vector 2 : ZMod 3) = 1)
    (replacementBounds : ∀ column, (matrix.updateCol column vector).det.natAbs < bound) :
    ReducedSubdivision matrix normalized vector vectorNormalized := by
  have notUnimodular' : matrix.det.natAbs ≠ 1 := by omega
  let reducing := reducingVector matrix nonzero normalized notUnimodular'
  have reducingNormalized : (reducing 2 : ZMod 3) = 1 :=
    reducingVector_normalized matrix nonzero normalized notUnimodular'
  have reducingBalanced : BalancedCoordinates (inverseCoordinates matrix nonzero reducing) :=
    reducingVector_balanced matrix nonzero normalized notUnimodular'
  have reducingBounds (column : Fin 3) : (matrix.updateCol column reducing).det.natAbs < bound := by
    rw [← determinant]
    exact reducing_vector_determinant matrix nonzero reducing reducingBalanced.1 column
  have vectorBounds (column : Fin 3) : |inverseCoordinates matrix nonzero vector column| < 1 := by
    have comparison := replacementBounds column
    rw [← determinant] at comparison
    have castComparison : |((matrix.updateCol column vector).det : ℚ)| < |(matrix.det : ℚ)| := by
      exact_mod_cast (show |(matrix.updateCol column vector).det| < |matrix.det| by
        rw [← Int.natCast_natAbs, ← Int.natCast_natAbs]
        exact_mod_cast comparison)
    rw [determinant_updateCol matrix nonzero vector column, abs_mul] at castComparison
    have positive : 0 < |(matrix.det : ℚ)| := abs_pos.mpr (Int.cast_ne_zero.mpr nonzero)
    nlinarith [abs_nonneg (inverseCoordinates matrix nonzero vector column)]
  have mixedBounds (firstColumn secondColumn : Fin 3) :
      ((matrix.updateCol firstColumn vector).updateCol secondColumn reducing).det.natAbs < bound := by
    by_cases equality : firstColumn = secondColumn
    · subst secondColumn
      rw [double_replacement_same]
      exact reducingBounds firstColumn
    · rw [double_replacement_commute matrix vector reducing firstColumn secondColumn equality,
        ← determinant]
      exact mixed_replacement_determinant_lt matrix nonzero reducing vector reducingBalanced
        vectorBounds secondColumn firstColumn (Ne.symm equality)
  have subdivisions (column : Fin 3) :
      ReducedSubdivision (matrix.updateCol column vector)
        (normalized_updateCol matrix normalized vector vectorNormalized column)
        reducing reducingNormalized :=
    below _ _ _ _ (replacementBounds column) (mixedBounds column)
  have offDiagonal (firstColumn secondColumn : Fin 3) (distinct : firstColumn ≠ secondColumn) :
      reducedSymbol ((matrix.updateCol firstColumn vector).updateCol secondColumn reducing)
        (normalized_updateCol _
          (normalized_updateCol matrix normalized vector vectorNormalized firstColumn)
          reducing reducingNormalized secondColumn) =
        -reducedSymbol ((matrix.updateCol secondColumn vector).updateCol firstColumn reducing)
          (normalized_updateCol _
            (normalized_updateCol matrix normalized vector vectorNormalized secondColumn)
            reducing reducingNormalized firstColumn) :=
    (reducedSymbol_eq_of_matrix_eq _ _ _ _
      (double_replacement_swap matrix firstColumn secondColumn distinct vector reducing)).trans
        (alternating _ _ firstColumn secondColumn distinct (mixedBounds secondColumn firstColumn))
  unfold ReducedSubdivision
  exact (reducedSymbol_reduction matrix nonzero normalized notUnimodular').trans
    (subdivision_sum_comparison matrix normalized vector reducing vectorNormalized reducingNormalized
      subdivisions offDiagonal).symm

theorem alternating_at_of_below (bound : ℕ) (below : SubdivisionBelow bound)
    (alternating : AlternatingBelow bound) (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (determinant : matrix.det.natAbs = bound)
    (first second : Fin 3) (distinct : first ≠ second) :
    reducedSymbol (swapColumns matrix first second)
      (swapColumns_normalized matrix normalized first second) = -reducedSymbol matrix normalized := by
  by_cases small : bound ≤ 1
  · apply alternatingBelow_two matrix normalized first second distinct
    omega
  · have nonzero : matrix.det ≠ 0 := by
      intro zero
      simp only [zero, Int.natAbs_zero] at determinant
      omega
    have notUnimodular : matrix.det.natAbs ≠ 1 := by omega
    let reducing := reducingVector matrix nonzero normalized notUnimodular
    have reducingNormalized : (reducing 2 : ZMod 3) = 1 :=
      reducingVector_normalized matrix nonzero normalized notUnimodular
    have reducingBounds (column : Fin 3) : (matrix.updateCol column reducing).det.natAbs < bound := by
      rw [← determinant]
      exact reducing_vector_determinant matrix nonzero reducing
        (reducingVector_balanced matrix nonzero normalized notUnimodular).1 column
    have swappedDeterminant : (swapColumns matrix first second).det.natAbs = bound := by
      rw [swapColumns_det matrix first second distinct, Int.natAbs_neg, determinant]
    have swappedNonzero : (swapColumns matrix first second).det ≠ 0 := by
      rw [swapColumns_det matrix first second distinct]
      exact neg_ne_zero.mpr nonzero
    have swappedBounds (column : Fin 3) :
        ((swapColumns matrix first second).updateCol column reducing).det.natAbs < bound := by
      rw [swapColumns_updateCol, swapColumns_det _ first second distinct, Int.natAbs_neg]
      exact reducingBounds _
    have subdivision := strict_subdivision_of_below bound below alternating
      (swapColumns matrix first second) (swapColumns_normalized matrix normalized first second)
      swappedNonzero swappedDeterminant (by omega) reducing reducingNormalized swappedBounds
    unfold ReducedSubdivision at subdivision
    rw [subdivision, reducedSymbol_reduction matrix nonzero normalized notUnimodular,
      ← Finset.sum_neg_distrib]
    have entry (column : Fin 3) :
        reducedSymbol ((swapColumns matrix first second).updateCol column reducing)
          (normalized_updateCol _ (swapColumns_normalized matrix normalized first second)
            reducing reducingNormalized column) =
          -reducedSymbol (matrix.updateCol (Equiv.swap first second column) reducing)
            (normalized_updateCol matrix normalized reducing reducingNormalized
              (Equiv.swap first second column)) :=
      (reducedSymbol_eq_of_matrix_eq _ _ _ _ (swapColumns_updateCol matrix first second column reducing)).trans
        (alternating _ _ first second distinct (reducingBounds _))
    simp_rw [entry]
    exact Equiv.sum_comp (Equiv.swap first second)
      (fun column : Fin 3 => -reducedSymbol (matrix.updateCol column reducing)
        (normalized_updateCol matrix normalized reducing reducingNormalized column))

theorem alternatingBelow_succ (bound : ℕ) (below : SubdivisionBelow bound)
    (alternating : AlternatingBelow bound) : AlternatingBelow (bound + 1) := by
  intro matrix normalized first second distinct comparison
  by_cases strict : matrix.det.natAbs < bound
  · exact alternating matrix normalized first second distinct strict
  · exact alternating_at_of_below bound below alternating matrix normalized (by omega)
      first second distinct

theorem replacement_coordinate_bound (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (vector : Fin 3 → ℤ) (column : Fin 3)
    (bound : (matrix.updateCol column vector).det.natAbs ≤ matrix.det.natAbs) :
    |inverseCoordinates matrix nonzero vector column| ≤ 1 := by
  have comparison : |((matrix.updateCol column vector).det : ℚ)| ≤ |(matrix.det : ℚ)| := by
    exact_mod_cast (show |(matrix.updateCol column vector).det| ≤ |matrix.det| by
      rw [← Int.natCast_natAbs, ← Int.natCast_natAbs]
      exact_mod_cast bound)
  rw [determinant_updateCol matrix nonzero vector column, abs_mul] at comparison
  have positive : 0 < |(matrix.det : ℚ)| := abs_pos.mpr (Int.cast_ne_zero.mpr nonzero)
  nlinarith [abs_nonneg (inverseCoordinates matrix nonzero vector column)]

theorem replacement_coordinate_eq_one (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (vector : Fin 3 → ℤ) (column : Fin 3) :
    |inverseCoordinates matrix nonzero vector column| = 1 ↔
      (matrix.updateCol column vector).det.natAbs = matrix.det.natAbs := by
  have determinant := congrArg abs (determinant_updateCol matrix nonzero vector column)
  rw [abs_mul] at determinant
  have positive : 0 < |(matrix.det : ℚ)| := abs_pos.mpr (Int.cast_ne_zero.mpr nonzero)
  have castAbs (integer : ℤ) : (integer.natAbs : ℚ) = |(integer : ℚ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  constructor
  · intro equality
    rw [equality, one_mul] at determinant
    rw [← castAbs, ← castAbs] at determinant
    exact_mod_cast determinant
  · intro equality
    have equality' : |((matrix.updateCol column vector).det : ℚ)| = |(matrix.det : ℚ)| := by
      rw [← castAbs, ← castAbs, equality]
    rw [equality'] at determinant
    nlinarith

def boundaryColumns (matrix : Matrix (Fin 3) (Fin 3) ℤ) (vector : Fin 3 → ℤ) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun column => (matrix.updateCol column vector).det.natAbs = matrix.det.natAbs)

theorem boundaryColumns_mem (matrix : Matrix (Fin 3) (Fin 3) ℤ) (vector : Fin 3 → ℤ)
    (column : Fin 3) : column ∈ boundaryColumns matrix vector ↔
      (matrix.updateCol column vector).det.natAbs = matrix.det.natAbs := by
  classical
  simp only [boundaryColumns, Finset.mem_filter, Finset.mem_univ, true_and]

theorem subdivision_at_of_below (bound : ℕ) (below : SubdivisionBelow bound)
    (alternating : AlternatingBelow bound) (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (determinant : matrix.det.natAbs = bound)
    (_nonzero : bound ≠ 0) (vector : Fin 3 → ℤ) (vectorNormalized : (vector 2 : ZMod 3) = 1)
    (replacementBounds : ∀ column, (matrix.updateCol column vector).det.natAbs ≤ bound) :
    ReducedSubdivision matrix normalized vector vectorNormalized := by
  classical
  by_cases small : bound ≤ 1
  · apply subdivisionBelow_two matrix normalized vector vectorNormalized
    · omega
    · intro column
      have comparison := replacementBounds column
      omega
  · have alternation := alternatingBelow_succ bound below alternating
    suffices result : ∀ count, ∀ (candidate : Matrix (Fin 3) (Fin 3) ℤ)
        (candidateNormalized : normalizedIntegralMatrix candidate)
        (inserted : Fin 3 → ℤ) (insertedNormalized : (inserted 2 : ZMod 3) = 1),
        candidate.det.natAbs = bound →
        (∀ column, (candidate.updateCol column inserted).det.natAbs ≤ bound) →
        (boundaryColumns candidate inserted).card = count →
        ReducedSubdivision candidate candidateNormalized inserted insertedNormalized by
      exact result _ matrix normalized vector vectorNormalized determinant replacementBounds rfl
    intro count
    induction count using Nat.strong_induction_on with
    | h count induction =>
      intro candidate candidateNormalized inserted insertedNormalized candidateDeterminant
        insertedBounds countEquality
      have candidateNonzero : candidate.det ≠ 0 := by
        intro zero
        simp only [zero, Int.natAbs_zero] at candidateDeterminant
        omega
      have notUnimodular : candidate.det.natAbs ≠ 1 := by omega
      let reducing := reducingVector candidate candidateNonzero candidateNormalized notUnimodular
      have reducingNormalized : (reducing 2 : ZMod 3) = 1 :=
        reducingVector_normalized candidate candidateNonzero candidateNormalized notUnimodular
      have reducingBalanced : BalancedCoordinates (inverseCoordinates candidate candidateNonzero reducing) :=
        reducingVector_balanced candidate candidateNonzero candidateNormalized notUnimodular
      have reducingBounds (column : Fin 3) : (candidate.updateCol column reducing).det.natAbs < bound := by
        rw [← candidateDeterminant]
        exact reducing_vector_determinant candidate candidateNonzero reducing reducingBalanced.1 column
      have coordinateBounds (column : Fin 3) : |inverseCoordinates candidate candidateNonzero inserted column| ≤ 1 :=
        replacement_coordinate_bound candidate candidateNonzero inserted column
          (by rw [candidateDeterminant]; exact insertedBounds column)
      have mixedBounds (firstColumn secondColumn : Fin 3) :
          ((candidate.updateCol firstColumn inserted).updateCol secondColumn reducing).det.natAbs ≤ bound := by
        by_cases equality : firstColumn = secondColumn
        · subst secondColumn
          rw [double_replacement_same]
          exact (reducingBounds firstColumn).le
        · rw [double_replacement_commute candidate inserted reducing firstColumn secondColumn equality,
            ← candidateDeterminant]
          exact mixed_replacement_determinant_le candidate candidateNonzero reducing inserted
            reducingBalanced coordinateBounds secondColumn firstColumn (Ne.symm equality)
      have mixedBoundary (firstColumn secondColumn : Fin 3)
          (equality : ((candidate.updateCol firstColumn inserted).updateCol secondColumn reducing).det.natAbs = bound) :
          firstColumn ∈ boundaryColumns candidate inserted ∧
            secondColumn ∈ boundaryColumns candidate inserted ∧ firstColumn ≠ secondColumn := by
        have distinct : firstColumn ≠ secondColumn := by
          intro equal
          subst secondColumn
          rw [double_replacement_same] at equality
          have comparison := reducingBounds firstColumn
          omega
        have determinantIdentity := congrArg abs (determinant_updateCol_updateCol candidate candidateNonzero
          reducing inserted secondColumn firstColumn (Ne.symm distinct))
        rw [abs_mul] at determinantIdentity
        have castEquality : |(((candidate.updateCol secondColumn reducing).updateCol firstColumn inserted).det : ℚ)| =
            |(candidate.det : ℚ)| := by
          rw [← double_replacement_commute candidate inserted reducing firstColumn secondColumn distinct]
          have castAbs (integer : ℤ) : (integer.natAbs : ℚ) = |(integer : ℚ)| := by
            rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
          rw [← castAbs, ← castAbs, equality, candidateDeterminant]
        rw [castEquality] at determinantIdentity
        have positive : 0 < |(candidate.det : ℚ)| := abs_pos.mpr (Int.cast_ne_zero.mpr candidateNonzero)
        have mixingEquality :
            |inverseCoordinates candidate candidateNonzero reducing secondColumn *
                inverseCoordinates candidate candidateNonzero inserted firstColumn -
              inverseCoordinates candidate candidateNonzero reducing firstColumn *
                inverseCoordinates candidate candidateNonzero inserted secondColumn| = 1 := by
          nlinarith
        have boundaries := mixing_eq_one_coordinates _ _ _ _
          (reducingBalanced.1 secondColumn) (reducingBalanced.1 firstColumn)
          (reducingBalanced.2 secondColumn firstColumn (Ne.symm distinct))
          (coordinateBounds secondColumn) (coordinateBounds firstColumn) mixingEquality
        exact ⟨(boundaryColumns_mem _ _ _).mpr
          ((replacement_coordinate_eq_one _ _ _ _).mp boundaries.2),
          (boundaryColumns_mem _ _ _).mpr
          ((replacement_coordinate_eq_one _ _ _ _).mp boundaries.1), distinct⟩
      have subdivisions (column : Fin 3) :
          ReducedSubdivision (candidate.updateCol column inserted)
            (normalized_updateCol candidate candidateNormalized inserted insertedNormalized column)
            reducing reducingNormalized := by
        by_cases columnBoundary : column ∈ boundaryColumns candidate inserted
        · have newDeterminant : (candidate.updateCol column inserted).det.natAbs = bound := by
            rw [(boundaryColumns_mem _ _ _).mp columnBoundary, candidateDeterminant]
          have strictSubset : boundaryColumns (candidate.updateCol column inserted) reducing ⊂
              boundaryColumns candidate inserted := by
            apply Finset.ssubset_iff_subset_ne.mpr
            constructor
            · intro other membership
              have equality := (boundaryColumns_mem _ _ _).mp membership
              rw [newDeterminant] at equality
              exact (mixedBoundary column other equality).2.1
            · intro equality
              have membership : column ∈ boundaryColumns (candidate.updateCol column inserted) reducing :=
                equality ▸ columnBoundary
              have determinantEquality := (boundaryColumns_mem _ _ _).mp membership
              rw [double_replacement_same, newDeterminant] at determinantEquality
              have comparison := reducingBounds column
              omega
          have cardinality := Finset.card_lt_card strictSubset
          rw [countEquality] at cardinality
          exact induction _ cardinality _ _ _ _ newDeterminant (mixedBounds column) rfl
        · apply below _ _ _ _
          · have different := (boundaryColumns_mem _ _ _).not.mp columnBoundary
            have comparison := insertedBounds column
            omega
          · intro other
            have comparison := mixedBounds column other
            by_contra notStrict
            have equality : ((candidate.updateCol column inserted).updateCol other reducing).det.natAbs = bound := by omega
            exact columnBoundary (mixedBoundary column other equality).1
      have offDiagonal (firstColumn secondColumn : Fin 3) (distinct : firstColumn ≠ secondColumn) :
          reducedSymbol ((candidate.updateCol firstColumn inserted).updateCol secondColumn reducing)
            (normalized_updateCol _
              (normalized_updateCol candidate candidateNormalized inserted insertedNormalized firstColumn)
              reducing reducingNormalized secondColumn) =
            -reducedSymbol ((candidate.updateCol secondColumn inserted).updateCol firstColumn reducing)
              (normalized_updateCol _
                (normalized_updateCol candidate candidateNormalized inserted insertedNormalized secondColumn)
                reducing reducingNormalized firstColumn) :=
        (reducedSymbol_eq_of_matrix_eq _ _ _ _
          (double_replacement_swap candidate firstColumn secondColumn distinct inserted reducing)).trans
            (alternation _ _ firstColumn secondColumn distinct (by
              have comparison := mixedBounds secondColumn firstColumn
              omega))
      unfold ReducedSubdivision
      exact (reducedSymbol_reduction candidate candidateNonzero candidateNormalized notUnimodular).trans
        (subdivision_sum_comparison candidate candidateNormalized inserted reducing insertedNormalized
          reducingNormalized subdivisions offDiagonal).symm

theorem subdivisionBelow_zero : SubdivisionBelow 0 := by
  intro matrix _normalized _vector _vectorNormalized comparison _bounds
  omega

theorem alternatingBelow_zero : AlternatingBelow 0 := by
  intro matrix _normalized _first _second _distinct comparison
  omega

theorem subdivisionBelow_succ (bound : ℕ) (below : SubdivisionBelow bound)
    (alternating : AlternatingBelow bound) : SubdivisionBelow (bound + 1) := by
  classical
  intro matrix normalized vector vectorNormalized determinantBound replacementBounds
  by_cases zeroBound : bound = 0
  · have zero : matrix.det = 0 := by
      have absZero : matrix.det.natAbs = 0 := by omega
      exact Int.natAbs_eq_zero.mp absZero
    unfold ReducedSubdivision
    rw [reducedSymbol_zero matrix normalized zero]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro column _membership
    apply reducedSymbol_zero
    apply Int.natAbs_eq_zero.mp
    have comparison := replacementBounds column
    omega
  · by_cases determinant : matrix.det.natAbs = bound
    · exact subdivision_at_of_below bound below alternating matrix normalized determinant zeroBound
        vector vectorNormalized (fun column => by have comparison := replacementBounds column; omega)
    · have strict : matrix.det.natAbs < bound := by omega
      by_cases allStrict : ∀ column, (matrix.updateCol column vector).det.natAbs < bound
      · exact below matrix normalized vector vectorNormalized strict allStrict
      · obtain ⟨pivot, notStrict⟩ := not_forall.mp allStrict
        have pivotDeterminant : (matrix.updateCol pivot vector).det.natAbs = bound := by
          have comparison := replacementBounds pivot
          omega
        have alternation := alternatingBelow_succ bound below alternating
        apply (reducedSubdivision_rebase matrix normalized vector vectorNormalized pivot
          (fun column distinct => alternation _ _ pivot column distinct (replacementBounds column))).mpr
        apply subdivision_at_of_below bound below alternating _ _ pivotDeterminant zeroBound
        intro column
        by_cases equality : column = pivot
        · subst column
          rw [replacement_rebase_same]
          exact strict.le
        · rw [replacement_rebase_other matrix vector pivot column (Ne.symm equality),
            swapColumns_det _ pivot column (Ne.symm equality), Int.natAbs_neg]
          have comparison := replacementBounds column
          omega

theorem subdivision_and_alternatingBelow (bound : ℕ) :
    SubdivisionBelow bound ∧ AlternatingBelow bound := by
  induction bound with
  | zero => exact ⟨subdivisionBelow_zero, alternatingBelow_zero⟩
  | succ bound induction =>
    exact ⟨subdivisionBelow_succ bound induction.1 induction.2,
      alternatingBelow_succ bound induction.1 induction.2⟩

theorem reducedSymbol_swap (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (first second : Fin 3)
    (distinct : first ≠ second) :
    reducedSymbol (swapColumns matrix first second)
      (swapColumns_normalized matrix normalized first second) = -reducedSymbol matrix normalized :=
  (subdivision_and_alternatingBelow (matrix.det.natAbs + 1)).2
    matrix normalized first second distinct (Nat.lt_succ_self _)

theorem reducedSymbol_subdivision (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (vector : Fin 3 → ℤ)
    (vectorNormalized : (vector 2 : ZMod 3) = 1) :
    ReducedSubdivision matrix normalized vector vectorNormalized := by
  apply (subdivision_and_alternatingBelow
    (matrix.det.natAbs + (∑ column, (matrix.updateCol column vector).det.natAbs) + 1)).1
  · omega
  · intro column
    have comparison : (matrix.updateCol column vector).det.natAbs ≤
        ∑ index, (matrix.updateCol index vector).det.natAbs :=
      Finset.single_le_sum
        (f := fun index : Fin 3 => (matrix.updateCol index vector).det.natAbs)
        (fun _index _membership => Nat.zero_le _) (Finset.mem_univ column)
    omega

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.SubdivisionInduction
