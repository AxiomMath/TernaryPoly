module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.SmallInsertion

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry TernaryPeriodPolynomials.GoodApartmentFunctional.RationalApartments
open TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralBases TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralReduction

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.BalancedReduction

noncomputable section

def BalancedCoordinates (coordinates : Fin 3 → ℚ) : Prop :=
  (∀ column, |coordinates column| < 1) ∧
    ∀ first second, first ≠ second → |coordinates first| + |coordinates second| ≤ 1

def centeredRemainder (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (vector : Fin 3 → ℤ) : Fin 3 → ℤ :=
  vector - matrix *ᵥ
    (fun column => ⌊inverseCoordinates matrix nonzero vector column + (1 / 2 : ℚ)⌋)

theorem inverseCoordinates_centeredRemainder (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (vector : Fin 3 → ℤ) :
    inverseCoordinates matrix nonzero (centeredRemainder matrix nonzero vector) =
      fun column => inverseCoordinates matrix nonzero vector column -
        (⌊inverseCoordinates matrix nonzero vector column + (1 / 2 : ℚ)⌋ : ℚ) := by
  unfold inverseCoordinates centeredRemainder
  rw [map_sub, integerVectorMap_mulVec, Matrix.mulVec_sub,
    ← integralMatrixRationalFrame_val matrix nonzero, inverse_mulVec_mulVec]
  rfl

theorem centered_lattice_point (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (notUnimodular : matrix.det.natAbs ≠ 1) :
    ∃ vector : Fin 3 → ℤ,
      (∀ column, |inverseCoordinates matrix nonzero vector column| ≤ (1 / 2 : ℚ)) ∧
      ∃ column, inverseCoordinates matrix nonzero vector column ≠ 0 := by
  obtain ⟨vector, bounds, coordinate, coordinateNonzero⟩ :=
    fractional_lattice_point matrix nonzero notUnimodular
  refine ⟨centeredRemainder matrix nonzero vector, ?_, coordinate, ?_⟩
  · intro column
    rw [inverseCoordinates_centeredRemainder, abs_le]
    have lower := Int.floor_le (inverseCoordinates matrix nonzero vector column + (1 / 2 : ℚ))
    have upper := Int.lt_floor_add_one
      (inverseCoordinates matrix nonzero vector column + (1 / 2 : ℚ))
    constructor <;> linarith
  · rw [inverseCoordinates_centeredRemainder]
    intro zero
    have equality := sub_eq_zero.mp zero
    have nonnegative :
        0 ≤ ⌊inverseCoordinates matrix nonzero vector coordinate + (1 / 2 : ℚ)⌋ := by
      exact_mod_cast equality ▸ (bounds coordinate).1
    have lessOne :
        ⌊inverseCoordinates matrix nonzero vector coordinate + (1 / 2 : ℚ)⌋ < 1 := by
      exact_mod_cast equality ▸ (bounds coordinate).2
    have floorZero :
        ⌊inverseCoordinates matrix nonzero vector coordinate + (1 / 2 : ℚ)⌋ = 0 := by
      omega
    rw [floorZero, Int.cast_zero] at equality
    exact coordinateNonzero equality

theorem half_bounded_balanced (coordinates : Fin 3 → ℚ)
    (bounds : ∀ column, |coordinates column| ≤ (1 / 2 : ℚ)) :
    BalancedCoordinates coordinates := by
  constructor
  · intro column
    linarith [bounds column]
  · intro first second _distinct
    linarith [bounds first, bounds second]

theorem balanced_neg (coordinates : Fin 3 → ℚ) (balanced : BalancedCoordinates coordinates) :
    BalancedCoordinates (-coordinates) := by
  constructor
  · intro column
    simpa only [Pi.neg_apply, abs_neg] using balanced.1 column
  · intro first second distinct
    simpa only [Pi.neg_apply, abs_neg] using balanced.2 first second distinct

theorem balanced_corrected (coordinates : Fin 3 → ℚ) (coordinate : Fin 3)
    (bounds : ∀ column, |coordinates column| ≤ (1 / 2 : ℚ))
    (positive : 0 < coordinates coordinate)
    (maximal : ∀ column, |coordinates column| ≤ |coordinates coordinate|) :
    BalancedCoordinates (Pi.single coordinate 1 - coordinates) := by
  have maximum : |coordinates coordinate| = coordinates coordinate := abs_of_pos positive
  have distinguished : |1 - coordinates coordinate| = 1 - coordinates coordinate := by
    rw [abs_of_nonneg]
    linarith [bounds coordinate, maximum]
  have entry (column : Fin 3) :
      |((Pi.single coordinate 1 : Fin 3 → ℚ) - coordinates) column| =
        if column = coordinate then 1 - coordinates coordinate else |coordinates column| := by
    by_cases equality : column = coordinate
    · subst column
      simp only [Pi.sub_apply, Pi.single_eq_same, ite_true, distinguished]
    · simp only [Pi.sub_apply, Pi.single_eq_of_ne equality, zero_sub, abs_neg, ite_eq_right equality]
  constructor
  · intro column
    rw [entry]
    split_ifs
    · linarith
    · linarith [bounds column]
  · intro first second distinct
    rw [entry, entry]
    by_cases firstEquality : first = coordinate
    · subst first
      rw [ite_eq_left rfl, ite_eq_right (Ne.symm distinct)]
      linarith [maximal second, maximum]
    · rw [ite_eq_right firstEquality]
      by_cases secondEquality : second = coordinate
      · subst second
        rw [ite_eq_left rfl]
        linarith [maximal first, maximum]
      · rw [ite_eq_right secondEquality]
        linarith [bounds first, bounds second]

theorem balanced_reducing_vector (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (normalized : normalizedIntegralMatrix matrix)
    (notUnimodular : matrix.det.natAbs ≠ 1) :
    ∃ vector : Fin 3 → ℤ, (vector 2 : ZMod 3) = 1 ∧
      BalancedCoordinates (inverseCoordinates matrix nonzero vector) := by
  obtain ⟨vector, bounds, nonzeroCoordinate, coordinateNonzero⟩ :=
    centered_lattice_point matrix nonzero notUnimodular
  by_cases bad : (vector 2 : ZMod 3) = 0
  · obtain ⟨coordinate, _membership, maximal⟩ := Finset.exists_max_image
      (Finset.univ : Finset (Fin 3))
      (fun column => |inverseCoordinates matrix nonzero vector column|) (by simp)
    have maximalBound (column : Fin 3) :
        |inverseCoordinates matrix nonzero vector column| ≤
          |inverseCoordinates matrix nonzero vector coordinate| := maximal column (by simp)
    have coordinateNonzero' : inverseCoordinates matrix nonzero vector coordinate ≠ 0 := by
      intro zero
      have bound := maximalBound nonzeroCoordinate
      rw [zero, abs_zero] at bound
      exact coordinateNonzero (abs_nonpos_iff.mp bound)
    rcases lt_or_gt_of_ne coordinateNonzero' with negative | positive
    · refine ⟨matrix.col coordinate + vector, ?_, ?_⟩
      · change ((matrix 2 coordinate + vector 2 : ℤ) : ZMod 3) = 1
        rw [Int.cast_add, normalized coordinate, bad, add_zero]
      · rw [inverseCoordinates_add, inverseCoordinates_column]
        have corrected := balanced_corrected
          (-inverseCoordinates matrix nonzero vector) coordinate
          (by simpa only [Pi.neg_apply, abs_neg] using bounds)
          (by simpa only [Pi.neg_apply] using neg_pos.mpr negative)
          (by simpa only [Pi.neg_apply, abs_neg] using maximalBound)
        simpa only [sub_neg_eq_add] using corrected
    · refine ⟨matrix.col coordinate - vector, ?_, ?_⟩
      · change ((matrix 2 coordinate - vector 2 : ℤ) : ZMod 3) = 1
        rw [Int.cast_sub, normalized coordinate, bad, sub_zero]
      · rw [inverseCoordinates_sub, inverseCoordinates_column]
        exact balanced_corrected _ coordinate bounds positive maximalBound
  · have possibilities : (vector 2 : ZMod 3) = 1 ∨ (vector 2 : ZMod 3) = -1 := by
      have finiteFact : ∀ value : ZMod 3, value ≠ 0 → value = 1 ∨ value = -1 := by decide
      exact finiteFact _ bad
    rcases possibilities with positive | negative
    · exact ⟨vector, positive, half_bounded_balanced _ bounds⟩
    · refine ⟨-vector, ?_, ?_⟩
      · change ((-vector 2 : ℤ) : ZMod 3) = 1
        rw [Int.cast_neg, negative, neg_neg]
      · rw [inverseCoordinates_neg]
        exact balanced_neg _ (half_bounded_balanced _ bounds)

theorem mixing_lt_one (first second third fourth : ℚ)
    (pairBound : |first| + |second| ≤ 1)
    (thirdBound : |third| < 1) (fourthBound : |fourth| < 1) :
    |first * fourth - second * third| < 1 := by
  let bound := max |third| |fourth|
  have boundNonnegative : 0 ≤ bound :=
    le_trans (abs_nonneg third) (le_max_left _ _)
  calc
    |first * fourth - second * third| ≤ |first * fourth| + |second * third| := abs_sub _ _
    _ = |first| * |fourth| + |second| * |third| := by rw [abs_mul, abs_mul]
    _ ≤ |first| * bound + |second| * bound :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg first))
        (mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg second))
    _ = (|first| + |second|) * bound := by ring
    _ ≤ 1 * bound := mul_le_mul_of_nonneg_right pairBound boundNonnegative
    _ = bound := one_mul _
    _ < 1 := max_lt thirdBound fourthBound

theorem mixing_le_one (first second third fourth : ℚ)
    (pairBound : |first| + |second| ≤ 1)
    (thirdBound : |third| ≤ 1) (fourthBound : |fourth| ≤ 1) :
    |first * fourth - second * third| ≤ 1 := by
  calc
    |first * fourth - second * third| ≤ |first * fourth| + |second * third| := abs_sub _ _
    _ = |first| * |fourth| + |second| * |third| := by rw [abs_mul, abs_mul]
    _ ≤ |first| * 1 + |second| * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left fourthBound (abs_nonneg first))
        (mul_le_mul_of_nonneg_left thirdBound (abs_nonneg second))
    _ = |first| + |second| := by ring
    _ ≤ 1 := pairBound

theorem mixing_lt_one_of_one_strict (first second third fourth : ℚ)
    (firstBound : |first| < 1) (pairBound : |first| + |second| ≤ 1)
    (thirdBound : |third| < 1) (fourthBound : |fourth| ≤ 1) :
    |first * fourth - second * third| < 1 := by
  have triangle : |first * fourth - second * third| ≤
      |first| * |fourth| + |second| * |third| := by
    simpa only [abs_mul] using abs_sub (first * fourth) (second * third)
  have firstTerm : |first| * |fourth| ≤ |first| := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left fourthBound (abs_nonneg first)
  by_cases secondZero : second = 0
  · subst second
    simp only [abs_zero, zero_mul, add_zero] at triangle ⊢
    linarith
  · have secondTerm : |second| * |third| < |second| := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left thirdBound (abs_pos.mpr secondZero)
    linarith

theorem mixing_eq_one_coordinates (first second third fourth : ℚ)
    (firstBound : |first| < 1) (secondBound : |second| < 1)
    (pairBound : |first| + |second| ≤ 1)
    (thirdBound : |third| ≤ 1) (fourthBound : |fourth| ≤ 1)
    (equality : |first * fourth - second * third| = 1) :
    |third| = 1 ∧ |fourth| = 1 := by
  constructor
  · by_contra different
    have strict := mixing_lt_one_of_one_strict first second third fourth firstBound pairBound
      (lt_of_le_of_ne thirdBound different) fourthBound
    linarith
  · by_contra different
    have strict := mixing_lt_one_of_one_strict second first fourth third secondBound
      (by simpa only [add_comm] using pairBound)
      (lt_of_le_of_ne fourthBound different) thirdBound
    rw [abs_sub_comm] at strict
    linarith

theorem determinant_updateCol_updateCol (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (first second : Fin 3 → ℤ)
    (firstColumn secondColumn : Fin 3) (distinct : firstColumn ≠ secondColumn) :
    (((matrix.updateCol firstColumn first).updateCol secondColumn second).det : ℚ) =
      (inverseCoordinates matrix nonzero first firstColumn *
          inverseCoordinates matrix nonzero second secondColumn -
        inverseCoordinates matrix nonzero first secondColumn *
          inverseCoordinates matrix nonzero second firstColumn) * (matrix.det : ℚ) := by
  let firstCoordinates := inverseCoordinates matrix nonzero first
  let secondCoordinates := inverseCoordinates matrix nonzero second
  have firstReconstruct : integerVectorMap first = rationalMatrix matrix *ᵥ firstCoordinates :=
    (inverseCoordinates_reconstruct matrix nonzero first).symm
  have secondReconstruct : integerVectorMap second = rationalMatrix matrix *ᵥ secondCoordinates :=
    (inverseCoordinates_reconstruct matrix nonzero second).symm
  rw [← rationalMatrix_det, rationalMatrix, Matrix.map_updateCol, Matrix.map_updateCol]
  change (((rationalMatrix matrix).updateCol firstColumn (integerVectorMap first)).updateCol
    secondColumn (integerVectorMap second)).det = _
  rw [firstReconstruct, secondReconstruct, ← rationalMatrix_det]
  change (((rationalMatrix matrix).updateCol firstColumn
    (rationalMatrix matrix *ᵥ firstCoordinates)).updateCol secondColumn
    (rationalMatrix matrix *ᵥ secondCoordinates)).det =
      (firstCoordinates firstColumn * secondCoordinates secondColumn -
        firstCoordinates secondColumn * secondCoordinates firstColumn) * (rationalMatrix matrix).det
  fin_cases firstColumn <;> fin_cases secondColumn <;>
    simp only [ne_eq, not_true_eq_false] at distinct
  all_goals simp [Matrix.det_fin_three, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three]
  all_goals ring

theorem mixed_replacement_determinant_lt (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (first second : Fin 3 → ℤ)
    (balanced : BalancedCoordinates (inverseCoordinates matrix nonzero first))
    (bounds : ∀ column, |inverseCoordinates matrix nonzero second column| < 1)
    (firstColumn secondColumn : Fin 3) (distinct : firstColumn ≠ secondColumn) :
    ((matrix.updateCol firstColumn first).updateCol secondColumn second).det.natAbs <
      matrix.det.natAbs := by
  have determinant := congrArg abs
    (determinant_updateCol_updateCol matrix nonzero first second firstColumn secondColumn distinct)
  rw [abs_mul] at determinant
  have bound := mixing_lt_one
    (inverseCoordinates matrix nonzero first firstColumn)
    (inverseCoordinates matrix nonzero first secondColumn)
    (inverseCoordinates matrix nonzero second firstColumn)
    (inverseCoordinates matrix nonzero second secondColumn)
    (balanced.2 firstColumn secondColumn distinct) (bounds firstColumn) (bounds secondColumn)
  have strict := mul_lt_mul_of_pos_right bound
    (abs_pos.mpr (Int.cast_ne_zero.mpr nonzero) : 0 < |(matrix.det : ℚ)|)
  rw [one_mul, ← determinant] at strict
  have castAbs (integer : ℤ) : (integer.natAbs : ℚ) = |(integer : ℚ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [← castAbs, ← castAbs] at strict
  exact_mod_cast strict

def balancedCandidates (matrix : Matrix (Fin 3) (Fin 3) ℤ) : Set (Fin 3 → ℤ) :=
  {vector | (vector 2 : ZMod 3) = 1 ∧
    ∃ nonzero : matrix.det ≠ 0, BalancedCoordinates (inverseCoordinates matrix nonzero vector)}

theorem balancedCandidates_nonempty (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (normalized : normalizedIntegralMatrix matrix)
    (notUnimodular : matrix.det.natAbs ≠ 1) : (balancedCandidates matrix).Nonempty := by
  obtain ⟨vector, vectorNormalized, balanced⟩ :=
    balanced_reducing_vector matrix nonzero normalized notUnimodular
  exact ⟨vector, vectorNormalized, nonzero, balanced⟩

def reducingVector (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (normalized : normalizedIntegralMatrix matrix)
    (notUnimodular : matrix.det.natAbs ≠ 1) : Fin 3 → ℤ :=
  (balancedCandidates_nonempty matrix nonzero normalized notUnimodular).some

theorem reducingVector_normalized (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (normalized : normalizedIntegralMatrix matrix)
    (notUnimodular : matrix.det.natAbs ≠ 1) :
    ((reducingVector matrix nonzero normalized notUnimodular) 2 : ZMod 3) = 1 :=
  (balancedCandidates_nonempty matrix nonzero normalized notUnimodular).some_mem.1

theorem reducingVector_balanced (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (normalized : normalizedIntegralMatrix matrix)
    (notUnimodular : matrix.det.natAbs ≠ 1) :
    BalancedCoordinates
      (inverseCoordinates matrix nonzero (reducingVector matrix nonzero normalized notUnimodular)) :=
  (balancedCandidates_nonempty matrix nonzero normalized notUnimodular).some_mem.2.choose_spec

def reducedSymbol (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) : TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralSymbols.SymbolSpace :=
  if nonzero : matrix.det ≠ 0 then
    if unimodular : matrix.det.natAbs = 1 then
      TernaryPeriodPolynomials.GoodApartmentFunctional.SmallInsertion.matrixSymbol matrix normalized
    else
      let vector := reducingVector matrix nonzero normalized unimodular
      let vectorNormalized := reducingVector_normalized matrix nonzero normalized unimodular
      ∑ column, reducedSymbol (matrix.updateCol column vector)
        (normalized_updateCol matrix normalized vector vectorNormalized column)
  else 0
termination_by matrix.det.natAbs
decreasing_by
  exact reducing_vector_determinant matrix nonzero _
    (reducingVector_balanced matrix nonzero normalized unimodular).1 column

theorem reducedSymbol_zero (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (zero : matrix.det = 0) :
    reducedSymbol matrix normalized = 0 := by
  rw [reducedSymbol, dite_eq_right (by simp only [zero, ne_eq, not_true_eq_false, not_false_eq_true])]

theorem reducedSymbol_unimodular (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (unimodular : matrix.det.natAbs = 1) :
    reducedSymbol matrix normalized = TernaryPeriodPolynomials.GoodApartmentFunctional.SmallInsertion.matrixSymbol matrix normalized := by
  have nonzero : matrix.det ≠ 0 := by
    intro zero
    simp only [zero, Int.natAbs_zero, Nat.zero_ne_one] at unimodular
  rw [reducedSymbol, dite_eq_left nonzero, dite_eq_left unimodular]

theorem reducedSymbol_frame (frame : NormalizedFrames) :
    reducedSymbol frame.val.val frame.property = TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralSymbols.frameSymbol frame := by
  exact (reducedSymbol_unimodular frame.val.val frame.property
    (Int.isUnit_iff_natAbs_eq.mp (Matrix.isUnits_det_units frame.val))).trans
    (TernaryPeriodPolynomials.GoodApartmentFunctional.SmallInsertion.matrixSymbol_of_frame frame frame.property)

theorem reducedSymbol_reduction (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (normalized : normalizedIntegralMatrix matrix)
    (notUnimodular : matrix.det.natAbs ≠ 1) :
    reducedSymbol matrix normalized =
      ∑ column, reducedSymbol
        (matrix.updateCol column (reducingVector matrix nonzero normalized notUnimodular))
        (normalized_updateCol matrix normalized _
          (reducingVector_normalized matrix nonzero normalized notUnimodular) column) := by
  rw [reducedSymbol, dite_eq_left nonzero, dite_eq_right notUnimodular]

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.BalancedReduction
