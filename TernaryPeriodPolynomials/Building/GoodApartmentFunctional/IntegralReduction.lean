module

public import TernaryPeriodPolynomials.Building.GoodApartmentFunctional.ApartmentGeneration
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section


open GeneralEisenstein
open Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.GoodApartmentFunctional.Helpers TernaryPeriodPolynomials.GoodApartmentFunctional.FlagGeometry TernaryPeriodPolynomials.GoodApartmentFunctional.Incidence
open TernaryPeriodPolynomials.GoodApartmentFunctional.RationalApartments TernaryPeriodPolynomials.GoodApartmentFunctional.ApartmentGeneration
open TernaryPeriodPolynomials.GoodApartmentFunctional.GenericLine
open TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralBases

namespace TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralReduction

noncomputable section

def rationalMatrix (matrix : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℚ :=
  matrix.map (Int.castRingHom ℚ)

theorem rationalMatrix_det (matrix : Matrix (Fin 3) (Fin 3) ℤ) :
    (rationalMatrix matrix).det = (matrix.det : ℚ) := by
  exact ((Int.castRingHom ℚ).map_det matrix).symm

def integralMatrixRationalFrame (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) : RationalGL3 :=
  GeneralLinearGroup.mkOfDetNeZero (rationalMatrix matrix)
    (by rwa [rationalMatrix_det, Int.cast_ne_zero])

theorem integralMatrixRationalFrame_val (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) :
    (integralMatrixRationalFrame matrix nonzero).val = rationalMatrix matrix := by
  exact GeneralLinearGroup.val_mkOfDetNeZero _ _

def normalizedIntegralMatrix (matrix : Matrix (Fin 3) (Fin 3) ℤ) : Prop :=
  ∀ column, (matrix 2 column : ZMod 3) = 1

theorem normalizedIntegralMatrix_good_columns (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (normalized : normalizedIntegralMatrix matrix) :
    ∀ column, GoodFlag .line (columnLine (integralMatrixRationalFrame matrix nonzero) column) := by
  intro column
  rw [goodFlag_iff]
  refine ⟨matrix.col column, ?_, ?_⟩
  · rw [columnLine_subspace, integralMatrixRationalFrame_val]
    exact Submodule.subset_span (by rfl)
  · change (matrix 2 column : ZMod 3) ≠ 0
    rw [normalized column]
    exact one_ne_zero

theorem normalizedIntegralMatrix_lastCoordinate (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (coordinates : Fin 3 → ℤ) :
    ((matrix *ᵥ coordinates) 2 : ZMod 3) = ∑ column, (coordinates column : ZMod 3) := by
  have lastRow : ∀ column, (matrix 2 column : ZMod 3) = 1 := normalized
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, lastRow, one_mul]

theorem determinant_one_normalizedFrame (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (normalized : normalizedIntegralMatrix matrix)
    (unimodular : matrix.det.natAbs = 1) :
    ∃ frame : NormalizedFrames,
      GeneralLinearGroup.map (Int.castRingHom ℚ) frame.val =
        integralMatrixRationalFrame matrix nonzero := by
  let integral : IntegralGL3 := GeneralLinearGroup.mk'' matrix
    (Int.isUnit_iff_natAbs_eq.mpr unimodular)
  have integralValue : integral.val = matrix := GeneralLinearGroup.val_mk'' _ _
  refine ⟨⟨integral, ?_⟩, ?_⟩
  · rw [integralValue]
    exact normalized
  · apply Units.ext
    change integral.val.map (Int.castRingHom ℚ) =
      (integralMatrixRationalFrame matrix nonzero).val
    rw [integralValue, integralMatrixRationalFrame_val]
    rfl

def inverseCoordinates (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (vector : Fin 3 → ℤ) : Fin 3 → ℚ :=
  (integralMatrixRationalFrame matrix nonzero)⁻¹.val *ᵥ integerVectorMap vector

theorem inverseCoordinates_reconstruct (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (vector : Fin 3 → ℤ) :
    rationalMatrix matrix *ᵥ inverseCoordinates matrix nonzero vector =
      integerVectorMap vector := by
  rw [← integralMatrixRationalFrame_val matrix nonzero]
  unfold inverseCoordinates
  rw [Matrix.mulVec_mulVec, ← GeneralLinearGroup.coe_mul, mul_inv_cancel,
    GeneralLinearGroup.coe_one, Matrix.one_mulVec]

theorem determinant_updateCol (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (vector : Fin 3 → ℤ) (column : Fin 3) :
    ((matrix.updateCol column vector).det : ℚ) =
      inverseCoordinates matrix nonzero vector column * (matrix.det : ℚ) := by
  rw [← rationalMatrix_det, rationalMatrix, Matrix.map_updateCol]
  change ((rationalMatrix matrix).updateCol column (integerVectorMap vector)).det = _
  rw [← inverseCoordinates_reconstruct matrix nonzero vector]
  have multiplication : rationalMatrix matrix *ᵥ inverseCoordinates matrix nonzero vector =
      fun row => ∑ index, inverseCoordinates matrix nonzero vector index •
        rationalMatrix matrix row index := by
    ext row
    simp only [Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm]
  rw [multiplication, Matrix.det_updateCol_sum, smul_eq_mul, rationalMatrix_det]

def fractionalRemainder (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (vector : Fin 3 → ℤ) : Fin 3 → ℤ :=
  vector - matrix *ᵥ (fun column => ⌊inverseCoordinates matrix nonzero vector column⌋)

theorem integerVectorMap_mulVec (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (vector : Fin 3 → ℤ) :
    integerVectorMap (matrix *ᵥ vector) = rationalMatrix matrix *ᵥ integerVectorMap vector := by
  ext row
  simp [integerVectorMap, rationalMatrix, Matrix.mulVec, dotProduct, Int.cast_sum]

theorem inverseCoordinates_fractionalRemainder (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (vector : Fin 3 → ℤ) :
    inverseCoordinates matrix nonzero (fractionalRemainder matrix nonzero vector) =
      fun column => Int.fract (inverseCoordinates matrix nonzero vector column) := by
  unfold inverseCoordinates fractionalRemainder
  rw [map_sub, integerVectorMap_mulVec, Matrix.mulVec_sub,
    ← integralMatrixRationalFrame_val matrix nonzero, inverse_mulVec_mulVec]
  rfl

theorem fractional_lattice_point (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (notUnimodular : matrix.det.natAbs ≠ 1) :
    ∃ vector : Fin 3 → ℤ,
      (∀ column, 0 ≤ inverseCoordinates matrix nonzero vector column ∧
        inverseCoordinates matrix nonzero vector column < 1) ∧
      ∃ column, inverseCoordinates matrix nonzero vector column ≠ 0 := by
  by_cases existsFraction : ∃ basisColumn coordinate : Fin 3,
      Int.fract (inverseCoordinates matrix nonzero (Pi.single basisColumn 1) coordinate) ≠ 0
  · obtain ⟨basisColumn, coordinate, fractionNonzero⟩ := existsFraction
    refine ⟨fractionalRemainder matrix nonzero (Pi.single basisColumn 1), ?_, ?_⟩
    · intro column
      rw [inverseCoordinates_fractionalRemainder]
      exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · exact ⟨coordinate, by rwa [inverseCoordinates_fractionalRemainder]⟩
  · have fractionsZero (basisColumn coordinate : Fin 3) :
        Int.fract (inverseCoordinates matrix nonzero (Pi.single basisColumn 1) coordinate) = 0 := by
      by_contra nonzeroFraction
      exact existsFraction ⟨basisColumn, coordinate, nonzeroFraction⟩
    let inverse : Matrix (Fin 3) (Fin 3) ℤ := fun row column =>
      ⌊inverseCoordinates matrix nonzero (Pi.single column 1) row⌋
    have coordinateEquality (basisColumn : Fin 3) :
        integerVectorMap (inverse.col basisColumn) =
          inverseCoordinates matrix nonzero (Pi.single basisColumn 1) := by
      ext coordinate
      have fraction := fractionsZero basisColumn coordinate
      change inverseCoordinates matrix nonzero (Pi.single basisColumn 1) coordinate -
        (⌊inverseCoordinates matrix nonzero (Pi.single basisColumn 1) coordinate⌋ : ℚ) = 0
        at fraction
      exact (sub_eq_zero.mp fraction).symm
    have rightInverse : matrix * inverse = 1 := by
      have rationalRightInverse : rationalMatrix matrix * rationalMatrix inverse = 1 := by
        ext row column
        have reconstruction := inverseCoordinates_reconstruct matrix nonzero (Pi.single column 1)
        rw [← coordinateEquality column, ← integerVectorMap_mulVec] at reconstruction
        have entry := congrFun reconstruction row
        simpa [rationalMatrix, integerVectorMap, Matrix.mul_apply, Matrix.mulVec,
          dotProduct, Matrix.col, Pi.single_apply, Matrix.one_apply] using entry
      ext row column
      apply (Int.cast_injective (α := ℚ))
      have entry := congrFun (congrFun rationalRightInverse row) column
      simpa [rationalMatrix, Matrix.mul_apply, Matrix.one_apply, Int.cast_sum] using entry
    exact (notUnimodular
      (Int.isUnit_iff_natAbs_eq.mp (Matrix.isUnit_det_of_right_inverse rightInverse))).elim

theorem inverseCoordinates_add (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (first second : Fin 3 → ℤ) :
    inverseCoordinates matrix nonzero (first + second) =
      inverseCoordinates matrix nonzero first + inverseCoordinates matrix nonzero second := by
  simp only [inverseCoordinates, map_add, Matrix.mulVec_add]

theorem inverseCoordinates_neg (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (vector : Fin 3 → ℤ) :
    inverseCoordinates matrix nonzero (-vector) = -inverseCoordinates matrix nonzero vector := by
  simp only [inverseCoordinates, map_neg, Matrix.mulVec_neg]

theorem inverseCoordinates_sub (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (first second : Fin 3 → ℤ) :
    inverseCoordinates matrix nonzero (first - second) =
      inverseCoordinates matrix nonzero first - inverseCoordinates matrix nonzero second := by
  simp only [inverseCoordinates, map_sub, Matrix.mulVec_sub]

theorem inverseCoordinates_column (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (column : Fin 3) :
    inverseCoordinates matrix nonzero (matrix.col column) = Pi.single column 1 := by
  unfold inverseCoordinates
  have columnEquality : integerVectorMap (matrix.col column) =
      (integralMatrixRationalFrame matrix nonzero).val *ᵥ Pi.single column 1 := by
    rw [Matrix.mulVec_single_one, integralMatrixRationalFrame_val]
    rfl
  rw [columnEquality, inverse_mulVec_mulVec]

theorem normalized_reducing_vector (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (normalized : normalizedIntegralMatrix matrix)
    (notUnimodular : matrix.det.natAbs ≠ 1) :
    ∃ vector : Fin 3 → ℤ, (vector 2 : ZMod 3) = 1 ∧
      ∀ column, |inverseCoordinates matrix nonzero vector column| < 1 := by
  obtain ⟨vector, bounds, coordinate, coordinateNonzero⟩ :=
    fractional_lattice_point matrix nonzero notUnimodular
  by_cases bad : (vector 2 : ZMod 3) = 0
  · refine ⟨matrix.col coordinate - vector, ?_, ?_⟩
    · change ((matrix 2 coordinate - vector 2 : ℤ) : ZMod 3) = 1
      rw [Int.cast_sub, normalized coordinate, bad, sub_zero]
    · intro column
      rw [inverseCoordinates_sub, inverseCoordinates_column]
      by_cases equality : coordinate = column
      · subst column
        rw [Pi.sub_apply, Pi.single_eq_same]
        have positive := lt_of_le_of_ne (bounds coordinate).1 (Ne.symm coordinateNonzero)
        rw [abs_of_nonneg (by linarith [(bounds coordinate).2])]
        linarith
      · rw [Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm equality), zero_sub, abs_neg,
          abs_of_nonneg (bounds column).1]
        exact (bounds column).2
  · have possibilities : (vector 2 : ZMod 3) = 1 ∨ (vector 2 : ZMod 3) = -1 := by
      have finiteFact : ∀ value : ZMod 3, value ≠ 0 → value = 1 ∨ value = -1 := by
        decide
      exact finiteFact _ bad
    rcases possibilities with normalizedVector | negativeVector
    · refine ⟨vector, normalizedVector, ?_⟩
      intro column
      rw [abs_of_nonneg (bounds column).1]
      exact (bounds column).2
    · refine ⟨-vector, ?_, ?_⟩
      · change ((-vector 2 : ℤ) : ZMod 3) = 1
        rw [Int.cast_neg, negativeVector, neg_neg]
      · intro column
        rw [inverseCoordinates_neg, Pi.neg_apply, abs_neg, abs_of_nonneg (bounds column).1]
        exact (bounds column).2

theorem normalized_updateCol (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (normalized : normalizedIntegralMatrix matrix) (vector : Fin 3 → ℤ)
    (normalizedVector : (vector 2 : ZMod 3) = 1) (column : Fin 3) :
    normalizedIntegralMatrix (matrix.updateCol column vector) := by
  intro candidate
  by_cases equality : candidate = column
  · subst candidate
    simpa using normalizedVector
  · simpa [Matrix.updateCol, equality] using normalized candidate

theorem reducing_vector_determinant (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (vector : Fin 3 → ℤ)
    (bounds : ∀ column, |inverseCoordinates matrix nonzero vector column| < 1)
    (column : Fin 3) :
    (matrix.updateCol column vector).det.natAbs < matrix.det.natAbs := by
  have determinantEquality := congrArg abs (determinant_updateCol matrix nonzero vector column)
  rw [abs_mul] at determinantEquality
  have positive : 0 < |(matrix.det : ℚ)| := abs_pos.mpr (Int.cast_ne_zero.mpr nonzero)
  have strict := mul_lt_mul_of_pos_right (bounds column) positive
  rw [one_mul, ← determinantEquality] at strict
  have castAbs (integer : ℤ) : (integer.natAbs : ℚ) = |(integer : ℚ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [← castAbs, ← castAbs] at strict
  exact_mod_cast strict

theorem normalizedVector_nonzero (vector : Fin 3 → ℤ)
    (normalized : (vector 2 : ZMod 3) = 1) : integerVectorMap vector ≠ 0 := by
  intro zero
  have coordinate : (vector 2 : ℚ) = 0 := congrFun zero 2
  have integralZero : vector 2 = 0 := Int.cast_eq_zero.mp coordinate
  rw [integralZero, Int.cast_zero] at normalized
  exact zero_ne_one normalized

def normalizedVectorLine (vector : Fin 3 → ℤ) (normalized : (vector 2 : ZMod 3) = 1) :
    Flags .line :=
  QuotientGroup.mk (vector_extends_rational_frame (integerVectorMap vector)
    (normalizedVector_nonzero vector normalized)).choose

theorem normalizedVectorLine_subspace (vector : Fin 3 → ℤ)
    (normalized : (vector 2 : ZMod 3) = 1) :
    flagSubspace .line (normalizedVectorLine vector normalized) =
      Submodule.span ℚ {integerVectorMap vector} := by
  rw [normalizedVectorLine, flagSubspace_mk, line_frame_subspace,
    (vector_extends_rational_frame (integerVectorMap vector)
      (normalizedVector_nonzero vector normalized)).choose_spec]

theorem normalizedVectorLine_good (vector : Fin 3 → ℤ)
    (normalized : (vector 2 : ZMod 3) = 1) :
    GoodFlag .line (normalizedVectorLine vector normalized) := by
  rw [goodFlag_iff, normalizedVectorLine_subspace]
  exact ⟨vector, Submodule.mem_span_singleton_self _, normalized ▸ one_ne_zero⟩

theorem updateCol_line (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (vector : Fin 3 → ℤ)
    (normalizedVector : (vector 2 : ZMod 3) = 1) (column candidate : Fin 3)
    (updateNonzero : (matrix.updateCol column vector).det ≠ 0) :
    columnLine (integralMatrixRationalFrame (matrix.updateCol column vector) updateNonzero)
      candidate = if candidate = column then normalizedVectorLine vector normalizedVector
        else columnLine (integralMatrixRationalFrame matrix nonzero) candidate := by
  apply flagSubspace_injective
  rw [columnLine_subspace, integralMatrixRationalFrame_val]
  by_cases equality : candidate = column
  · subst candidate
    rw [ite_eq_left rfl, normalizedVectorLine_subspace]
    have columnEquality : (rationalMatrix (matrix.updateCol column vector)).col column =
        integerVectorMap vector := by
      ext row
      change ((matrix.updateCol column vector) row column : ℚ) = (vector row : ℚ)
      simp
    rw [columnEquality]
  · rw [ite_eq_right equality, columnLine_subspace, integralMatrixRationalFrame_val]
    have columnEquality : (rationalMatrix (matrix.updateCol column vector)).col candidate =
        (rationalMatrix matrix).col candidate := by
      ext row
      change ((matrix.updateCol column vector) row candidate : ℚ) = (matrix row candidate : ℚ)
      simp [Matrix.updateCol, equality]
    rw [columnEquality]

theorem zero_coordinate_in_opposite_plane (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (vector : Fin 3 → ℤ) (column : Fin 3)
    (zero : inverseCoordinates matrix nonzero vector column = 0) :
    integerVectorMap vector ∈
      flagSubspace .plane (columnPlane (integralMatrixRationalFrame matrix nonzero) (column + 1)) := by
  rw [columnPlane_subspace]
  have reconstruction := inverseCoordinates_reconstruct matrix nonzero vector
  rw [← integralMatrixRationalFrame_val matrix nonzero] at reconstruction
  let frame := integralMatrixRationalFrame matrix nonzero
  have decomposition : integerVectorMap vector =
      inverseCoordinates matrix nonzero vector (column + 1) • frame.val.col (column + 1) +
      inverseCoordinates matrix nonzero vector (column + 1 + 1) •
        frame.val.col (column + 1 + 1) := by
    rw [← reconstruction]
    ext row
    fin_cases column <;> dsimp at zero <;>
      simp [frame, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.col,
        zero, mul_comm, add_comm]
  rw [decomposition]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [frame])))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [frame])))

def replacementTriangle (frame : GoodRationalFrames) (inserted : Flags .line)
    (insertedGood : GoodFlag .line inserted) (column : Fin 3) : EdgeChains :=
  lineTriangle
    (if column = 0 then inserted else columnLine frame.val 0)
    (if column = 1 then inserted else columnLine frame.val 1)
    (if column = 2 then inserted else columnLine frame.val 2)
    (by split <;> [exact insertedGood; exact frame.property 0])
    (by split <;> [exact insertedGood; exact frame.property 1])
    (by split <;> [exact insertedGood; exact frame.property 2])

theorem apartment_replacement_sum (frame : GoodRationalFrames) (inserted : Flags .line)
    (insertedGood : GoodFlag .line inserted) :
    apartment frame.val = ∑ column, replacementTriangle frame inserted insertedGood column := by
  rw [Fin.sum_univ_three, apartment_subdivision frame inserted insertedGood]
  simp only [replacementTriangle, ↓reduceIte, Fin.reduceEq]

theorem replacementTriangle_apartment (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (normalized : normalizedIntegralMatrix matrix)
    (vector : Fin 3 → ℤ) (normalizedVector : (vector 2 : ZMod 3) = 1) (column : Fin 3)
    (updateNonzero : (matrix.updateCol column vector).det ≠ 0) :
    replacementTriangle
      ⟨integralMatrixRationalFrame matrix nonzero,
        normalizedIntegralMatrix_good_columns matrix nonzero normalized⟩
      (normalizedVectorLine vector normalizedVector)
      (normalizedVectorLine_good vector normalizedVector) column =
        apartment (integralMatrixRationalFrame (matrix.updateCol column vector) updateNonzero) := by
  rw [apartment_as_lineConnectors _
    (normalizedIntegralMatrix_good_columns _ updateNonzero
      (normalized_updateCol matrix normalized vector normalizedVector column))]
  unfold replacementTriangle lineTriangle
  simp only [updateCol_line matrix nonzero vector normalizedVector column, eq_comm]

theorem replacementTriangle_zero (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (normalized : normalizedIntegralMatrix matrix)
    (vector : Fin 3 → ℤ) (normalizedVector : (vector 2 : ZMod 3) = 1) (column : Fin 3)
    (updateZero : (matrix.updateCol column vector).det = 0) :
    replacementTriangle
      ⟨integralMatrixRationalFrame matrix nonzero,
        normalizedIntegralMatrix_good_columns matrix nonzero normalized⟩
      (normalizedVectorLine vector normalizedVector)
      (normalizedVectorLine_good vector normalizedVector) column = 0 := by
  have zero : inverseCoordinates matrix nonzero vector column = 0 := by
    have equality := determinant_updateCol matrix nonzero vector column
    rw [updateZero, Int.cast_zero] at equality
    exact (mul_eq_zero.mp equality.symm).resolve_right (Int.cast_ne_zero.mpr nonzero)
  have insertedIncidence : flagSubspace .line (normalizedVectorLine vector normalizedVector) ≤
      flagSubspace .plane
        (columnPlane (integralMatrixRationalFrame matrix nonzero) (column + 1)) := by
    rw [normalizedVectorLine_subspace]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr
      (zero_coordinate_in_opposite_plane matrix nonzero vector column zero)
  have firstIncidence := columnLine_first_incidence (integralMatrixRationalFrame matrix nonzero)
    (column + 1)
  have secondIncidence := columnLine_second_incidence (integralMatrixRationalFrame matrix nonzero)
    (column + 1)
  unfold replacementTriangle
  fin_cases column
  · exact lineTriangle_coplanar _ _ _ _ _ _ _ insertedIncidence firstIncidence secondIncidence
  · exact lineTriangle_coplanar _ _ _ _ _ _ _ secondIncidence insertedIncidence firstIncidence
  · exact lineTriangle_coplanar _ _ _ _ _ _ _ firstIncidence secondIncidence insertedIncidence

def integralApartmentSpan : Submodule ℂ EdgeChains :=
  (goodCycles.subtype.comp apartmentPresentation).range

theorem integral_matrix_apartment_in_span (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (nonzero : matrix.det ≠ 0) (normalized : normalizedIntegralMatrix matrix) :
    apartment (integralMatrixRationalFrame matrix nonzero) ∈ integralApartmentSpan := by
  generalize sizeEquality : matrix.det.natAbs = size
  induction size using Nat.strong_induction_on generalizing matrix with
  | h size inductionHypothesis =>
    by_cases unimodular : matrix.det.natAbs = 1
    · obtain ⟨frame, equality⟩ := determinant_one_normalizedFrame matrix nonzero normalized unimodular
      refine ⟨Finsupp.single frame 1, ?_⟩
      simp only [LinearMap.comp_apply, apartmentPresentation, Finsupp.linearCombination_single,
        one_smul, normalizedApartment, Submodule.subtype_apply, equality]
    · obtain ⟨vector, normalizedVector, bounds⟩ :=
        normalized_reducing_vector matrix nonzero normalized unimodular
      rw [apartment_replacement_sum
        ⟨integralMatrixRationalFrame matrix nonzero,
          normalizedIntegralMatrix_good_columns matrix nonzero normalized⟩
        (normalizedVectorLine vector normalizedVector)
        (normalizedVectorLine_good vector normalizedVector)]
      apply Submodule.sum_mem
      intro column _membership
      by_cases updateZero : (matrix.updateCol column vector).det = 0
      · rw [replacementTriangle_zero matrix nonzero normalized vector normalizedVector column updateZero]
        exact Submodule.zero_mem _
      · rw [replacementTriangle_apartment matrix nonzero normalized vector normalizedVector column updateZero]
        apply inductionHypothesis (matrix.updateCol column vector).det.natAbs
        · rw [← sizeEquality]
          exact reducing_vector_determinant matrix nonzero vector bounds column
        · exact normalized_updateCol matrix normalized vector normalizedVector column
        · rfl

theorem good_rational_frame_normalized_matrix (frame : GoodRationalFrames) :
    ∃ (matrix : Matrix (Fin 3) (Fin 3) ℤ) (nonzero : matrix.det ≠ 0),
      normalizedIntegralMatrix matrix ∧
      ∀ column, columnLine (integralMatrixRationalFrame matrix nonzero) column =
        columnLine frame.val column := by
  choose integral lineEquality using
    fun column => normalized_line_integral_frame (columnLine frame.val column) (frame.property column)
  let matrix : Matrix (Fin 3) (Fin 3) ℤ := fun row column => (integral column).val.val row 0
  have normalized : normalizedIntegralMatrix matrix := fun column => (integral column).property 0
  have vectorMembership (column : Fin 3) : integerVectorMap (matrix.col column) ∈
      Submodule.span ℚ {frame.val.val.col column} := by
    have subspaceEquality := congrArg (flagSubspace .line) (lineEquality column)
    rw [flagSubspace_mk, line_frame_subspace, columnLine_subspace] at subspaceEquality
    rw [← subspaceEquality]
    exact Submodule.mem_span_singleton_self _
  choose scalar scalarEquality using
    fun column => Submodule.mem_span_singleton.mp (vectorMembership column)
  have scalarNonzero (column : Fin 3) : scalar column ≠ 0 := by
    intro zero
    have equality := scalarEquality column
    rw [zero, zero_smul] at equality
    exact normalizedVector_nonzero (matrix.col column) (normalized column) equality.symm
  have matrixEquality : rationalMatrix matrix =
      Matrix.of (fun row column => scalar column * frame.val.val row column) := by
    ext row column
    exact (congrFun (scalarEquality column) row).symm
  have rationalNonzero : (rationalMatrix matrix).det ≠ 0 := by
    rw [matrixEquality, Matrix.det_mul_row]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun column _membership => scalarNonzero column))
      (isUnit_iff_ne_zero.mp (Matrix.isUnits_det_units frame.val))
  have nonzero : matrix.det ≠ 0 := by
    rwa [rationalMatrix_det, Int.cast_ne_zero] at rationalNonzero
  refine ⟨matrix, nonzero, normalized, ?_⟩
  intro column
  apply flagSubspace_injective
  rw [columnLine_subspace, integralMatrixRationalFrame_val]
  have subspaceEquality := congrArg (flagSubspace .line) (lineEquality column)
  rw [flagSubspace_mk, line_frame_subspace] at subspaceEquality
  exact subspaceEquality

theorem rational_apartment_in_integral_span (frame : GoodRationalFrames) :
    apartment frame.val ∈ integralApartmentSpan := by
  obtain ⟨matrix, nonzero, normalized, columns⟩ := good_rational_frame_normalized_matrix frame
  have apartmentEquality : apartment frame.val =
      apartment (integralMatrixRationalFrame matrix nonzero) := by
    rw [apartment_as_lineConnectors frame.val frame.property,
      apartment_as_lineConnectors _ (normalizedIntegralMatrix_good_columns matrix nonzero normalized)]
    simp only [columns]
  rw [apartmentEquality]
  exact integral_matrix_apartment_in_span matrix nonzero normalized

theorem apartmentPresentation_surjective : Function.Surjective apartmentPresentation := by
  intro chain
  have inclusion : rationalApartmentSpan ≤ integralApartmentSpan := by
    apply Submodule.span_le.mpr
    rintro value ⟨frame, good, rfl⟩
    exact rational_apartment_in_integral_span ⟨frame, good⟩
  obtain ⟨combination, equality⟩ := inclusion
    (goodCycle_mem_rationalApartmentSpan chain.val ((mem_goodCycles _).mp chain.property))
  exact ⟨combination, Subtype.ext equality⟩

end

end TernaryPeriodPolynomials.GoodApartmentFunctional.IntegralReduction
