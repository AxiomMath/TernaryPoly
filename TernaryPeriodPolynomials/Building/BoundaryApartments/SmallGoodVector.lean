module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.Presentation
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section


open GeneralEisenstein

noncomputable section


namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem integral_inverse_entry_nonintegral
    (integer_matrix : Matrix (Fin 3) (Fin 3) ℤ) (frame : RationalGL3)
    (entries : frame.val = integer_matrix.map (Int.castRingHom ℚ))
    (not_unit : ¬IsUnit integer_matrix) :
    ∃ row column, ∀ integer : ℤ, frame.inv row column ≠ (integer : ℚ) := by
  classical
  by_contra no_entry
  push Not at no_entry
  choose coefficients inverse_entries using no_entry
  let inverse : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of coefficients
  have inverse_eq : inverse.map (Int.castRingHom ℚ) = frame.inv := by
    ext row column
    exact (inverse_entries row column).symm
  have left_inverse : integer_matrix * inverse = 1 := by
    apply Matrix.map_injective (Int.cast_injective (α := ℚ))
    change (integer_matrix * inverse).map (Int.castRingHom ℚ) =
      (1 : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)
    rw [Matrix.map_mul, inverse_eq, ← entries]
    simp
  have right_inverse : inverse * integer_matrix = 1 := by
    apply Matrix.map_injective (Int.cast_injective (α := ℚ))
    change (inverse * integer_matrix).map (Int.castRingHom ℚ) =
      (1 : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℚ)
    rw [Matrix.map_mul, inverse_eq, ← entries]
    simp
  exact not_unit ⟨⟨integer_matrix, inverse, left_inverse, right_inverse⟩, rfl⟩

theorem integer_matrix_mulVec_cast (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (vector : Fin 3 → ℤ) :
    matrix.map (Int.castRingHom ℚ) *ᵥ (fun index => (vector index : ℚ)) =
      fun index => ((matrix *ᵥ vector) index : ℚ) := by
  ext index
  simp [Matrix.mulVec, dotProduct]

/-- A nonunimodular good frame contains a good integral vector whose frame
coordinates all have absolute value strictly less than one. -/
theorem small_good_integral_vector
    (integer_matrix : Matrix (Fin 3) (Fin 3) ℤ) (frame : RationalGL3)
    (entries : frame.val = integer_matrix.map (Int.castRingHom ℚ))
    (not_unit : ¬IsUnit integer_matrix)
    (columns_good : ∀ column, (integer_matrix 2 column : ZMod 3) ≠ 0) :
    ∃ (vector : Fin 3 → ℤ) (weights : Fin 3 → ℚ),
      frame.val *ᵥ weights = (fun index => (vector index : ℚ)) ∧
      (∀ index, |weights index| < 1) ∧ (vector 2 : ZMod 3) ≠ 0 := by
  classical
  obtain ⟨row, column, nonintegral⟩ :=
    integral_inverse_entry_nonintegral integer_matrix frame entries not_unit
  let coordinates := frame.inv.col column
  let floors : Fin 3 → ℤ := fun index => ⌊coordinates index⌋
  let fractions : Fin 3 → ℚ := fun index => Int.fract (coordinates index)
  let vector : Fin 3 → ℤ := Pi.single column 1 - integer_matrix *ᵥ floors
  have inverse_column : frame.val *ᵥ coordinates = Pi.single column 1 := by
    funext index
    have product := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℚ => matrix index column)
      frame.mul_inv
    simpa [coordinates, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Matrix.one_apply, Pi.single_apply, eq_comm] using product
  have fraction_coordinates : fractions = coordinates - fun index => (floors index : ℚ) := rfl
  have combination : frame.val *ᵥ fractions = fun index => (vector index : ℚ) := by
    rw [fraction_coordinates, Matrix.mulVec_sub, inverse_column, entries,
      integer_matrix_mulVec_cast]
    funext index
    simp [vector, Pi.single_apply]
  have nonnegative (index : Fin 3) : 0 ≤ fractions index := Int.fract_nonneg _
  have less_one (index : Fin 3) : fractions index < 1 := Int.fract_lt_one _
  have small (index : Fin 3) : |fractions index| < 1 := by
    rw [abs_of_nonneg (nonnegative index)]
    exact less_one index
  by_cases vector_good : (vector 2 : ZMod 3) ≠ 0
  · exact ⟨vector, fractions, combination, small, vector_good⟩
  · have fractional_positive : 0 < fractions row := by
      apply lt_of_le_of_ne (nonnegative row)
      intro zero
      apply nonintegral (floors row)
      change coordinates row = (floors row : ℚ)
      apply sub_eq_zero.mp
      exact zero.symm
    let adjusted : Fin 3 → ℤ := vector - integer_matrix.col row
    let adjusted_weights : Fin 3 → ℚ := fractions - Pi.single row 1
    refine ⟨adjusted, adjusted_weights, ?_, ?_, ?_⟩
    · rw [show adjusted_weights = fractions - Pi.single row 1 from rfl,
        Matrix.mulVec_sub, combination, Matrix.mulVec_single_one, entries]
      funext index
      simp [adjusted]
    · intro index
      dsimp only [adjusted_weights, Pi.sub_apply]
      by_cases same : index = row
      · rw [same, Pi.single_eq_same]
        apply abs_lt.mpr
        constructor <;> linarith [less_one row]
      · simpa only [Pi.single_eq_of_ne same, sub_zero] using small index
    · have zero : (vector 2 : ZMod 3) = 0 := not_ne_iff.mp vector_good
      change ((vector 2 - integer_matrix 2 row : ℤ) : ZMod 3) ≠ 0
      simpa only [Int.cast_sub, zero, zero_sub, neg_ne_zero] using columns_good row

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
