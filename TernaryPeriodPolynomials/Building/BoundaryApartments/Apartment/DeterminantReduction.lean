module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.SmallGoodVector

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem integer_matrix_det_cast (matrix : Matrix (Fin 3) (Fin 3) ℤ) :
    (matrix.det : ℚ) = (matrix.map (Int.castRingHom ℚ)).det :=
  (Int.castRingHom ℚ).map_det matrix

theorem integer_updateCol_det_formula (integer_matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (frame : RationalGL3) (entries : frame.val = integer_matrix.map (Int.castRingHom ℚ))
    (vector : Fin 3 → ℤ) (weights : Fin 3 → ℚ)
    (combination : frame.val *ᵥ weights = fun index => (vector index : ℚ)) (column : Fin 3) :
    ((integer_matrix.updateCol column vector).det : ℚ) = weights column * (integer_matrix.det : ℚ) := by
  rw [integer_matrix_det_cast, Matrix.map_updateCol, ← entries]
  have vector_eq : (fun index => (vector index : ℚ)) =
      fun row => ∑ index, weights index • frame.val row index := by
    rw [← combination]
    funext row
    simp [Matrix.mulVec, dotProduct, mul_comm]
  change (frame.val.updateCol column (fun index => (vector index : ℚ))).det = _
  rw [vector_eq, Matrix.det_updateCol_sum, smul_eq_mul, entries, ← integer_matrix_det_cast]

theorem integer_updateCol_det_decreases (integer_matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (frame : RationalGL3) (entries : frame.val = integer_matrix.map (Int.castRingHom ℚ))
    (determinant_nonzero : integer_matrix.det ≠ 0)
    (vector : Fin 3 → ℤ) (weights : Fin 3 → ℚ)
    (combination : frame.val *ᵥ weights = fun index => (vector index : ℚ))
    (small : ∀ index, |weights index| < 1) (column : Fin 3) :
    (integer_matrix.updateCol column vector).det.natAbs < integer_matrix.det.natAbs := by
  have determinant_cast_nonzero : (integer_matrix.det : ℚ) ≠ 0 := by
    exact_mod_cast determinant_nonzero
  have bound := mul_lt_mul_of_pos_right (small column) (abs_pos.mpr determinant_cast_nonzero)
  rw [one_mul, ← abs_mul,
    ← integer_updateCol_det_formula integer_matrix frame entries vector weights combination column]
    at bound
  have cast_natAbs (integer : ℤ) : (integer.natAbs : ℚ) = |(integer : ℚ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    rfl
  rw [← cast_natAbs, ← cast_natAbs] at bound
  exact_mod_cast bound

theorem good_frame_determinant_reduction (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (determinant_nonzero : matrix.det ≠ 0) (not_unit : ¬IsUnit matrix)
    (columns_good : ∀ column, (matrix 2 column : ZMod 3) ≠ 0) :
    ∃ vector : Fin 3 → ℤ, (vector 2 : ZMod 3) ≠ 0 ∧
      ∀ column, (∀ index, ((matrix.updateCol column vector) 2 index : ZMod 3) ≠ 0) ∧
        (matrix.updateCol column vector).det.natAbs < matrix.det.natAbs := by
  have rational_determinant : (matrix.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [← integer_matrix_det_cast]
    exact_mod_cast determinant_nonzero
  let frame := GeneralLinearGroup.mkOfDetNeZero (matrix.map (Int.castRingHom ℚ)) rational_determinant
  obtain ⟨vector, weights, combination, small, vector_good⟩ :=
    small_good_integral_vector matrix frame rfl not_unit columns_good
  refine ⟨vector, vector_good, ?_⟩
  intro column
  refine ⟨?_, integer_updateCol_det_decreases matrix frame rfl determinant_nonzero
    vector weights combination small column⟩
  intro index
  by_cases same : index = column
  · subst index
    simpa only [Matrix.updateCol_self] using vector_good
  · simpa only [Matrix.updateCol_ne same] using columns_good index

/-- Determinant induction for good integral frames. The replacement vector stays
good, and every column replacement has strictly smaller determinant magnitude. -/
theorem good_integer_frame_induction
    (property : Matrix (Fin 3) (Fin 3) ℤ → Prop)
    (singular : ∀ matrix, matrix.det = 0 → property matrix)
    (unimodular : ∀ matrix, IsUnit matrix →
      (∀ column, (matrix 2 column : ZMod 3) ≠ 0) → property matrix)
    (subdivision : ∀ matrix vector,
      (∀ column, (matrix 2 column : ZMod 3) ≠ 0) → (vector 2 : ZMod 3) ≠ 0 →
      (∀ column, property (matrix.updateCol column vector)) → property matrix)
    (matrix : Matrix (Fin 3) (Fin 3) ℤ)
    (columns_good : ∀ column, (matrix 2 column : ZMod 3) ≠ 0) : property matrix := by
  have induction : ∀ height, ∀ candidate : Matrix (Fin 3) (Fin 3) ℤ,
      candidate.det.natAbs = height →
      (∀ column, (candidate 2 column : ZMod 3) ≠ 0) → property candidate := by
    intro height
    induction height using Nat.strong_induction_on with
    | h height previous =>
      intro candidate height_eq good
      by_cases determinant_zero : candidate.det = 0
      · exact singular candidate determinant_zero
      · by_cases unit : IsUnit candidate
        · exact unimodular candidate unit good
        · obtain ⟨vector, vector_good, replacements⟩ :=
            good_frame_determinant_reduction candidate determinant_zero unit good
          apply subdivision candidate vector good vector_good
          intro column
          exact previous _ (height_eq ▸ (replacements column).2)
            (candidate.updateCol column vector) rfl (replacements column).1
  exact induction _ matrix rfl columns_good

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
