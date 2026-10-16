module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.ControlledGoodReduction
public import Mathlib.Algebra.Order.Round

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem centered_sign_correction (fraction : ℚ) (centered : |fraction| ≤ 1 / 2) :
    ∃ sign : ℤ, (sign = 1 ∨ sign = -1) ∧
      |fraction - (sign : ℚ)| = 1 - |fraction| := by
  by_cases nonnegative : 0 ≤ fraction
  · refine ⟨1, Or.inl rfl, ?_⟩
    have below_one : fraction - 1 ≤ 0 := by
      rw [abs_of_nonneg nonnegative] at centered
      linarith
    simp only [Int.cast_one, abs_of_nonpos below_one, abs_of_nonneg nonnegative]
    ring
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have nonpositive : fraction ≤ 0 := le_of_not_ge nonnegative
    have above_negative_one : 0 ≤ fraction - (-1) := by
      rw [abs_of_nonpos nonpositive] at centered
      linarith
    simp only [Int.cast_neg, Int.cast_one, abs_of_nonneg above_negative_one, abs_of_nonpos nonpositive]
    ring

/-- A good reduction vector may be chosen with pairwise absolute coordinate
sums at most one. This condition is invariant under column signs. -/
theorem small_good_integral_vector_pairwise
    (integer_matrix : Matrix (Fin 3) (Fin 3) ℤ) (frame : RationalGL3)
    (entries : frame.val = integer_matrix.map (Int.castRingHom ℚ))
    (not_unit : ¬IsUnit integer_matrix)
    (columns_good : ∀ column, (integer_matrix 2 column : ZMod 3) ≠ 0) :
    ∃ (vector : Fin 3 → ℤ) (weights : Fin 3 → ℚ),
      frame.val *ᵥ weights = (fun index => (vector index : ℚ)) ∧
      (∀ index, |weights index| < 1) ∧
      (∀ first second, first ≠ second → |weights first| + |weights second| ≤ 1) ∧
      (vector 2 : ZMod 3) ≠ 0 := by
  classical
  obtain ⟨row, column, nonintegral⟩ :=
    integral_inverse_entry_nonintegral integer_matrix frame entries not_unit
  let coordinates := frame.inv.col column
  let rounded : Fin 3 → ℤ := fun index => round (coordinates index)
  let fractions : Fin 3 → ℚ := coordinates - fun index => (rounded index : ℚ)
  let vector : Fin 3 → ℤ := Pi.single column 1 - integer_matrix *ᵥ rounded
  have inverse_column : frame.val *ᵥ coordinates = Pi.single column 1 := by
    funext index
    have product := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℚ => matrix index column)
      frame.mul_inv
    simpa [coordinates, Matrix.mulVec, Matrix.mul_apply, dotProduct,
      Matrix.one_apply, Pi.single_apply, eq_comm] using product
  have combination : frame.val *ᵥ fractions = fun index => (vector index : ℚ) := by
    rw [show fractions = coordinates - fun index => (rounded index : ℚ) from rfl,
      Matrix.mulVec_sub, inverse_column, entries, integer_matrix_mulVec_cast]
    funext index
    simp [vector, Pi.single_apply]
  have centered (index : Fin 3) : |fractions index| ≤ 1 / 2 := abs_sub_round (coordinates index)
  have small (index : Fin 3) : |fractions index| < 1 := by linarith [centered index]
  by_cases vector_good : (vector 2 : ZMod 3) ≠ 0
  · refine ⟨vector, fractions, combination, small, ?_, vector_good⟩
    intro first second _
    linarith [centered first, centered second]
  · have fractional_nonzero : fractions row ≠ 0 := by
      intro zero
      exact nonintegral (rounded row) (sub_eq_zero.mp zero)
    obtain ⟨largest, maximal⟩ := Finite.exists_max (fun index => |fractions index|)
    have largest_positive : 0 < |fractions largest| :=
      lt_of_lt_of_le (abs_pos.mpr fractional_nonzero) (maximal row)
    obtain ⟨sign, sign_cases, correction⟩ := centered_sign_correction (fractions largest) (centered largest)
    let adjusted : Fin 3 → ℤ := vector - fun index => sign * integer_matrix index largest
    let adjusted_weights : Fin 3 → ℚ := fractions - Pi.single largest (sign : ℚ)
    have signed_column : frame.val *ᵥ Pi.single largest (sign : ℚ) =
        fun index => (sign : ℚ) * frame.val index largest := by
      ext index
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
    have adjusted_largest : |adjusted_weights largest| = 1 - |fractions largest| := by
      simpa only [adjusted_weights, Pi.sub_apply, Pi.single_eq_same] using correction
    have adjusted_other (index : Fin 3) (different : index ≠ largest) :
        adjusted_weights index = fractions index := by
      simp only [adjusted_weights, Pi.sub_apply, Pi.single_eq_of_ne different, sub_zero]
    refine ⟨adjusted, adjusted_weights, ?_, ?_, ?_, ?_⟩
    · rw [show adjusted_weights = fractions - Pi.single largest (sign : ℚ) from rfl,
        Matrix.mulVec_sub, combination, signed_column, entries]
      funext index
      simp [adjusted]
    · intro index
      by_cases same : index = largest
      · subst index
        rw [adjusted_largest]
        linarith
      · rw [adjusted_other index same]
        exact small index
    · intro first second different
      by_cases first_same : first = largest
      · subst first
        rw [adjusted_largest, adjusted_other second (Ne.symm different)]
        linarith [maximal second]
      · rw [adjusted_other first first_same]
        by_cases second_same : second = largest
        · subst second
          rw [adjusted_largest]
          linarith [maximal first]
        · rw [adjusted_other second second_same]
          linarith [centered first, centered second]
    · have zero : (vector 2 : ZMod 3) = 0 := not_ne_iff.mp vector_good
      change ((vector 2 - sign * integer_matrix 2 largest : ℤ) : ZMod 3) ≠ 0
      rcases sign_cases with rfl | rfl <;>
        simpa only [Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_one,
          zero, one_mul, neg_mul, neg_neg, zero_sub, neg_ne_zero] using columns_good largest

theorem pairwise_minor_le_one (first second x y : ℚ)
    (pair_bound : |first| + |second| ≤ 1) (x_bound : |x| ≤ 1) (y_bound : |y| ≤ 1) :
    |first * y - second * x| ≤ 1 := by
  calc
    |first * y - second * x| ≤ |first * y| + |second * x| := abs_sub _ _
    _ = |first| * |y| + |second| * |x| := by rw [abs_mul, abs_mul]
    _ ≤ |first| + |second| := by
      nlinarith [mul_nonneg (abs_nonneg first) (sub_nonneg.mpr y_bound),
        mul_nonneg (abs_nonneg second) (sub_nonneg.mpr x_bound)]
    _ ≤ 1 := pair_bound

theorem pairwise_minor_lt_one (first second x y : ℚ)
    (pair_bound : |first| + |second| ≤ 1) (x_bound : |x| < 1) (y_bound : |y| < 1) :
    |first * y - second * x| < 1 := by
  have maximum_bound : max |x| |y| < 1 := max_lt x_bound y_bound
  have maximum_nonnegative : 0 ≤ max |x| |y| := le_trans (abs_nonneg x) (le_max_left _ _)
  calc
    |first * y - second * x| ≤ |first * y| + |second * x| := abs_sub _ _
    _ = |first| * |y| + |second| * |x| := by rw [abs_mul, abs_mul]
    _ ≤ (|first| + |second|) * max |x| |y| := by
      nlinarith [mul_nonneg (abs_nonneg first) (sub_nonneg.mpr (le_max_right |x| |y|)),
        mul_nonneg (abs_nonneg second) (sub_nonneg.mpr (le_max_left |x| |y|))]
    _ ≤ max |x| |y| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right pair_bound maximum_nonnegative
    _ < 1 := maximum_bound

theorem pairwise_minor_abs_eq_one (first second x y : ℚ)
    (first_small : |first| < 1) (second_small : |second| < 1)
    (pair_bound : |first| + |second| ≤ 1) (x_bound : |x| ≤ 1) (y_bound : |y| ≤ 1)
    (equality : |first * y - second * x| = 1) : |x| = 1 ∧ |y| = 1 ∧ |first| + |second| = 1 := by
  have triangle := abs_sub (first * y) (second * x)
  rw [equality, abs_mul, abs_mul] at triangle
  have first_gap := mul_nonneg (abs_nonneg first) (sub_nonneg.mpr y_bound)
  have second_gap := mul_nonneg (abs_nonneg second) (sub_nonneg.mpr x_bound)
  have pair_eq : |first| + |second| = 1 := by nlinarith
  have first_positive : 0 < |first| := by linarith
  have second_positive : 0 < |second| := by linarith
  have first_slack : |first| * (1 - |y|) = 0 := by nlinarith
  have second_slack : |second| * (1 - |x|) = 0 := by nlinarith
  have y_gap : 1 - |y| = 0 := by
    exact (mul_eq_zero.mp first_slack).resolve_left first_positive.ne'
  have x_gap : 1 - |x| = 0 := by
    exact (mul_eq_zero.mp second_slack).resolve_left second_positive.ne'
  exact ⟨by linarith, by linarith, pair_eq⟩

theorem pairwise_double_replacement_bound (frame : RationalGL3)
    (vector other_vector weights other_weights : Fin 3 → ℚ)
    (combination : frame.val *ᵥ weights = vector)
    (other_combination : frame.val *ᵥ other_weights = other_vector)
    (pair_bound : ∀ first second, first ≠ second → |weights first| + |weights second| ≤ 1)
    (other_bound : ∀ index, |other_weights index| ≤ 1)
    (first second : Fin 3) (different : first ≠ second) :
    |((frame.val.updateCol first vector).updateCol second other_vector).det| ≤ |frame.val.det| := by
  rw [rationalFrame_double_updateCol_det frame vector other_vector weights other_weights
    combination other_combination first second different, abs_mul]
  have minor := pairwise_minor_le_one _ _ _ _ (pair_bound first second different)
    (other_bound first) (other_bound second)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right minor (abs_nonneg frame.val.det)

theorem pairwise_double_replacement_strict (frame : RationalGL3)
    (vector other_vector weights other_weights : Fin 3 → ℚ)
    (combination : frame.val *ᵥ weights = vector)
    (other_combination : frame.val *ᵥ other_weights = other_vector)
    (pair_bound : ∀ first second, first ≠ second → |weights first| + |weights second| ≤ 1)
    (other_small : ∀ index, |other_weights index| < 1)
    (first second : Fin 3) (different : first ≠ second) :
    |((frame.val.updateCol first vector).updateCol second other_vector).det| < |frame.val.det| := by
  rw [rationalFrame_double_updateCol_det frame vector other_vector weights other_weights
    combination other_combination first second different, abs_mul]
  have minor := pairwise_minor_lt_one _ _ _ _ (pair_bound first second different)
    (other_small first) (other_small second)
  have determinant_nonzero := ((Matrix.isUnit_iff_isUnit_det frame.val).mp frame.isUnit).ne_zero
  simpa only [one_mul] using mul_lt_mul_of_pos_right minor (abs_pos.mpr determinant_nonzero)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
