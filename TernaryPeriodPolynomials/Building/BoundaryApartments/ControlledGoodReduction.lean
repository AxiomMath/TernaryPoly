module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.SmallGoodVector

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

/-- Choose the column of largest fractional coordinate when correcting
goodness. The reduced coordinates then differ by at most one. -/
theorem small_good_integral_vector_bounded_spread
    (integer_matrix : Matrix (Fin 3) (Fin 3) ℤ) (frame : RationalGL3)
    (entries : frame.val = integer_matrix.map (Int.castRingHom ℚ))
    (not_unit : ¬IsUnit integer_matrix)
    (columns_good : ∀ column, (integer_matrix 2 column : ZMod 3) ≠ 0) :
    ∃ (vector : Fin 3 → ℤ) (weights : Fin 3 → ℚ),
      frame.val *ᵥ weights = (fun index => (vector index : ℚ)) ∧
      (∀ index, |weights index| < 1) ∧
      (∀ first second, weights first - weights second ≤ 1) ∧ (vector 2 : ZMod 3) ≠ 0 := by
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
  · refine ⟨vector, fractions, combination, small, ?_, vector_good⟩
    intro first second
    linarith [less_one first, nonnegative second]
  · have fractional_positive : 0 < fractions row := by
      apply lt_of_le_of_ne (nonnegative row)
      intro zero
      apply nonintegral (floors row)
      change coordinates row = (floors row : ℚ)
      apply sub_eq_zero.mp
      exact zero.symm
    obtain ⟨largest, maximal⟩ := Finite.exists_max fractions
    have largest_positive : 0 < fractions largest := lt_of_lt_of_le fractional_positive (maximal row)
    let adjusted : Fin 3 → ℤ := vector - integer_matrix.col largest
    let adjusted_weights : Fin 3 → ℚ := fractions - Pi.single largest 1
    refine ⟨adjusted, adjusted_weights, ?_, ?_, ?_, ?_⟩
    · rw [show adjusted_weights = fractions - Pi.single largest 1 from rfl,
        Matrix.mulVec_sub, combination, Matrix.mulVec_single_one, entries]
      funext index
      simp [adjusted]
    · intro index
      dsimp only [adjusted_weights, Pi.sub_apply]
      by_cases same : index = largest
      · rw [same, Pi.single_eq_same]
        apply abs_lt.mpr
        constructor <;> linarith [less_one largest]
      · simpa only [Pi.single_eq_of_ne same, sub_zero] using small index
    · intro first second
      dsimp only [adjusted_weights, Pi.sub_apply]
      by_cases first_same : first = largest
      · subst first
        by_cases second_same : second = largest
        · subst second
          simp
        · simp only [Pi.single_eq_same, Pi.single_eq_of_ne second_same, sub_zero]
          linarith [less_one largest, nonnegative second]
      · by_cases second_same : second = largest
        · subst second
          simp only [Pi.single_eq_same, Pi.single_eq_of_ne first_same, sub_zero]
          linarith [maximal first]
        · simp only [Pi.single_eq_of_ne first_same, Pi.single_eq_of_ne second_same, sub_zero]
          linarith [less_one first, nonnegative second]
    · have zero : (vector 2 : ZMod 3) = 0 := not_ne_iff.mp vector_good
      change ((vector 2 - integer_matrix 2 largest : ℤ) : ZMod 3) ≠ 0
      simpa only [Int.cast_sub, zero, zero_sub, neg_ne_zero] using columns_good largest

theorem controlled_minor_le_one (first second x y : ℚ)
    (first_small : |first| < 1) (second_small : |second| < 1)
    (spread : first - second ≤ 1) (reverse_spread : second - first ≤ 1)
    (x_nonnegative : 0 ≤ x) (x_le : x ≤ 1) (y_nonnegative : 0 ≤ y) (y_le : y ≤ 1) :
    |first * y - second * x| ≤ 1 := by
  obtain ⟨first_lower, first_upper⟩ := abs_lt.mp first_small
  obtain ⟨second_lower, second_upper⟩ := abs_lt.mp second_small
  have x_gap : 0 ≤ 1 - x := sub_nonneg.mpr x_le
  have y_gap : 0 ≤ 1 - y := sub_nonneg.mpr y_le
  apply abs_le.mpr
  by_cases first_nonnegative : 0 ≤ first
  · by_cases second_nonnegative : 0 ≤ second
    · constructor <;> nlinarith [mul_nonneg first_nonnegative y_nonnegative,
        mul_nonneg second_nonnegative x_nonnegative, mul_nonneg first_nonnegative y_gap,
        mul_nonneg second_nonnegative x_gap]
    · have second_nonpositive : second ≤ 0 := le_of_not_ge second_nonnegative
      constructor <;> nlinarith [mul_nonneg first_nonnegative y_nonnegative,
        mul_nonneg (neg_nonneg.mpr second_nonpositive) x_nonnegative,
        mul_nonneg first_nonnegative y_gap, mul_nonneg (neg_nonneg.mpr second_nonpositive) x_gap]
  · have first_nonpositive : first ≤ 0 := le_of_not_ge first_nonnegative
    by_cases second_nonnegative : 0 ≤ second
    · constructor <;> nlinarith [mul_nonneg (neg_nonneg.mpr first_nonpositive) y_nonnegative,
        mul_nonneg second_nonnegative x_nonnegative,
        mul_nonneg (neg_nonneg.mpr first_nonpositive) y_gap, mul_nonneg second_nonnegative x_gap]
    · have second_nonpositive : second ≤ 0 := le_of_not_ge second_nonnegative
      constructor <;> nlinarith [mul_nonneg (neg_nonneg.mpr first_nonpositive) y_nonnegative,
        mul_nonneg (neg_nonneg.mpr second_nonpositive) x_nonnegative,
        mul_nonneg (neg_nonneg.mpr first_nonpositive) y_gap,
        mul_nonneg (neg_nonneg.mpr second_nonpositive) x_gap]

theorem controlled_minor_eq_one (first second x y : ℚ)
    (first_small : |first| < 1) (second_small : |second| < 1)
    (spread : first - second ≤ 1)
    (x_nonnegative : 0 ≤ x) (x_le : x ≤ 1) (y_nonnegative : 0 ≤ y) (y_le : y ≤ 1)
    (equality : first * y - second * x = 1) : x = 1 ∧ y = 1 ∧ first - second = 1 := by
  obtain ⟨first_lower, first_upper⟩ := abs_lt.mp first_small
  obtain ⟨second_lower, second_upper⟩ := abs_lt.mp second_small
  have x_gap : 0 ≤ 1 - x := sub_nonneg.mpr x_le
  have y_gap : 0 ≤ 1 - y := sub_nonneg.mpr y_le
  have first_positive : 0 < first := by
    by_contra not_positive
    have first_nonpositive : first ≤ 0 := le_of_not_gt not_positive
    by_cases second_nonnegative : 0 ≤ second
    · nlinarith [mul_nonneg (neg_nonneg.mpr first_nonpositive) y_nonnegative,
        mul_nonneg second_nonnegative x_nonnegative]
    · have second_nonpositive : second ≤ 0 := le_of_not_ge second_nonnegative
      nlinarith [mul_nonneg (neg_nonneg.mpr first_nonpositive) y_nonnegative,
        mul_nonneg (neg_nonneg.mpr second_nonpositive) x_gap]
  have second_negative : second < 0 := by
    by_contra not_negative
    have second_nonnegative : 0 ≤ second := le_of_not_gt not_negative
    nlinarith [mul_nonneg first_positive.le y_gap, mul_nonneg second_nonnegative x_nonnegative]
  have first_slack := mul_nonneg first_positive.le y_gap
  have second_slack := mul_nonneg (neg_nonneg.mpr second_negative.le) x_gap
  have spread_eq : first - second = 1 := by nlinarith
  have x_slack : (-second) * (1 - x) = 0 := by nlinarith
  have y_slack : first * (1 - y) = 0 := by nlinarith
  have x_eq : 1 - x = 0 := (mul_eq_zero.mp x_slack).resolve_left (neg_ne_zero.mpr second_negative.ne)
  have y_eq : 1 - y = 0 := (mul_eq_zero.mp y_slack).resolve_left first_positive.ne'
  exact ⟨by linarith, by linarith, spread_eq⟩

theorem controlled_minor_abs_eq_one (first second x y : ℚ)
    (first_small : |first| < 1) (second_small : |second| < 1)
    (spread : first - second ≤ 1) (reverse_spread : second - first ≤ 1)
    (x_nonnegative : 0 ≤ x) (x_le : x ≤ 1) (y_nonnegative : 0 ≤ y) (y_le : y ≤ 1)
    (equality : |first * y - second * x| = 1) : x = 1 ∧ y = 1 ∧ |first - second| = 1 := by
  by_cases nonnegative : 0 ≤ first * y - second * x
  · rw [abs_of_nonneg nonnegative] at equality
    obtain ⟨x_eq, y_eq, spread_eq⟩ := controlled_minor_eq_one first second x y
      first_small second_small spread x_nonnegative x_le y_nonnegative y_le equality
    exact ⟨x_eq, y_eq, by rw [spread_eq, abs_one]⟩
  · rw [abs_of_nonpos (le_of_not_ge nonnegative)] at equality
    have reversed : second * x - first * y = 1 := by linarith
    obtain ⟨y_eq, x_eq, spread_eq⟩ := controlled_minor_eq_one second first y x
      second_small first_small reverse_spread y_nonnegative y_le x_nonnegative x_le reversed
    refine ⟨x_eq, y_eq, ?_⟩
    have negative_spread : first - second = -1 := by linarith
    rw [negative_spread, abs_neg, abs_one]

theorem identity_double_updateCol_det (weights other_weights : Fin 3 → ℚ) (first second : Fin 3)
    (different : first ≠ second) :
    (((1 : Matrix (Fin 3) (Fin 3) ℚ).updateCol first weights).updateCol second other_weights).det =
      weights first * other_weights second - weights second * other_weights first := by
  fin_cases first <;> fin_cases second <;>
    simp_all [Matrix.det_fin_three] <;> ring

theorem rationalFrame_double_updateCol_det (frame : RationalGL3)
    (vector other_vector weights other_weights : Fin 3 → ℚ)
    (combination : frame.val *ᵥ weights = vector)
    (other_combination : frame.val *ᵥ other_weights = other_vector)
    (first second : Fin 3) (different : first ≠ second) :
    ((frame.val.updateCol first vector).updateCol second other_vector).det =
      (weights first * other_weights second - weights second * other_weights first) * frame.val.det := by
  have updated : (frame.val.updateCol first vector).updateCol second other_vector =
      frame.val * (((1 : Matrix (Fin 3) (Fin 3) ℚ).updateCol first weights).updateCol second other_weights) := by
    rw [Matrix.mul_updateCol, Matrix.mul_updateCol, Matrix.mul_one, combination, other_combination]
  rw [updated, Matrix.det_mul, identity_double_updateCol_det weights other_weights first second different]
  ring

theorem controlled_double_replacement_bound (frame : RationalGL3)
    (vector other_vector weights other_weights : Fin 3 → ℚ)
    (combination : frame.val *ᵥ weights = vector)
    (other_combination : frame.val *ᵥ other_weights = other_vector)
    (small : ∀ index, |weights index| < 1)
    (spread : ∀ first second, weights first - weights second ≤ 1)
    (nonnegative : ∀ index, 0 ≤ other_weights index)
    (at_most_one : ∀ index, other_weights index ≤ 1)
    (first second : Fin 3) (different : first ≠ second) :
    |((frame.val.updateCol first vector).updateCol second other_vector).det| ≤ |frame.val.det| := by
  rw [rationalFrame_double_updateCol_det frame vector other_vector weights other_weights
    combination other_combination first second different, abs_mul]
  have minor := controlled_minor_le_one (weights first) (weights second)
    (other_weights first) (other_weights second) (small first) (small second)
    (spread first second) (spread second first) (nonnegative first) (at_most_one first)
    (nonnegative second) (at_most_one second)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right minor (abs_nonneg frame.val.det)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
