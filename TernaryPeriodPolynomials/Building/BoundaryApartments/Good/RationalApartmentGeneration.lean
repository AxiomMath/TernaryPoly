module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.IntegralApartmentGeneration

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem firstColumn_multiple_of_line_eq (first second : RationalGL3)
    (same_line : (QuotientGroup.mk first : Flags .line) = QuotientGroup.mk second) :
    ∃ scalar : ℚ, ∀ row, second.val row 0 = scalar * first.val row 0 := by
  have parabolic := QuotientGroup.eq.mp same_line
  change (first⁻¹ * second).val 1 0 = 0 ∧ (first⁻¹ * second).val 2 0 = 0 at parabolic
  refine ⟨(first⁻¹ * second).val 0 0, ?_⟩
  intro row
  have product : first * (first⁻¹ * second) = second := mul_inv_cancel_left first second
  have entry := congrArg (fun matrix : RationalGL3 => matrix.val row 0) product
  rw [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three] at entry
  simpa only [parabolic.1, parabolic.2, mul_zero, zero_mul, add_zero, mul_comm] using entry.symm

theorem good_line_integral_multiple (frame : RationalGL3)
    (good : GoodFlag .line (QuotientGroup.mk frame)) :
    ∃ (vector : Fin 3 → ℤ) (scalar : ℚ), scalar ≠ 0 ∧
      (∀ row, (vector row : ℚ) = scalar * frame.val row 0) ∧ (vector 2 : ZMod 3) ≠ 0 := by
  obtain ⟨vector, ⟨representative, same_line, weights, weights_condition, combination⟩,
    vector_good⟩ := good
  obtain ⟨scale, columns⟩ := firstColumn_multiple_of_line_eq frame representative same_line.symm
  have vector_eq (row : Fin 3) : (vector row : ℚ) =
      (weights 0 * scale) * frame.val row 0 := by
    have entry := congrFun combination row
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      weights_condition.1, weights_condition.2, mul_zero, add_zero, columns] at entry
    rw [← entry]
    ring
  refine ⟨vector, weights 0 * scale, ?_, vector_eq, vector_good⟩
  intro zero_scale
  have rational_zero : (vector 2 : ℚ) = 0 := by rw [vector_eq, zero_scale, zero_mul]
  have integer_zero : vector 2 = 0 := by exact_mod_cast rational_zero
  exact vector_good (by rw [integer_zero, Int.cast_zero])

theorem frame_weylPower_firstColumn (frame : RationalGL3) (column row : Fin 3) :
    (frame * Adelic.weyl ^ column.val).val row 0 = frame.val row column := by
  fin_cases column
  · simp
  · change (frame * Adelic.weyl ^ 1).val row 0 = frame.val row 1
    simpa only [pow_one] using frame_weyl_firstColumn frame row
  · exact frame_weylSquared_firstColumn frame row

theorem good_rational_apartment_in_presentation (frame : RationalGL3)
    (columns_good : ∀ column : Fin 3,
      GoodFlag .line (QuotientGroup.mk (frame * Adelic.weyl ^ column.val))) :
    ∃ symbols : ApartmentSymbols, (apartmentPresentationMap symbols).val = apartment frame := by
  have multiples (column : Fin 3) : ∃ (vector : Fin 3 → ℤ) (scalar : ℚ), scalar ≠ 0 ∧
      (∀ row, (vector row : ℚ) = scalar * frame.val row column) ∧ (vector 2 : ZMod 3) ≠ 0 := by
    simpa only [frame_weylPower_firstColumn] using
      good_line_integral_multiple (frame * Adelic.weyl ^ column.val) (columns_good column)
  choose vectors scalars scales_nonzero columns vectors_good using multiples
  let matrix : Matrix (Fin 3) (Fin 3) ℤ := fun row column => vectors column row
  have entries : matrix.map (Int.castRingHom ℚ) =
      Matrix.of (fun row column => scalars column * frame.val row column) := by
    ext row column
    exact columns column row
  have nonzero : (matrix.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [entries, Matrix.det_mul_row]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun index _ => scales_nonzero index))
      (rationalFrame_det_nonzero frame)
  let integral_frame := GeneralLinearGroup.mkOfDetNeZero (matrix.map (Int.castRingHom ℚ)) nonzero
  obtain ⟨symbols, value⟩ := good_integral_apartment_in_presentation matrix integral_frame rfl
    vectors_good
  refine ⟨symbols, ?_⟩
  rw [value]
  symm
  apply apartment_eq_of_scaled_columns frame integral_frame scalars
  intro row column
  exact columns column row

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
