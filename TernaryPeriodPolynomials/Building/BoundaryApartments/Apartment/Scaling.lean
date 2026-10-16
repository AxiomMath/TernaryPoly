module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.Subdivision

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem edge_eq_of_scaled_columns (first second : RationalGL3) (first_scale second_scale : ℚ)
    (first_column : ∀ row, second.val row 0 = first_scale * first.val row 0)
    (second_column : ∀ row, second.val row 1 = second_scale * first.val row 1) :
    (QuotientGroup.mk first : Edges) = QuotientGroup.mk second := by
  have product (column : Fin 3) (scalar : ℚ)
      (same : ∀ row, second.val row column = scalar * first.val row column)
      (row : Fin 3) : (first⁻¹ * second).val row column =
        scalar * (1 : RationalGL3).val row column := by
    calc
      (first⁻¹ * second).val row column = scalar * (first⁻¹ * first).val row column := by
        simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, same]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro index _
        ring
      _ = _ := by rw [inv_mul_cancel]
  apply QuotientGroup.eq.mpr
  constructor <;> constructor
  · simpa using product 0 first_scale first_column 2
  · simpa using product 1 second_scale second_column 2
  · simpa using product 0 first_scale first_column 1
  · simpa using product 0 first_scale first_column 2

theorem framePair_eq_of_scaled_columns (first second : RationalGL3) (first_scale second_scale : ℚ)
    (first_column : ∀ row, second.val row 0 = first_scale * first.val row 0)
    (second_column : ∀ row, second.val row 1 = second_scale * first.val row 1) :
    framePair first = framePair second := by
  have unswapped := edge_eq_of_scaled_columns first second first_scale second_scale
    first_column second_column
  have swapped := edge_eq_of_scaled_columns (first * swapFirstTwo) (second * swapFirstTwo)
    second_scale first_scale
    (by simpa only [frame_swap_firstColumn] using second_column)
    (by simpa only [frame_swap_secondColumn] using first_column)
  simp only [framePair, unswapped, swapped]

theorem apartment_eq_of_scaled_columns (first second : RationalGL3) (scales : Fin 3 → ℚ)
    (columns : ∀ row column, second.val row column = scales column * first.val row column) :
    apartment first = apartment second := by
  have first_pair := framePair_eq_of_scaled_columns first second (scales 0) (scales 1)
    (fun row => columns row 0) (fun row => columns row 1)
  have second_pair := framePair_eq_of_scaled_columns (first * Adelic.weyl) (second * Adelic.weyl)
    (scales 1) (scales 2)
    (by simpa only [frame_weyl_firstColumn] using fun row => columns row 1)
    (by simpa only [frame_weyl_secondColumn] using fun row => columns row 2)
  have third_pair := framePair_eq_of_scaled_columns (first * Adelic.weyl ^ 2)
    (second * Adelic.weyl ^ 2) (scales 2) (scales 0)
    (by simpa only [frame_weylSquared_firstColumn] using fun row => columns row 2)
    (by simpa only [frame_weylSquared_secondColumn] using fun row => columns row 0)
  simp only [apartment_eq_framePairs, first_pair, second_pair, third_pair]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
