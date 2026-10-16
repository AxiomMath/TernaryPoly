module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Apartment.ChainRelations

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem edge_eq_of_first_two_columns (first second : RationalGL3)
    (first_column : ∀ row, second.val row 0 = first.val row 0)
    (second_column : ∀ row, second.val row 1 = first.val row 1) :
    (QuotientGroup.mk first : Edges) = QuotientGroup.mk second := by
  have product (column : Fin 3) (same : ∀ row, second.val row column = first.val row column)
      (row : Fin 3) : (first⁻¹ * second).val row column = (1 : RationalGL3).val row column := by
    calc
      (first⁻¹ * second).val row column = (first⁻¹ * first).val row column := by
        simp only [GeneralLinearGroup.coe_mul, Matrix.mul_apply, same]
      _ = _ := by rw [inv_mul_cancel]
  apply QuotientGroup.eq.mpr
  exact ⟨⟨product 0 first_column 2, product 1 second_column 2⟩,
    ⟨product 0 first_column 1, product 0 first_column 2⟩⟩

theorem frame_swap_secondColumn (frame : RationalGL3) (row : Fin 3) :
    (frame * swapFirstTwo).val row 1 = frame.val row 0 := by
  simp [swapFirstTwo, Matrix.mul_apply, Fin.sum_univ_three]

def framePair (frame : RationalGL3) : EdgeChains :=
  Finsupp.single (QuotientGroup.mk frame) 1 -
    Finsupp.single (QuotientGroup.mk (frame * swapFirstTwo)) 1

theorem framePair_eq_of_columns (first second : RationalGL3)
    (first_column : ∀ row, second.val row 0 = first.val row 0)
    (second_column : ∀ row, second.val row 1 = first.val row 1) :
    framePair first = framePair second := by
  have unswapped := edge_eq_of_first_two_columns first second first_column second_column
  have swapped := edge_eq_of_first_two_columns (first * swapFirstTwo) (second * swapFirstTwo)
    (by simpa only [frame_swap_firstColumn] using second_column)
    (by simpa only [frame_swap_secondColumn] using first_column)
  simp only [framePair, unswapped, swapped]

theorem framePair_reverse_of_columns (first second : RationalGL3)
    (first_column : ∀ row, second.val row 0 = first.val row 1)
    (second_column : ∀ row, second.val row 1 = first.val row 0) :
    framePair second = -framePair first := by
  have unswapped := edge_eq_of_first_two_columns (first * swapFirstTwo) second
    (by simpa only [frame_swap_firstColumn] using first_column)
    (by simpa only [frame_swap_secondColumn] using second_column)
  have swapped := edge_eq_of_first_two_columns first (second * swapFirstTwo)
    (by simpa only [frame_swap_firstColumn] using second_column)
    (by simpa only [frame_swap_secondColumn] using first_column)
  rw [framePair, framePair, ← unswapped, ← swapped]
  abel

theorem frame_weyl_firstColumn (frame : RationalGL3) (row : Fin 3) :
    (frame * Adelic.weyl).val row 0 = frame.val row 1 := by
  simp [Adelic.weyl, Matrix.mul_apply, Fin.sum_univ_three]

theorem frame_weyl_secondColumn (frame : RationalGL3) (row : Fin 3) :
    (frame * Adelic.weyl).val row 1 = frame.val row 2 := by
  simp [Adelic.weyl, Matrix.mul_apply, Fin.sum_univ_three]

theorem frame_weylSquared_firstColumn (frame : RationalGL3) (row : Fin 3) :
    (frame * Adelic.weyl ^ 2).val row 0 = frame.val row 2 := by
  simp [Adelic.weyl, pow_two, Matrix.mul_apply, Fin.sum_univ_three]

theorem frame_weylSquared_secondColumn (frame : RationalGL3) (row : Fin 3) :
    (frame * Adelic.weyl ^ 2).val row 1 = frame.val row 0 := by
  simp [Adelic.weyl, pow_two, Matrix.mul_apply, Fin.sum_univ_three]

theorem apartment_eq_framePairs (frame : RationalGL3) :
    apartment frame = framePair frame + framePair (frame * Adelic.weyl) +
      framePair (frame * Adelic.weyl ^ 2) := by
  simp only [apartment, framePair]
  abel

theorem apartment_subdivision_nondegenerate (frame : RationalGL3) (vector : Fin 3 → ℚ)
    (first_nonzero : (frame.val.updateCol 0 vector).det ≠ 0)
    (second_nonzero : (frame.val.updateCol 1 vector).det ≠ 0)
    (third_nonzero : (frame.val.updateCol 2 vector).det ≠ 0) :
    apartment frame =
      apartment (GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 0 vector) first_nonzero) +
      apartment (GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 1 vector) second_nonzero) +
      apartment (GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 2 vector) third_nonzero) := by
  let first := GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 0 vector) first_nonzero
  let second := GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 1 vector) second_nonzero
  let third := GeneralLinearGroup.mkOfDetNeZero (frame.val.updateCol 2 vector) third_nonzero
  have original_first : framePair third = framePair frame := by
    apply framePair_eq_of_columns <;> intro row <;> simp [third]
  have original_second : framePair (first * Adelic.weyl) = framePair (frame * Adelic.weyl) := by
    apply framePair_eq_of_columns <;> intro row <;>
      simp [frame_weyl_firstColumn, frame_weyl_secondColumn, first]
  have original_third : framePair (second * Adelic.weyl ^ 2) =
      framePair (frame * Adelic.weyl ^ 2) := by
    apply framePair_eq_of_columns <;> intro row <;>
      simp [frame_weylSquared_firstColumn, frame_weylSquared_secondColumn, second]
  have internal_first : framePair (third * Adelic.weyl) = -framePair first := by
    apply framePair_reverse_of_columns <;> intro row <;>
      simp [frame_weyl_firstColumn, frame_weyl_secondColumn, first, third]
  have internal_second : framePair (second * Adelic.weyl) =
      -framePair (first * Adelic.weyl ^ 2) := by
    apply framePair_reverse_of_columns <;> intro row <;>
      simp [frame_weyl_firstColumn, frame_weyl_secondColumn,
        frame_weylSquared_firstColumn, frame_weylSquared_secondColumn, first, second]
  have internal_third : framePair (third * Adelic.weyl ^ 2) = -framePair second := by
    apply framePair_reverse_of_columns <;> intro row <;>
      simp [frame_weylSquared_firstColumn, frame_weylSquared_secondColumn, second, third]
  change apartment frame = apartment first + apartment second + apartment third
  simp only [apartment_eq_framePairs, original_first, original_second, original_third,
    internal_first, internal_second, internal_third]
  abel

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
