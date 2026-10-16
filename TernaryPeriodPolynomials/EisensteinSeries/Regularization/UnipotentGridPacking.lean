module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearBoxes

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Pointwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem real_grid_index_unique {radius first second : ℝ} {i j : ℕ}
    (positive : 0 < radius) (first_bound : |first| ≤ radius) (second_bound : |second| ≤ radius)
    (equality : 4 * radius * i + first = 4 * radius * j + second) : i = j := by
  rcases abs_le.mp first_bound with ⟨first_lower, first_upper⟩
  rcases abs_le.mp second_bound with ⟨second_lower, second_upper⟩
  by_contra different
  rcases lt_or_gt_of_ne different with less | greater
  · have separated : (i : ℝ) + 1 ≤ j := by exact_mod_cast less
    nlinarith
  · have separated : (j : ℝ) + 1 ≤ i := by exact_mod_cast greater
    nlinarith

def realSpecialGridShift {L M N : ℕ} (r s t : ℝ) (index : Fin L × Fin M × Fin N) :
    SpecialLinearGroup (Fin 3) ℝ :=
  realSpecialUnipotent (4 * r * index.1.val) (4 * s * index.2.1.val) (4 * t * index.2.2.val)

theorem realSpecialSiegelBox_grid_disjoint {L M N : ℕ} {r s t : ℝ}
    (rpos : 0 < r) (spos : 0 < s) (tpos : 0 < t)
    {diagonals : Set (SpecialLinearGroup (Fin 3) ℝ)}
    (positive : ∀ diagonal ∈ diagonals, realPositiveDiagonal (SpecialLinearGroup.toGL diagonal)) :
    Pairwise (fun first second : Fin L × Fin M × Fin N =>
      Disjoint (realSpecialGridShift r s t first • realSpecialSiegelBox r s t diagonals)
        (realSpecialGridShift r s t second • realSpecialSiegelBox r s t diagonals)) := by
  intro first second different
  apply Set.disjoint_left.mpr
  intro matrix first_member second_member
  obtain ⟨firstPoint, first_point_member, first_eq⟩ := first_member
  obtain ⟨secondPoint, second_point_member, second_eq⟩ := second_member
  obtain ⟨x, y, z, diagonal, rotation, hx, hy, hz, hd, hk, firstPoint_eq⟩ :=
    mem_realSpecialSiegelBox_iff.mp first_point_member
  obtain ⟨x', y', z', diagonal', rotation', hx', hy', hz', hd', hk', secondPoint_eq⟩ :=
    mem_realSpecialSiegelBox_iff.mp second_point_member
  have equality : realSpecialGridShift r s t first * firstPoint =
      realSpecialGridShift r s t second * secondPoint := first_eq.trans second_eq.symm
  rw [firstPoint_eq, secondPoint_eq] at equality
  simp only [realSpecialGridShift, ← mul_assoc, realSpecialUnipotent_mul] at equality
  obtain ⟨horizontal, vertical1, vertical0⟩ :=
    realSpecialUnipotent_coordinates_unique (positive _ hd) (positive _ hd') hk hk' equality
  have first_index : first.1 = second.1 := Fin.ext (real_grid_index_unique rpos hx hx' horizontal)
  have second_index : first.2.1 = second.2.1 := Fin.ext (real_grid_index_unique spos hy hy' vertical1)
  rw [second_index] at vertical1
  have y_eq : y = y' := add_left_cancel vertical1
  rw [first_index, y_eq] at vertical0
  have third_index : first.2.2 = second.2.2 :=
    Fin.ext (real_grid_index_unique tpos hz hz' (add_right_cancel vertical0))
  exact different (Prod.ext first_index (Prod.ext second_index third_index))

theorem real_grid_coordinate_bound {radius : ℝ} {count : ℕ} (nonnegative : 0 ≤ radius)
    (bounded : radius * count ≤ 1 / 2) (index : Fin count) :
    |4 * radius * index.val| ≤ 2 := by
  have index_le : (index.val : ℝ) ≤ count := by exact_mod_cast index.isLt.le
  rw [abs_of_nonneg (by positivity)]
  nlinarith

theorem realSpecialSiegelBox_grid_subset {L M N : ℕ} {r s t : ℝ}
    (rnonneg : 0 ≤ r) (snonneg : 0 ≤ s) (tnonneg : 0 ≤ t)
    (rsmall : r ≤ 1 / 2) (ssmall : s ≤ 1 / 2) (tsmall : t ≤ 1 / 2)
    (rbound : r * L ≤ 1 / 2) (sbound : s * M ≤ 1 / 2) (tbound : t * N ≤ 1 / 2)
    (diagonals : Set (SpecialLinearGroup (Fin 3) ℝ)) (index : Fin L × Fin M × Fin N) :
    realSpecialGridShift r s t index • realSpecialSiegelBox r s t diagonals ⊆
      realSpecialSiegelBox 4 4 4 diagonals := by
  rintro matrix ⟨point, member, rfl⟩
  obtain ⟨x, y, z, diagonal, rotation, hx, hy, hz, hd, hk, rfl⟩ := mem_realSpecialSiegelBox_iff.mp member
  have cx := real_grid_coordinate_bound rnonneg rbound index.1
  have cy := real_grid_coordinate_bound snonneg sbound index.2.1
  have cz := real_grid_coordinate_bound tnonneg tbound index.2.2
  apply mem_realSpecialSiegelBox_iff.mpr
  refine ⟨4 * r * index.1.val + x, 4 * s * index.2.1.val + y,
    4 * t * index.2.2.val + z + (4 * r * index.1.val) * y,
    diagonal, rotation, ?_, ?_, ?_, hd, hk, ?_⟩
  · exact (abs_add_le _ _).trans (by linarith)
  · exact (abs_add_le _ _).trans (by linarith)
  · have product_bound : |(4 * r * index.1.val) * y| ≤ 1 := by
      rw [abs_mul]
      calc
        _ ≤ 2 * (1 / 2 : ℝ) := mul_le_mul cx (hy.trans ssmall) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    exact (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans (by linarith))
  · change realSpecialGridShift r s t index *
        (realSpecialUnipotent x y z * diagonal * rotation) = _
    simp only [realSpecialGridShift, ← mul_assoc, realSpecialUnipotent_mul]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
