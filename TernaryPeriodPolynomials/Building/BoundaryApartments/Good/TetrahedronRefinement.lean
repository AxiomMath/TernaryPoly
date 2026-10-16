module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.VectorCoordinates

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

theorem comparisonTetrahedronHeights_le_one (weights other_weights : Fin 3 → ℚ)
    (small : ∀ index, |weights index| < 1)
    (pairs : ∀ first second, first ≠ second → |weights first| + |weights second| ≤ 1)
    (other_bound : ∀ index, |other_weights index| ≤ 1) (pivot : Fin 3) (index : Fin 4) :
    comparisonTetrahedronHeights weights other_weights pivot index ≤ 1 := by
  fin_cases index
  · exact other_bound pivot
  · exact (small pivot).le
  · exact comparisonFaceHeights_le_one weights other_weights pairs other_bound pivot _
  · exact comparisonFaceHeights_le_one weights other_weights pairs other_bound pivot _

theorem comparisonTetrahedron_top_count (weights other_weights : Fin 3 → ℚ)
    (small : ∀ index, |weights index| < 1) (pivot : Fin 3) :
    (Finset.univ.filter (fun index => comparisonTetrahedronHeights weights other_weights pivot index = 1)).card =
      (Finset.univ.filter (fun index => comparisonFaceHeights weights other_weights pivot index = 1)).card := by
  classical
  have different (index : Fin 3) : |weights index| ≠ 1 := (small index).ne
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_four, Fin.sum_univ_three]
  fin_cases pivot <;>
    simp [comparisonTetrahedronHeights, comparisonFaceHeights, different] <;> ac_rfl

theorem nat_ratio_le_iff (height bound : ℕ) (ratio : ℚ) (positive : 0 < bound)
    (formula : (height : ℚ) = ratio * bound) : height ≤ bound ↔ ratio ≤ 1 := by
  have cast_positive : (0 : ℚ) < bound := by exact_mod_cast positive
  constructor
  · intro le
    have cast_le : (height : ℚ) ≤ bound := by exact_mod_cast le
    nlinarith
  · intro le
    have cast_le : (height : ℚ) ≤ bound := by nlinarith
    exact_mod_cast cast_le

theorem nat_ratio_eq_iff (height bound : ℕ) (ratio : ℚ) (positive : 0 < bound)
    (formula : (height : ℚ) = ratio * bound) : height = bound ↔ ratio = 1 := by
  have cast_positive : (0 : ℚ) < bound := by exact_mod_cast positive
  constructor
  · intro eq
    have cast_eq : (height : ℚ) = bound := by exact_mod_cast eq
    nlinarith
  · intro eq
    have cast_eq : (height : ℚ) = bound := by rw [formula, eq, one_mul]
    exact_mod_cast cast_eq

theorem goodTetrahedron_refine_front (bound : ℕ) (a b c d : NormalizedGoodVector)
    (large : 1 < bound) (bounded : TetrahedronBound goodTripleHeight bound (a, b, c, d))
    (attained : goodTripleHeight (b, c, d) = bound) (pivot : Fin 3) :
    TetrahedronBound goodTripleHeight bound
        (tetrahedronCone (goodTripleReducer (b, c, d)) (a, b, c, d) pivot.succ) ∧
      tetrahedronTopCount goodTripleHeight bound
        (tetrahedronCone (goodTripleReducer (b, c, d)) (a, b, c, d) pivot.succ) <
      tetrahedronTopCount goodTripleHeight bound (a, b, c, d) := by
  classical
  have base_large : 1 < goodTripleHeight (b, c, d) := attained ▸ large
  have nonzero : ((goodTripleMatrix (b, c, d)).map (Int.castRingHom ℚ)).det ≠ 0 := by
    intro zero
    have cast_height := goodTripleHeight_cast (b, c, d)
    rw [attained, zero, abs_zero] at cast_height
    have : bound = 0 := by exact_mod_cast cast_height
    omega
  let frame := GeneralLinearGroup.mkOfDetNeZero
    ((goodTripleMatrix (b, c, d)).map (Int.castRingHom ℚ)) nonzero
  have determinant : |frame.val.det| = (bound : ℚ) := by
    rw [← attained]
    exact (goodTripleHeight_cast (b, c, d)).symm
  obtain ⟨weights, combination, small, pairs⟩ := goodTripleReducer_spec (b, c, d) base_large
  have coordinates := goodVectorCoordinates_of_combination frame (goodTripleReducer (b, c, d)) weights combination
  let other_weights := goodVectorCoordinates frame a
  have old_formula (index : Fin 4) :
      (goodTripleHeight (tetrahedronFace (a, b, c, d) index) : ℚ) =
        ![1, |other_weights 0|, |other_weights 1|, |other_weights 2|] index * bound := by
    rw [← determinant]
    exact goodTetrahedron_coordinate_heights frame a b c d rfl other_weights rfl index
  have old_le (index : Fin 4) : ![1, |other_weights 0|, |other_weights 1|, |other_weights 2|] index ≤ 1 :=
    (nat_ratio_le_iff _ bound _ (by omega) (old_formula index)).mp (bounded index)
  have old_eq (index : Fin 4) : goodTripleHeight (tetrahedronFace (a, b, c, d) index) = bound ↔
      ![1, |other_weights 0|, |other_weights 1|, |other_weights 2|] index = 1 :=
    nat_ratio_eq_iff _ bound _ (by omega) (old_formula index)
  have other_bound (index : Fin 3) : |other_weights index| ≤ 1 := by
    fin_cases index
    · exact old_le 1
    · exact old_le 2
    · exact old_le 3
  have new_formula (index : Fin 4) :
      (goodTripleHeight (tetrahedronFace
        (tetrahedronCone (goodTripleReducer (b, c, d)) (a, b, c, d) pivot.succ) index) : ℚ) =
        comparisonTetrahedronHeights weights other_weights pivot index * bound := by
    rw [← determinant]
    exact goodTetrahedron_cone_coordinate_heights frame a b c d (goodTripleReducer (b, c, d))
      rfl weights other_weights coordinates rfl pivot index
  have new_eq (index : Fin 4) : goodTripleHeight (tetrahedronFace
      (tetrahedronCone (goodTripleReducer (b, c, d)) (a, b, c, d) pivot.succ) index) = bound ↔
        comparisonTetrahedronHeights weights other_weights pivot index = 1 :=
    nat_ratio_eq_iff _ bound _ (by omega) (new_formula index)
  constructor
  · intro index
    exact (nat_ratio_le_iff _ bound _ (by omega) (new_formula index)).mpr
      (comparisonTetrahedronHeights_le_one weights other_weights small pairs other_bound pivot index)
  · have old_count : tetrahedronTopCount goodTripleHeight bound (a, b, c, d) =
        1 + (Finset.univ.filter (fun index => |other_weights index| = 1)).card := by
      unfold tetrahedronTopCount
      simp only [old_eq]
      rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_four, Fin.sum_univ_three]
      simp
      ac_rfl
    have new_count : tetrahedronTopCount goodTripleHeight bound
        (tetrahedronCone (goodTripleReducer (b, c, d)) (a, b, c, d) pivot.succ) =
        (Finset.univ.filter (fun index => comparisonFaceHeights weights other_weights pivot index = 1)).card := by
      unfold tetrahedronTopCount
      simp only [new_eq]
      exact comparisonTetrahedron_top_count weights other_weights small pivot
    rw [old_count, new_count]
    exact comparison_top_face_count_lt weights other_weights small pairs other_bound pivot

theorem goodTetrahedron_refine (bound : ℕ) (tetrahedron : OrderedTetrahedron NormalizedGoodVector)
    (large : 1 < bound) (bounded : TetrahedronBound goodTripleHeight bound tetrahedron)
    (attained : ∃ index, goodTripleHeight (tetrahedronFace tetrahedron index) = bound) :
    ∃ pivot : Fin 4, ∃ vertex : NormalizedGoodVector,
      goodTripleHeight (tetrahedronFace tetrahedron pivot) = bound ∧
      vertex = goodTripleReducer (tetrahedronFace tetrahedron pivot) ∧
      ∀ index, index ≠ pivot →
        TetrahedronBound goodTripleHeight bound (tetrahedronCone vertex tetrahedron index) ∧
        tetrahedronTopCount goodTripleHeight bound (tetrahedronCone vertex tetrahedron index) <
          tetrahedronTopCount goodTripleHeight bound tetrahedron := by
  obtain ⟨pivot, height⟩ := attained
  let vertex := goodTripleReducer (tetrahedronFace tetrahedron pivot)
  refine ⟨pivot, vertex, height, rfl, ?_⟩
  let moved := tetrahedronMoveFront tetrahedron pivot
  have same_parent := goodTetrahedron_move_front tetrahedron pivot
  have moved_bound : TetrahedronBound goodTripleHeight bound moved := (same_parent bound).1.mpr bounded
  have base : tetrahedronFace moved 0 = tetrahedronFace tetrahedron pivot := rfl
  have moved_height : goodTripleHeight (tetrahedronFace moved 0) = bound := base ▸ height
  have children (index : Fin 4) (nonzero : index ≠ 0) :
      TetrahedronBound goodTripleHeight bound (tetrahedronCone vertex moved index) ∧
      tetrahedronTopCount goodTripleHeight bound (tetrahedronCone vertex moved index) <
        tetrahedronTopCount goodTripleHeight bound moved := by
    have vertex_eq : vertex = goodTripleReducer (moved.2.1, moved.2.2.1, moved.2.2.2) := rfl
    rw [vertex_eq]
    fin_cases index
    · exact (nonzero rfl).elim
    · exact goodTetrahedron_refine_front bound moved.1 moved.2.1 moved.2.2.1 moved.2.2.2
        large moved_bound moved_height 0
    · exact goodTetrahedron_refine_front bound moved.1 moved.2.1 moved.2.2.1 moved.2.2.2
        large moved_bound moved_height 1
    · exact goodTetrahedron_refine_front bound moved.1 moved.2.1 moved.2.2.1 moved.2.2.2
        large moved_bound moved_height 2
  intro index different
  obtain ⟨next, nonzero, same_child⟩ := goodTetrahedron_cone_move_front tetrahedron vertex pivot index different
  obtain ⟨child_bound, child_count⟩ := children next nonzero
  refine ⟨(same_child bound).1.mpr child_bound, ?_⟩
  rw [(same_child bound).2, ← (same_parent bound).2]
  exact child_count

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
