module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.RoundedGoodReduction

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

def comparisonFaceHeights (weights other_weights : Fin 3 → ℚ) (pivot index : Fin 3) : ℚ :=
  if index = pivot then |other_weights pivot| else
    |weights pivot * other_weights index - weights index * other_weights pivot|

theorem comparisonFaceHeights_le_one (weights other_weights : Fin 3 → ℚ)
    (pair_bound : ∀ first second, first ≠ second → |weights first| + |weights second| ≤ 1)
    (other_bound : ∀ index, |other_weights index| ≤ 1) (pivot index : Fin 3) :
    comparisonFaceHeights weights other_weights pivot index ≤ 1 := by
  by_cases same : index = pivot
  · simp only [comparisonFaceHeights, ite_eq_left same]
    exact other_bound pivot
  · simp only [comparisonFaceHeights, ite_eq_right same]
    exact pairwise_minor_le_one _ _ _ _ (pair_bound pivot index (Ne.symm same))
      (other_bound pivot) (other_bound index)

theorem comparisonFaceHeights_eq_one (weights other_weights : Fin 3 → ℚ)
    (small : ∀ index, |weights index| < 1)
    (pair_bound : ∀ first second, first ≠ second → |weights first| + |weights second| ≤ 1)
    (other_bound : ∀ index, |other_weights index| ≤ 1) (pivot index : Fin 3)
    (equality : comparisonFaceHeights weights other_weights pivot index = 1) :
    |other_weights pivot| = 1 ∧ |other_weights index| = 1 := by
  by_cases same : index = pivot
  · subst index
    simp only [comparisonFaceHeights] at equality
    exact ⟨equality, equality⟩
  · simp only [comparisonFaceHeights, ite_eq_right same] at equality
    exact (pairwise_minor_abs_eq_one _ _ _ _ (small pivot) (small index)
      (pair_bound pivot index (Ne.symm same)) (other_bound pivot) (other_bound index) equality).imp_right
        (fun h => h.1)

/-- Among the three remaining faces of a coned tetrahedron, every face
attaining the old determinant bound corresponds to a distinct old face
attaining that bound. The fourth new face is strictly smaller. -/
theorem comparison_top_face_count_lt (weights other_weights : Fin 3 → ℚ)
    (small : ∀ index, |weights index| < 1)
    (pair_bound : ∀ first second, first ≠ second → |weights first| + |weights second| ≤ 1)
    (other_bound : ∀ index, |other_weights index| ≤ 1) (pivot : Fin 3) :
    (Finset.univ.filter (fun index => comparisonFaceHeights weights other_weights pivot index = 1)).card <
      1 + (Finset.univ.filter (fun index => |other_weights index| = 1)).card := by
  have subset : Finset.univ.filter (fun index => comparisonFaceHeights weights other_weights pivot index = 1) ⊆
      Finset.univ.filter (fun index => |other_weights index| = 1) := by
    intro index member
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      (comparisonFaceHeights_eq_one weights other_weights small pair_bound other_bound pivot index
        (Finset.mem_filter.mp member).2).2⟩
  have bound := Finset.card_le_card subset
  omega

theorem comparisonFaceHeights_lt_one_of_pivot_lt (weights other_weights : Fin 3 → ℚ)
    (small : ∀ index, |weights index| < 1)
    (pair_bound : ∀ first second, first ≠ second → |weights first| + |weights second| ≤ 1)
    (other_bound : ∀ index, |other_weights index| ≤ 1) (pivot : Fin 3)
    (pivot_small : |other_weights pivot| < 1) (index : Fin 3) :
    comparisonFaceHeights weights other_weights pivot index < 1 := by
  apply lt_of_le_of_ne (comparisonFaceHeights_le_one weights other_weights pair_bound other_bound pivot index)
  intro equality
  exact pivot_small.ne ((comparisonFaceHeights_eq_one weights other_weights small pair_bound other_bound
    pivot index equality).1)

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
