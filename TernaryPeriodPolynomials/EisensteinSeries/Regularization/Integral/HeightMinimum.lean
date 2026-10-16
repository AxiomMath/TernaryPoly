module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.TransformedRowLattice
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.RowTranslation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def integralRealGroup : IntegralGL3 →* RealGL3 :=
  GeneralLinearGroup.map (Int.castRingHom ℝ)

theorem integralRealGroup_abs_det (matrix : IntegralGL3) :
    |(integralRealGroup matrix).val.det| = 1 := by
  change |(GeneralLinearGroup.det (integralRealGroup matrix)).val| = 1
  rw [integralRealGroup, GeneralLinearGroup.map_det]
  rcases Int.units_eq_one_or (GeneralLinearGroup.det matrix) with positive | negative
  · rw [positive]
    norm_num
  · rw [negative]
    norm_num

noncomputable def realRowHeight (row : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (row 0 ^ 2 + row 1 ^ 2 + row 2 ^ 2)

theorem realRowHeight_last (matrix : RealGL3) : realRowHeight (matrix.val 2) = realPlaneHeight matrix := rfl

noncomputable def integralTranslatedLastRow (matrix : RealGL3) (integral : IntegralGL3) :
    transformedRowLattice matrix := transformedRowEquiv matrix (integral.val 2)

theorem integralTranslatedLastRow_val (matrix : RealGL3) (integral : IntegralGL3) :
    (integralTranslatedLastRow matrix integral).val = (integralRealGroup integral * matrix).val 2 := by
  rw [integralTranslatedLastRow, transformedRowEquiv_val]
  rfl

theorem integralTranslatedLastRow_height (matrix : RealGL3) (integral : IntegralGL3) :
    realRowHeight (integralTranslatedLastRow matrix integral).val =
      realPlaneHeight (integralRealGroup integral * matrix) := by
  rw [integralTranslatedLastRow_val, realRowHeight_last]

theorem integral_plane_height_minimum (matrix : RealGL3) (matrices : Set IntegralGL3)
    (nonempty : matrices.Nonempty) :
    ∃ integral ∈ matrices, ∀ other ∈ matrices,
      realPlaneHeight (integralRealGroup integral * matrix) ≤
        realPlaneHeight (integralRealGroup other * matrix) := by
  classical
  obtain ⟨base, base_member⟩ := nonempty
  let bound := realPlaneHeight (integralRealGroup base * matrix)
  let candidates : Set (transformedRowLattice matrix) :=
    {row | ∃ integral ∈ matrices, integralTranslatedLastRow matrix integral = row ∧
      realPlaneHeight (integralRealGroup integral * matrix) ≤ bound}
  have finite_candidates : candidates.Finite :=
    (transformedRowLattice_finite_ball matrix (bound + 1)).subset (by
      intro row member
      obtain ⟨integral, _, equality, bounded⟩ := member
      rw [← equality]
      change ‖(integralTranslatedLastRow matrix integral).val‖ < bound + 1
      rw [integralTranslatedLastRow_val]
      exact (real_row_norm_le_height _).trans_lt (bounded.trans_lt (lt_add_one bound)))
  have nonempty_candidates : candidates.Nonempty :=
    ⟨integralTranslatedLastRow matrix base, base, base_member, rfl, le_rfl⟩
  obtain ⟨row, row_member, minimal⟩ := Set.exists_min_image candidates
    (fun row => realRowHeight row.val) finite_candidates nonempty_candidates
  obtain ⟨integral, integral_member, row_eq, integral_bound⟩ := row_member
  refine ⟨integral, integral_member, ?_⟩
  intro other other_member
  by_cases other_bound : realPlaneHeight (integralRealGroup other * matrix) ≤ bound
  · have comparison := minimal (integralTranslatedLastRow matrix other)
      ⟨other, other_member, rfl, other_bound⟩
    rw [← row_eq, integralTranslatedLastRow_height, integralTranslatedLastRow_height] at comparison
    exact comparison
  · exact integral_bound.trans (le_of_not_ge other_bound)

theorem integral_plane_height_minimum_univ (matrix : RealGL3) :
    ∃ integral : IntegralGL3, ∀ other : IntegralGL3,
      realPlaneHeight (integralRealGroup integral * matrix) ≤
        realPlaneHeight (integralRealGroup other * matrix) := by
  obtain ⟨integral, _, minimal⟩ := integral_plane_height_minimum matrix Set.univ Set.univ_nonempty
  exact ⟨integral, fun other => minimal other (Set.mem_univ other)⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
