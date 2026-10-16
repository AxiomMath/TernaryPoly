module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cohomological.CasimirEigenvector

@[expose] public section


open GeneralEisenstein

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cohomological_minimal_rotation_weight {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) :
    ∃ weight : ℤ, ∃ vector : cusp.smooth, vector ≠ 0 ∧
      cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector ∧
      ∀ other : ℤ, ∀ otherVector : cusp.smooth, otherVector ≠ 0 →
        cuspRotationOperator cusp otherVector = (Complex.I * (other : ℂ)) • otherVector →
        weight.natAbs ≤ other.natAbs := by
  classical
  let property : ℕ → Prop := fun size => ∃ weight : ℤ, ∃ vector : cusp.smooth,
    weight.natAbs = size ∧ vector ≠ 0 ∧
      cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector
  have exists_size : ∃ size, property size := by
    obtain ⟨weight, vector, nonzero, rotation⟩ := cohomological_rotation_eigenvector_exists cohomological
    exact ⟨weight.natAbs, weight, vector, rfl, nonzero, rotation⟩
  obtain ⟨weight, vector, size, nonzero, rotation⟩ := Nat.find_spec exists_size
  refine ⟨weight, vector, nonzero, rotation, ?_⟩
  intro other otherVector other_nonzero other_rotation
  rw [size]
  exact Nat.find_min' exists_size ⟨other, otherVector, rfl, other_nonzero, other_rotation⟩

theorem cohomological_extremal_rotation_weight {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) :
    ∃ weight : ℤ, ∃ vector : cusp.smooth, vector ≠ 0 ∧
      cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector ∧
      |(weight : ℝ)| = (degree : ℝ) + 3 ∧
      (0 < weight → cuspLoweringOperator cusp vector = 0) ∧
      (weight < 0 → cuspRaisingOperator cusp vector = 0) := by
  obtain ⟨weight, vector, nonzero, rotation, minimal⟩ := cohomological_minimal_rotation_weight cohomological
  have rotation_real : cuspRotationOperator cusp vector = (Complex.I * ((weight : ℝ) : ℂ)) • vector := by
    simpa only [Complex.ofReal_intCast] using rotation
  have gap := cohomological_rotation_weight_gap cohomological weight vector nonzero rotation_real
  have casimir := cohomological_casimir_eigenvector cohomological vector
  have lowest (positive : 0 < weight) : cuspLoweringOperator cusp vector = 0 := by
    have positive_real : (0 : ℝ) ≤ weight := by exact_mod_cast positive.le
    have weight_large : (3 : ℝ) ≤ weight := by
      rw [abs_of_nonneg positive_real] at gap
      linarith [Nat.cast_nonneg (α := ℝ) degree]
    have large : (3 : ℤ) ≤ weight := by exact_mod_cast weight_large
    by_contra lowered_nonzero
    have lowered_rotation : cuspRotationOperator cusp (cuspLoweringOperator cusp vector) =
        (Complex.I * ((weight - 2 : ℤ) : ℂ)) • cuspLoweringOperator cusp vector := by
      simpa only [Int.cast_sub, Int.cast_ofNat] using cuspLowering_weight cusp weight vector rotation
    have size := minimal (weight - 2) (cuspLoweringOperator cusp vector) lowered_nonzero lowered_rotation
    have smaller : (weight - 2).natAbs < weight.natAbs := by
      rw [Int.natAbs_lt_iff_sq_lt]
      nlinarith
    exact (not_lt_of_ge size) smaller
  have highest (negative : weight < 0) : cuspRaisingOperator cusp vector = 0 := by
    have negative_real : (weight : ℝ) ≤ 0 := by exact_mod_cast negative.le
    have weight_small : (weight : ℝ) ≤ -3 := by
      rw [abs_of_nonpos negative_real] at gap
      linarith [Nat.cast_nonneg (α := ℝ) degree]
    have small : weight ≤ (-3 : ℤ) := by exact_mod_cast weight_small
    by_contra raised_nonzero
    have raised_rotation : cuspRotationOperator cusp (cuspRaisingOperator cusp vector) =
        (Complex.I * ((weight + 2 : ℤ) : ℂ)) • cuspRaisingOperator cusp vector := by
      simpa only [Int.cast_add, Int.cast_ofNat] using cuspRaising_weight cusp weight vector rotation
    have size := minimal (weight + 2) (cuspRaisingOperator cusp vector) raised_nonzero raised_rotation
    have smaller : (weight + 2).natAbs < weight.natAbs := by
      rw [Int.natAbs_lt_iff_sq_lt]
      nlinarith
    exact (not_lt_of_ge size) smaller
  refine ⟨weight, vector, nonzero, rotation, ?_, lowest, highest⟩
  rcases lt_or_ge weight 0 with negative | nonnegative
  · have negative_real : (weight : ℝ) < 0 := by exact_mod_cast negative
    have value := cuspCasimir_eq_of_raising_zero cusp weight (((degree : ℝ) + 1) * ((degree : ℝ) + 3))
      vector nonzero rotation_real casimir (highest negative)
    have factor : ((weight : ℝ) + degree + 3) * ((weight : ℝ) - degree - 1) = 0 := by nlinarith
    have second_nonzero : (weight : ℝ) - degree - 1 ≠ 0 := by
      have : (weight : ℝ) - degree - 1 < 0 := by linarith [Nat.cast_nonneg (α := ℝ) degree]
      exact this.ne
    rw [abs_of_neg negative_real]
    linarith [(mul_eq_zero.mp factor).resolve_right second_nonzero]
  · have nonnegative_real : (0 : ℝ) ≤ weight := by exact_mod_cast nonnegative
    rw [abs_of_nonneg nonnegative_real] at gap ⊢
    have positive_real : (0 : ℝ) < weight := by linarith [Nat.cast_nonneg (α := ℝ) degree]
    have positive : 0 < weight := by exact_mod_cast positive_real
    have value := cuspCasimir_eq_of_lowering_zero cusp weight (((degree : ℝ) + 1) * ((degree : ℝ) + 3))
      vector nonzero rotation_real casimir (lowest positive)
    have factor : ((weight : ℝ) - degree - 3) * ((weight : ℝ) + degree + 1) = 0 := by nlinarith
    have second_nonzero : (weight : ℝ) + degree + 1 ≠ 0 := by positivity
    linarith [(mul_eq_zero.mp factor).resolve_right second_nonzero]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
