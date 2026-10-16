module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationCharacter

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def cuspRaisingSequence (cusp : CuspidalRepresentation) (vector : cusp.smooth) : ℕ → cusp.smooth
  | 0 => vector
  | step + 1 => cuspRaisingOperator cusp (cuspRaisingSequence cusp vector step)

theorem cuspRaisingSequence_weight (cusp : CuspidalRepresentation) (weight : ℂ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * weight) • vector) (step : ℕ) :
    cuspRotationOperator cusp (cuspRaisingSequence cusp vector step) =
      (Complex.I * (weight + 2 * (step : ℂ))) • cuspRaisingSequence cusp vector step := by
  induction step with
  | zero => simpa only [cuspRaisingSequence, Nat.cast_zero, mul_zero, add_zero] using rotation
  | succ step induction =>
    have shifted := cuspRaising_weight cusp (weight + 2 * (step : ℂ)) (cuspRaisingSequence cusp vector step) induction
    simpa only [cuspRaisingSequence, Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_assoc] using shifted

theorem cuspRaisingSequence_ne_zero (cusp : CuspidalRepresentation) (weight : ℝ) (positive : 0 < weight)
    (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector) (step : ℕ) :
    cuspRaisingSequence cusp vector step ≠ 0 := by
  induction step with
  | zero => exact nonzero
  | succ step induction =>
    apply cuspRaising_ne_zero_of_positive_weight cusp (weight + 2 * (step : ℝ))
      (by positivity) (cuspRaisingSequence cusp vector step) induction
    simpa only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast] using
      cuspRaisingSequence_weight cusp weight vector rotation step

theorem cohomological_positive_ladder_exists {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (step : ℕ) :
    ∃ vector : cusp.smooth, vector ≠ 0 ∧
      cuspRotationOperator cusp vector = (Complex.I * ((degree : ℂ) + 3 + 2 * step)) • vector := by
  obtain ⟨vector, nonzero, rotation, _⟩ := cohomological_lowest_weight_vector cohomological
  have rotation_real : cuspRotationOperator cusp vector =
      (Complex.I * (↑((degree : ℝ) + 3) : ℂ)) • vector := by
    simpa only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat] using rotation
  exact ⟨cuspRaisingSequence cusp vector step,
    cuspRaisingSequence_ne_zero cusp ((degree : ℝ) + 3) (by positivity) vector nonzero rotation_real step,
    cuspRaisingSequence_weight cusp ((degree : ℂ) + 3) vector rotation step⟩

theorem cohomological_negative_ladder_exists {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (step : ℕ) :
    ∃ vector : cusp.smooth, vector ≠ 0 ∧
      cuspRotationOperator cusp vector = (Complex.I * (-((degree : ℂ) + 3 + 2 * step))) • vector := by
  obtain ⟨vector, nonzero, rotation⟩ := cohomological_positive_ladder_exists cohomological step
  refine ⟨cuspSmoothAction cusp (atInfinity binaryReflection) vector,
    cuspSmoothAction_ne_zero cusp _ vector nonzero, ?_⟩
  rw [cuspRotation_reflection, rotation, map_smul, ← neg_smul, mul_neg]

theorem cuspRotationProjection_ne_zero_of_eigenvector (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector) :
    cuspRotationProjection cusp weight ≠ 0 := by
  intro zero
  have projected := cuspRotationProjection_of_eigenvector cusp weight weight vector rotation
  rw [zero, zero_apply, ite_eq_left rfl] at projected
  exact nonzero (Subtype.ext projected.symm)

theorem cohomological_hilbert_projection_ne_zero_iff {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℤ) :
    cuspRotationProjection cusp weight ≠ 0 ↔ ∃ step : ℕ, weight.natAbs = degree + 3 + 2 * step := by
  constructor
  · intro nonzero
    by_contra forbidden
    apply nonzero
    ext vector
    exact cohomological_hilbert_projection_spectrum cohomological weight forbidden vector
  · rintro ⟨step, size⟩
    have absolute : |weight| = (degree : ℤ) + 3 + 2 * step := by
      rw [← Int.natCast_natAbs, size]
      push_cast
      rfl
    rcases le_total 0 weight with nonnegative | nonpositive
    · rw [abs_of_nonneg nonnegative] at absolute
      obtain ⟨vector, nonzero, rotation⟩ := cohomological_positive_ladder_exists cohomological step
      apply cuspRotationProjection_ne_zero_of_eigenvector cusp weight vector nonzero
      simpa only [absolute, Int.cast_add, Int.cast_natCast, Int.cast_ofNat, Int.cast_mul] using rotation
    · rw [abs_of_nonpos nonpositive] at absolute
      have value : weight = -((degree : ℤ) + 3 + 2 * step) := by omega
      obtain ⟨vector, nonzero, rotation⟩ := cohomological_negative_ladder_exists cohomological step
      apply cuspRotationProjection_ne_zero_of_eigenvector cusp weight vector nonzero
      simpa only [value, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_ofNat, Int.cast_mul] using rotation

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
