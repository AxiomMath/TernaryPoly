module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RotationEigenvectors

@[expose] public section


open GeneralEisenstein

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem cohomological_smooth_projection_zero {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℤ)
    (forbidden : |(weight : ℝ)| < (degree : ℝ) + 3) (vector : cusp.smooth) :
    cuspSmoothRotationProjection cusp weight vector = 0 := by
  by_contra nonzero
  exact (not_le.mpr forbidden) (cohomological_smooth_projection_gap cohomological weight vector nonzero)

theorem cohomological_hilbert_projection_zero {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℤ)
    (forbidden : |(weight : ℝ)| < (degree : ℝ) + 3) (vector : cusp.H) :
    cuspRotationProjection cusp weight vector = 0 := by
  have closed : IsClosed {vector : cusp.H | cuspRotationProjection cusp weight vector = 0} :=
    isClosed_eq (cuspRotationProjection cusp weight).continuous continuous_const
  have smooth_zero : (cusp.smooth : Set cusp.H) ⊆ {vector | cuspRotationProjection cusp weight vector = 0} := by
    intro vector member
    exact congrArg Subtype.val (cohomological_smooth_projection_zero cohomological weight forbidden ⟨vector, member⟩)
  exact closure_minimal smooth_zero closed ((cohomological_smooth_dense cohomological) vector)

theorem cohomological_rotation_eigenvector_exists {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) :
    ∃ weight : ℤ, ∃ vector : cusp.smooth, vector ≠ 0 ∧
      cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector := by
  obtain ⟨vector, member, nonzero⟩ := (cusp.smooth.ne_bot_iff).mp (cohomological_smooth_ne_bot cohomological)
  have smooth_nonzero : (⟨vector, member⟩ : cusp.smooth) ≠ 0 := by
    intro zero
    exact nonzero (congrArg Subtype.val zero)
  obtain ⟨weight, projected_nonzero⟩ := cuspSmoothRotationProjection_exists_nonzero cusp ⟨vector, member⟩ smooth_nonzero
  exact ⟨weight, cuspSmoothRotationProjection cusp weight ⟨vector, member⟩, projected_nonzero,
    cuspSmoothRotationProjection_eigenvector cusp weight ⟨vector, member⟩⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
