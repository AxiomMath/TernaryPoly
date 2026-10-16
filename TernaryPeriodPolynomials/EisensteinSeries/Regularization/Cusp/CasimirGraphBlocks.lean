module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.WeakCasimirGraph

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

noncomputable def cuspCasimirGraphFirst (cusp : CuspidalRepresentation) : cusp.H →L[ℂ] cusp.H :=
  (cuspPairFirst cusp).comp ((cuspWeakCasimirGraph cusp).starProjection.comp (cuspPairInclusion cusp))

noncomputable def cuspCasimirGraphSecond (cusp : CuspidalRepresentation) : cusp.H →L[ℂ] cusp.H :=
  (cuspPairSecond cusp).comp ((cuspWeakCasimirGraph cusp).starProjection.comp (cuspPairInclusion cusp))

theorem cuspCasimirGraphFirst_selfAdjoint (cusp : CuspidalRepresentation) :
    IsSelfAdjoint (cuspCasimirGraphFirst cusp) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  change inner ℂ (cuspPairFirst cusp ((cuspWeakCasimirGraph cusp).starProjection (cuspPairInclusion cusp first)))
      second = inner ℂ first
        (cuspPairFirst cusp ((cuspWeakCasimirGraph cusp).starProjection (cuspPairInclusion cusp second)))
  rw [cuspPairFirst_inner, cuspPairInclusion_inner]
  exact (isSelfAdjoint_starProjection (cuspWeakCasimirGraph cusp)).isSymmetric _ _

theorem cuspCasimirGraphFirst_commuting (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    Commute (cuspCasimirGraphFirst cusp) (cuspUnitaryAction cusp matrix).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro vector
  change cuspPairFirst cusp ((cuspWeakCasimirGraph cusp).starProjection
      (cuspPairInclusion cusp (cusp.π matrix vector))) =
    cusp.π matrix (cuspPairFirst cusp ((cuspWeakCasimirGraph cusp).starProjection (cuspPairInclusion cusp vector)))
  rw [cuspPairInclusion_covariance, cuspWeakCasimirGraph_projection_covariance]
  rfl

theorem cuspCasimirGraphSecond_commuting (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL) :
    Commute (cuspCasimirGraphSecond cusp) (cuspUnitaryAction cusp matrix).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro vector
  change cuspPairSecond cusp ((cuspWeakCasimirGraph cusp).starProjection
      (cuspPairInclusion cusp (cusp.π matrix vector))) =
    cusp.π matrix (cuspPairSecond cusp ((cuspWeakCasimirGraph cusp).starProjection (cuspPairInclusion cusp vector)))
  rw [cuspPairInclusion_covariance, cuspWeakCasimirGraph_projection_covariance]
  rfl

theorem cuspCasimirGraphFirst_ne_zero {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) : cuspCasimirGraphFirst cusp ≠ 0 := by
  intro zero
  apply cohomological_smooth_ne_bot cohomological
  apply eq_bot_iff.mpr
  intro vector member
  change vector = 0
  let smoothVector : cusp.smooth := ⟨vector, member⟩
  have first_zero :
      ((cuspWeakCasimirGraph cusp).starProjection (cuspPairInclusion cusp vector)).ofLp.1 = 0 :=
    congrArg (fun operator : cusp.H →L[ℂ] cusp.H => operator vector) zero
  have projection_zero := cuspWeakCasimirGraph_vertical_zero cohomological
    ((cuspWeakCasimirGraph cusp).starProjection_apply_mem (cuspPairInclusion cusp vector)) first_zero
  have orthogonal := Submodule.starProjection_inner_eq_zero (cuspPairInclusion cusp vector)
    (WithLp.toLp 2 (vector, (cuspCasimirOperator cusp smoothVector).val))
    (cuspWeakCasimirGraph_contains cusp smoothVector)
  rw [projection_zero, sub_zero, WithLp.prod_inner_apply] at orthogonal
  change inner ℂ vector vector + inner ℂ 0 (cuspCasimirOperator cusp smoothVector).val = 0 at orthogonal
  rw [inner_zero_left, add_zero] at orthogonal
  exact inner_self_eq_zero.mp orthogonal

theorem cuspCasimirGraphFirst_scalar {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) :
    ∃ scalar : ℝ, scalar ≠ 0 ∧ cuspCasimirGraphFirst cusp = (scalar : ℂ) • (1 : cusp.H →L[ℂ] cusp.H) := by
  obtain ⟨scalar, equality⟩ := cusp_commuting_selfAdjoint_scalar cusp (cuspCasimirGraphFirst cusp)
    (cuspCasimirGraphFirst_selfAdjoint cusp) (cuspCasimirGraphFirst_commuting cusp)
  refine ⟨scalar, ?_, equality⟩
  intro zero
  apply cuspCasimirGraphFirst_ne_zero cohomological
  simpa only [zero, Complex.ofReal_zero, zero_smul] using equality

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
