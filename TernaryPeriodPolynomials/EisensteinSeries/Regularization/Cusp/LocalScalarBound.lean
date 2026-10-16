module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.CompactBanachLift
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ContinuousMapLocalAnalytic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix Filter
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspCenteredMatrixOrbit_zero (cusp : CuspidalRepresentation) (vector : cusp.H) :
    cuspCenteredMatrixOrbit cusp vector 0 = vector := by
  have matrix_one : invertibleMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    simpa only [Units.val_one] using invertibleMatrix_val (1 : BinaryRealGL)
  simp only [cuspCenteredMatrixOrbit, add_zero, matrix_one, binary_atInfinity_one,
    map_one, Module.End.one_apply]

theorem cusp_family_local_scalar_bound
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [ProperSpace D]
    {cusp : CuspidalRepresentation} {degree : ℕ} (cohomological : Cohomological cusp degree)
    (family : D → cuspFiniteFixedSubmodule cusp binaryPrincipalLevel) (center : D)
    (analytic : AnalyticAt ℝ
      (fun input : Matrix (Fin 2) (Fin 2) ℝ × D =>
        cuspCenteredMatrixOrbit cusp (family input.2).val.val input.1) (0, center)) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ᶠ point in nhds center,
      ‖cuspBoundedRealization cusp (family point).val‖ ≤ bound := by
  obtain ⟨radius, positive, orbit, orbit_analytic, orbit_spec⟩ :=
    analyticAt_continuousMap_local analytic
  have continuous : Continuous
      (fun point : Metric.closedBall center radius => (family point.val).val.val) := by
    apply (orbit 0).continuous.congr
    intro point
    exact (orbit_spec.self_of_nhds point).trans (cuspCenteredMatrixOrbit_zero cusp _)
  obtain ⟨bound, nonnegative, bounded⟩ := cusp_compact_family_scalar_bound cohomological
    (fun point : Metric.closedBall center radius => family point.val)
    continuous orbit orbit_analytic orbit_spec
  refine ⟨bound, nonnegative, ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds center positive] with point inside
  exact bounded ⟨point, inside⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
