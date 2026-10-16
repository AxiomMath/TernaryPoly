module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DiskOrbit

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem hasFPowerSeriesAt_continuousLinearMap
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {function : ℂ → E} {series : FormalMultilinearSeries ℂ ℂ E}
    (expansion : HasFPowerSeriesAt function series 0) (operator : E →L[ℂ] F) :
    HasFPowerSeriesAt (fun point => operator (function point))
      (operator.compFormalMultilinearSeries series) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [hasFPowerSeriesAt_iff.mp expansion] with point summation
  have mapped := operator.hasSum summation
  simpa only [zero_add, map_smul, FormalMultilinearSeries.coeff,
    ContinuousLinearMap.compFormalMultilinearSeries_apply'] using mapped

theorem powerSeries_coeff_covariance
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {function : ℂ → E} {series : FormalMultilinearSeries ℂ ℂ E}
    (expansion : HasFPowerSeriesAt function series 0) (operator : E →L[ℂ] E)
    (factor scale : ℂ)
    (covariance : ∀ᶠ point : ℂ in nhds 0,
      operator (function point) = factor • function (scale * point)) (index : ℕ) :
    operator (series.coeff index) = (factor * scale ^ index) • series.coeff index := by
  let scaling : ℂ →L[ℂ] ℂ := scale • ContinuousLinearMap.id ℂ ℂ
  have scaled : HasFPowerSeriesAt (function ∘ scaling) (series.compContinuousLinearMap scaling) 0 := by
    apply HasFPowerSeriesAt.compContinuousLinearMap
    simpa only [map_zero] using expansion
  have equality := (hasFPowerSeriesAt_continuousLinearMap expansion operator).eq_formalMultilinearSeries_of_eventually (scaled.const_smul (c := factor)) covariance
  have coefficient := congrArg (fun coefficients : FormalMultilinearSeries ℂ ℂ E =>
    coefficients.coeff index) equality
  change operator (series.coeff index) = factor • (series index) (fun _ => scale * 1) at coefficient
  simpa only [mul_one, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_smul] using coefficient

theorem cuspDiskTaylorSeries_weight (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ (2 * halfWeight) • vector)
    (series : FormalMultilinearSeries ℂ ℂ cusp.H)
    (expansion : HasFPowerSeriesAt (cuspDiskOrbit cusp halfWeight vector) series 0)
    (index : ℕ) (angle : Circle) :
    cusp.π (atInfinity (binaryRotations angle)) (series.coeff index) =
      (angle : ℂ) ^ (2 * halfWeight - 2 * (index : ℤ)) • series.coeff index := by
  have equation := powerSeries_coeff_covariance expansion
    (cuspUnitaryOperator cusp (atInfinity (binaryRotations angle)))
    ((angle : ℂ) ^ (2 * halfWeight)) ((angle : ℂ) ^ (-2 : ℤ)) (by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with point inside
      exact cuspDiskOrbit_rotation cusp halfWeight vector rotation angle point
        (by simpa only [Metric.mem_ball, dist_zero_right] using inside)) index
  change cusp.π (atInfinity (binaryRotations angle)) (series.coeff index) = _ at equation
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ (Circle.coe_ne_zero angle)] at equation
  convert equation using 1
  congr 2

theorem cuspDiskOrbit_exists_taylor (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ (2 * halfWeight) • vector)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet) :
    ∃ series : FormalMultilinearSeries ℂ ℂ cusp.H,
      HasFPowerSeriesAt (cuspDiskOrbit cusp halfWeight vector) series 0 ∧
      series.coeff 0 = vector ∧
      ∀ index : ℕ, ∀ angle : Circle,
        cusp.π (atInfinity (binaryRotations angle)) (series.coeff index) =
          (angle : ℂ) ^ (2 * halfWeight - 2 * (index : ℤ)) • series.coeff index := by
  obtain ⟨series, expansion⟩ := (cuspDiskOrbit_holomorphic cusp halfWeight vector holomorphic).analyticOnNhd Metric.isOpen_ball 0 (by simp)
  refine ⟨series, expansion, ?_, cuspDiskTaylorSeries_weight cusp halfWeight vector rotation series expansion⟩
  change (series 0) (fun _ => 1) = vector
  rw [expansion.coeff_zero, cuspDiskOrbit_zero]

theorem cuspDiskTaylorSeries_spherical (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H) (spherical : vector ∈ cuspSphericalValues cusp)
    (series : FormalMultilinearSeries ℂ ℂ cusp.H)
    (expansion : HasFPowerSeriesAt (cuspDiskOrbit cusp halfWeight vector) series 0)
    (index : ℕ) : series.coeff index ∈ cuspSphericalValues cusp := by
  apply (cuspSphericalProjection_eq_self_iff cusp _).mp
  have coefficient := powerSeries_coeff_covariance expansion (cuspSphericalProjection cusp) 1 1 (by
    filter_upwards [] with point
    simpa only [one_mul, one_smul] using (cuspSphericalProjection_eq_self_iff cusp _).mpr
      (cuspDiskOrbit_spherical cusp halfWeight vector spherical point)) index
  simpa only [one_pow, one_mul, one_smul] using coefficient

end TernaryPeriodPolynomials.SphericalDetection.Helpers
