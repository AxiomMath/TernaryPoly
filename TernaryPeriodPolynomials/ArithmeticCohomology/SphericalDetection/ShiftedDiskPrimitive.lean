module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.DiskScalarCoefficients

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspShiftedDiskOrbit (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.H)
    (point : ℂ) : cusp.H := point • cuspDiskOrbit cusp halfWeight vector point

theorem cuspShiftedDiskOrbit_holomorphic (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet) :
    DifferentiableOn ℂ (cuspShiftedDiskOrbit cusp halfWeight vector) (Metric.ball 0 1) :=
  differentiableOn_id.smul (cuspDiskOrbit_holomorphic cusp halfWeight vector holomorphic)

theorem cuspShiftedDiskOrbit_rotation (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ (2 * halfWeight) • vector)
    (angle : Circle) (point : ℂ) (inside : ‖point‖ < 1) :
    cusp.π (atInfinity (binaryRotations angle)) (cuspShiftedDiskOrbit cusp halfWeight vector point) =
      (angle : ℂ) ^ (2 * halfWeight + 2) •
        cuspShiftedDiskOrbit cusp halfWeight vector ((angle : ℂ) ^ (-2 : ℤ) * point) := by
  rw [cuspShiftedDiskOrbit, map_smul, cuspDiskOrbit_rotation cusp halfWeight vector rotation angle point inside,
    cuspShiftedDiskOrbit, smul_smul, smul_smul, ← mul_assoc,
    ← zpow_add₀ (Circle.coe_ne_zero angle)]
  congr 1
  rw [show 2 * halfWeight + 2 + (-2 : ℤ) = 2 * halfWeight by ring, mul_comm]

local instance shiftedDiskMeasurable : MeasurableSpace Circle := borel Circle
local instance shiftedDiskBorel : BorelSpace Circle := ⟨rfl⟩

theorem cuspShiftedDiskSeries_smooth_primitive (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet)
    (series : FormalMultilinearSeries ℂ ℂ cusp.H)
    (expansion : HasFPowerSeriesAt (cuspShiftedDiskOrbit cusp halfWeight vector.val) series 0) :
    ∀ᶠ point : ℂ in nhds 0,
      rotationSeriesPrimitive (2 * halfWeight + 2) 0 series.coeff point ∈ cusp.smooth := by
  obtain ⟨radius, positive, small, averaging⟩ :=
    cuspDiskOrbit_exists_smooth_average_radius cusp halfWeight vector spherical holomorphic
  obtain ⟨larger, larger_than, larger_small⟩ := exists_between small
  have larger_positive : 0 < larger := positive.trans larger_than
  have disk_holomorphic := cuspShiftedDiskOrbit_holomorphic cusp halfWeight vector.val holomorphic
  have closed_holomorphic : DifferentiableOn ℂ (cuspShiftedDiskOrbit cusp halfWeight vector.val)
      (Metric.closedBall (0 : ℂ) larger) := disk_holomorphic.mono (by
    intro point member
    rw [Metric.mem_ball, dist_zero_right]
    have bound : ‖point‖ ≤ (larger : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using member
    exact bound.trans_lt (show (larger : ℝ) < 1 from larger_small))
  have cauchy := closed_holomorphic.hasFPowerSeriesOnBall larger_positive
  have series_equal := expansion.eq_formalMultilinearSeries cauchy.hasFPowerSeriesAt
  have expansion_on_ball : HasFPowerSeriesOnBall (cuspShiftedDiskOrbit cusp halfWeight vector.val) series 0 larger :=
    series_equal.symm ▸ cauchy
  have neighborhood : ∀ᶠ point : ℂ in nhds 0, 25 * ‖point‖ < radius := by
    apply (isOpen_lt (continuous_const.mul continuous_norm) continuous_const).mem_nhds
    simpa using (show (0 : ℝ) < radius from positive)
  filter_upwards [neighborhood] with point inside
  rw [rotationSeriesPrimitive_eq_integral _ series larger expansion_on_ball radius positive
    (by exact_mod_cast larger_than) (2 * halfWeight + 2) 0 point inside]
  have kernel_continuous := rotationSeriesKernel_continuous (2 * halfWeight + 2) 0 point radius positive inside
  have average := averaging
    (fun angle : Circle => rotationSeriesKernel (2 * halfWeight + 2) 0 point radius angle *
      ((radius : ℂ) * (angle : ℂ))) (kernel_continuous.mul (continuous_const.mul (by fun_prop)))
  simpa only [cuspShiftedDiskOrbit, smul_smul] using average

theorem cuspShiftedDiskOrbit_exists_smooth_difference (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) :
    ∀ᶠ point : ℂ in nhds 0, ∃ primitive : cusp.smooth,
      cusp.π (atInfinity (binaryRotations rotationSeparatingCircle)) primitive.val -
        rotationSeparationPhase ^ (2 * halfWeight + 2) • primitive.val =
      cuspShiftedDiskOrbit cusp halfWeight vector.val point := by
  obtain ⟨series, expansion⟩ := (cuspShiftedDiskOrbit_holomorphic cusp halfWeight vector.val holomorphic).analyticOnNhd Metric.isOpen_ball 0 (by simp)
  have constant_zero : series.coeff 0 = 0 := by
    change (series 0) (fun _ => 1) = 0
    rw [expansion.coeff_zero, cuspShiftedDiskOrbit, zero_smul]
  have eigenvectors (index : ℕ) :
      cusp.π (atInfinity (binaryRotations rotationSeparatingCircle)) (series.coeff index) =
        rotationSeparationPhase ^ ((2 * halfWeight + 2) - 2 * (index : ℤ)) • series.coeff index := by
    have equation := powerSeries_coeff_covariance expansion
      (cuspUnitaryOperator cusp (atInfinity (binaryRotations rotationSeparatingCircle)))
      (rotationSeparationPhase ^ (2 * halfWeight + 2)) (rotationSeparationPhase ^ (-2 : ℤ)) (by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with point inside
        exact cuspShiftedDiskOrbit_rotation cusp halfWeight vector.val rotation rotationSeparatingCircle point
          (by simpa only [Metric.mem_ball, dist_zero_right] using inside)) index
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ rotationSeparationPhase_ne_zero] at equation
    change cusp.π (atInfinity (binaryRotations rotationSeparatingCircle)) (series.coeff index) = _ at equation
    simpa only [sub_eq_add_neg, neg_mul] using equation
  obtain ⟨radius, constant, positive, constant_positive, bound⟩ := powerSeries_coeff_geometric_bound expansion
  have neighborhood : ∀ᶠ point : ℂ in nhds 0, 25 * ‖point‖ < radius := by
    apply (isOpen_lt (continuous_const.mul continuous_norm) continuous_const).mem_nhds
    simpa using positive
  filter_upwards [neighborhood, hasFPowerSeriesAt_iff.mp expansion,
    cuspShiftedDiskSeries_smooth_primitive cusp halfWeight vector spherical holomorphic series expansion]
    with point inside summation smooth
  refine ⟨⟨rotationSeriesPrimitive (2 * halfWeight + 2) 0 series.coeff point, smooth⟩, ?_⟩
  have equation := rotationSeriesPrimitive_equation
    (cuspUnitaryOperator cusp (atInfinity (binaryRotations rotationSeparatingCircle)))
    (2 * halfWeight + 2) 0 series.coeff point (cuspShiftedDiskOrbit cusp halfWeight vector.val point)
    eigenvectors (by simpa only [zero_add] using summation)
    (rotationSeriesPrimitive_summable _ _ _ _ radius constant positive constant_positive.le bound inside)
  change cusp.π (atInfinity (binaryRotations rotationSeparatingCircle)) _ - _ = _ at equation
  simpa only [Nat.cast_zero, mul_zero, sub_zero, constant_zero, smul_zero] using equation

end TernaryPeriodPolynomials.SphericalDetection.Helpers
