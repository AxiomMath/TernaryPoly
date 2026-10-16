module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.BridgePart6
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DiskAverage
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.ShiftedDiskPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.DiskMean
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.Holomorphic

@[expose] public section


/-!
# Level-three port of the spherical holomorphic-detection chain, Part7

Mechanical port to the level-three group `{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}` of
`SphericalDetection.BinaryDiskAverage`, `SphericalDetection.ShiftedDiskPrimitive`,
`SphericalDetection.ScalarDiskMean`, `SphericalDetection.ScalarHolomorphic`.
`SphericalCusp` is replaced by `LevelThreeCusp`, `cuspSphericalValues` by `levelThreeValues`,
`cuspSphericalProjection` by `levelThreeProjection` and the level `GL₂(ℤ̂)` used for smoothness by
the principal congruence level of conductor three. Proofs are those of the original declarations
(source: the SphericalDetection development, AxiomProver); the port was generated and checked by AxiomCode (Claude Sonnet 5.5).
-/

noncomputable section

open TernaryPeriodPolynomials.SphericalDetection
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.MultiplicityOne

section CloneBinaryDiskAverage

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

open scoped Matrix.Norms.Elementwise

theorem levelThree_smooth_of_analyticAt_one (cusp : CuspidalRepresentation) (vector : cusp.H)
    (spherical : vector ∈ levelThreeValues cusp)
    (analytic : AnalyticAt ℝ (fun matrix : BinaryRealMatrix =>
      cusp.π (atInfinity (invertibleMatrix matrix)) vector) 1) : vector ∈ cusp.smooth := by
  apply (cusp.smooth_exact vector).mpr
  refine ⟨cuspUnitary_orbit_smooth_of_one cusp vector analytic,
    levelThreeSmoothLevel, levelThreeSmoothLevel_isOpen, levelThreeSmoothLevel_isCompact, ?_⟩
  intro element
  exact levelThreeValues_fixed_smoothLevel cusp vector spherical
    element.val element.property

local instance diskAverageMeasurable : MeasurableSpace Circle := borel Circle

local instance diskAverageBorel : BorelSpace Circle := ⟨rfl⟩

theorem cuspDiskOrbit_exists_smooth_average_radius (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ levelThreeValues cusp)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) :
    ∃ radius : NNReal, 0 < radius ∧ radius < 1 ∧
      ∀ kernel : Circle → ℂ, Continuous kernel →
        (∫ angle : Circle, kernel angle • cuspDiskOrbit cusp halfWeight vector.val
          ((radius : ℂ) * (angle : ℂ)) ∂binaryRotationMeasure) ∈ cusp.smooth := by
  obtain ⟨series, outerRadius, expansion⟩ := cuspDiskMatrixOrbit_analytic cusp halfWeight vector
  obtain ⟨small, small_positive, small_bound⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
    (lt_min expansion.r_pos (by norm_num : (0 : ENNReal) < 1))
  have small_pos : 0 < small := by exact_mod_cast small_positive
  let radius : NNReal := small / 4
  have positive : 0 < radius := by dsimp [radius]; positivity
  have twice_small : radius + radius < small := by
    dsimp [radius]
    exact_mod_cast (show (small : ℝ) / 4 + (small : ℝ) / 4 < small by
      have : (0 : ℝ) < small := small_pos
      linarith)
  have inside : (radius : ENNReal) + radius < outerRadius := by
    rw [← ENNReal.coe_add]
    exact (ENNReal.coe_lt_coe.mpr twice_small).trans (lt_of_lt_of_le small_bound (min_le_left _ _))
  have radius_small : radius < 1 := by
    have small_one : small < 1 := by
      exact_mod_cast lt_of_lt_of_le small_bound (min_le_right outerRadius 1)
    exact (lt_of_le_of_lt le_self_add twice_small).trans small_one
  refine ⟨radius, positive, radius_small, ?_⟩
  intro kernel kernel_continuous
  let circlePoint : Circle → ℂ := fun angle => (radius : ℂ) * (angle : ℂ)
  have circle_continuous : Continuous circlePoint := continuous_const.mul (by fun_prop)
  have circle_norm (angle : Circle) : ‖circlePoint angle‖ = radius := by
    simp only [circlePoint, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg radius.coe_nonneg]
  have circle_inside (angle : Circle) : circlePoint angle ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, circle_norm]
    exact_mod_cast radius_small
  have orbit_continuous : Continuous (fun angle => cuspDiskOrbit cusp halfWeight vector.val
    (circlePoint angle)) :=
    (cuspDiskOrbit_holomorphic cusp halfWeight vector.val holomorphic).continuousOn.comp_continuous
      circle_continuous circle_inside
  have integrable : Integrable (fun angle => kernel angle •
      cuspDiskOrbit cusp halfWeight vector.val (circlePoint angle)) binaryRotationMeasure :=
    (kernel_continuous.smul orbit_continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let average := ∫ angle : Circle, kernel angle •
    cuspDiskOrbit cusp halfWeight vector.val (circlePoint angle) ∂binaryRotationMeasure
  have average_spherical : average ∈ levelThreeValues cusp := by
    apply (levelThreeProjection_eq_self_iff cusp _).mp
    dsimp only [average]
    rw [← (levelThreeProjection cusp).integral_comp_comm integrable]
    apply integral_congr_ae
    filter_upwards [] with angle
    rw [map_smul, (levelThreeProjection_eq_self_iff cusp _).mpr
      (cuspDiskOrbit_levelThree cusp halfWeight vector.val spherical (circlePoint angle))]
  apply levelThree_smooth_of_analyticAt_one cusp average average_spherical
  have joint := analyticAt_weighted_shift_integral binaryRotationMeasure
    (cuspDiskMatrixOrbit cusp halfWeight vector.val) series ((1, 0) : BinaryRealMatrix × ℂ)
    outerRadius expansion (fun angle => ((0 : BinaryRealMatrix), circlePoint angle))
    (continuous_const.prodMk circle_continuous) kernel kernel_continuous radius radius positive
      inside (by
      intro angle
      have real_bound : ‖((0 : BinaryRealMatrix), circlePoint angle)‖ ≤ (radius : ℝ) := by
        rw [Prod.norm_def, norm_zero, circle_norm, max_eq_right radius.coe_nonneg]
      exact_mod_cast real_bound)
  have matrix_analytic := joint.fun_comp (f := (ContinuousLinearMap.inl ℝ BinaryRealMatrix ℂ))
    (x := (1 : BinaryRealMatrix))
    ((ContinuousLinearMap.inl ℝ BinaryRealMatrix ℂ).analyticAt (1 : BinaryRealMatrix))
  apply matrix_analytic.congr
  filter_upwards [] with matrix
  change (∫ angle, kernel angle • cusp.π (atInfinity (invertibleMatrix (matrix + 0)))
    (cuspDiskOrbit cusp halfWeight vector.val (0 + circlePoint angle)) ∂binaryRotationMeasure) = _
  simp only [add_zero, zero_add]
  change _ = (cuspUnitaryOperator cusp (atInfinity (invertibleMatrix matrix)))
    (∫ angle, kernel angle • cuspDiskOrbit cusp halfWeight vector.val (circlePoint angle)
      ∂binaryRotationMeasure)
  rw [← (cuspUnitaryOperator cusp (atInfinity (invertibleMatrix matrix))).integral_comp_comm
    integrable]
  apply integral_congr_ae
  filter_upwards [] with angle
  exact (map_smul _ _ _).symm

end CloneBinaryDiskAverage

section CloneShiftedDiskPrimitive

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

local instance shiftedDiskMeasurable : MeasurableSpace Circle := borel Circle

local instance shiftedDiskBorel : BorelSpace Circle := ⟨rfl⟩

theorem cuspShiftedDiskSeries_smooth_primitive (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ levelThreeValues cusp)
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
    have bound : ‖point‖ ≤ (larger : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right]
      using member
    exact bound.trans_lt (show (larger : ℝ) < 1 from larger_small))
  have cauchy := closed_holomorphic.hasFPowerSeriesOnBall larger_positive
  have series_equal := expansion.eq_formalMultilinearSeries cauchy.hasFPowerSeriesAt
  have expansion_on_ball : HasFPowerSeriesOnBall (cuspShiftedDiskOrbit cusp halfWeight vector.val)
    series 0 larger :=
    series_equal.symm ▸ cauchy
  have neighborhood : ∀ᶠ point : ℂ in nhds 0, 25 * ‖point‖ < radius := by
    apply (isOpen_lt (continuous_const.mul continuous_norm) continuous_const).mem_nhds
    simpa using (show (0 : ℝ) < radius from positive)
  filter_upwards [neighborhood] with point inside
  rw [rotationSeriesPrimitive_eq_integral _ series larger expansion_on_ball radius positive
    (by exact_mod_cast larger_than) (2 * halfWeight + 2) 0 point inside]
  have kernel_continuous := rotationSeriesKernel_continuous (2 * halfWeight + 2) 0 point radius
    positive inside
  have average := averaging
    (fun angle : Circle => rotationSeriesKernel (2 * halfWeight + 2) 0 point radius angle *
      ((radius : ℂ) * (angle : ℂ))) (kernel_continuous.mul (continuous_const.mul (by fun_prop)))
  simpa only [cuspShiftedDiskOrbit, smul_smul] using average

theorem cuspShiftedDiskOrbit_exists_smooth_difference (cusp : CuspidalRepresentation) (halfWeight :
    ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ levelThreeValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) :
    ∀ᶠ point : ℂ in nhds 0, ∃ primitive : cusp.smooth,
      cusp.π (atInfinity (binaryRotations rotationSeparatingCircle)) primitive.val -
        rotationSeparationPhase ^ (2 * halfWeight + 2) • primitive.val =
      cuspShiftedDiskOrbit cusp halfWeight vector.val point := by
  obtain ⟨series, expansion⟩ := (cuspShiftedDiskOrbit_holomorphic cusp halfWeight vector.val
    holomorphic).analyticOnNhd Metric.isOpen_ball 0 (by simp)
  have constant_zero : series.coeff 0 = 0 := by
    change (series 0) (fun _ => 1) = 0
    rw [expansion.coeff_zero, cuspShiftedDiskOrbit, zero_smul]
  have eigenvectors (index : ℕ) :
      cusp.π (atInfinity (binaryRotations rotationSeparatingCircle)) (series.coeff index) =
        rotationSeparationPhase ^ ((2 * halfWeight + 2) - 2 * (index : ℤ)) • series.coeff index :=
          by
    have equation := powerSeries_coeff_covariance expansion
      (cuspUnitaryOperator cusp (atInfinity (binaryRotations rotationSeparatingCircle)))
      (rotationSeparationPhase ^ (2 * halfWeight + 2)) (rotationSeparationPhase ^ (-2 : ℤ)) (by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with point inside
        exact cuspShiftedDiskOrbit_rotation cusp halfWeight vector.val rotation
          rotationSeparatingCircle point
          (by simpa only [Metric.mem_ball, dist_zero_right] using inside)) index
    rw [← zpow_natCast, ← zpow_mul, ← zpow_add₀ rotationSeparationPhase_ne_zero] at equation
    change cusp.π (atInfinity (binaryRotations rotationSeparatingCircle)) (series.coeff index) =
      _ at equation
    simpa only [sub_eq_add_neg, neg_mul] using equation
  obtain ⟨radius, constant, positive, constant_positive, bound⟩ :=
    powerSeries_coeff_geometric_bound expansion
  have neighborhood : ∀ᶠ point : ℂ in nhds 0, 25 * ‖point‖ < radius := by
    apply (isOpen_lt (continuous_const.mul continuous_norm) continuous_const).mem_nhds
    simpa using positive
  filter_upwards [neighborhood, hasFPowerSeriesAt_iff.mp expansion,
    cuspShiftedDiskSeries_smooth_primitive cusp halfWeight vector spherical holomorphic series
      expansion]
    with point inside summation smooth
  refine ⟨⟨rotationSeriesPrimitive (2 * halfWeight + 2) 0 series.coeff point, smooth⟩, ?_⟩
  have equation := rotationSeriesPrimitive_equation
    (cuspUnitaryOperator cusp (atInfinity (binaryRotations rotationSeparatingCircle)))
    (2 * halfWeight + 2) 0 series.coeff point (cuspShiftedDiskOrbit cusp halfWeight vector.val
      point)
    eigenvectors (by simpa only [zero_add] using summation)
    (rotationSeriesPrimitive_summable _ _ _ _ radius constant positive constant_positive.le bound
      inside)
  change cusp.π (atInfinity (binaryRotations rotationSeparatingCircle)) _ - _ = _ at equation
  simpa only [Nat.cast_zero, mul_zero, sub_zero, constant_zero, smul_zero] using equation

end CloneShiftedDiskPrimitive

section CloneScalarDiskMean

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

local instance scalarDiskMeanMeasurable : MeasurableSpace Circle := borel Circle

local instance scalarDiskMeanBorel : BorelSpace Circle := ⟨rfl⟩

theorem cuspScalarDiskRotationCoefficient_above (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ levelThreeValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) (base : BinaryAdelicGL) :
    ∀ᶠ point : ℂ in nhds 0,
      cuspScalarRotationCoefficient cusp (2 * halfWeight + 2) base
        (cuspDiskSmoothVector cusp halfWeight vector point) = 0 := by
  filter_upwards [cuspShiftedDiskOrbit_exists_smooth_difference cusp halfWeight vector spherical
    rotation holomorphic]
    with point witness
  by_cases zero : point = 0
  · subst point
    have disk_zero : cuspDiskSmoothVector cusp halfWeight vector 0 = vector := by
      apply Subtype.ext
      rw [cuspDiskSmoothVector_val, cuspDiskOrbit_zero]
    rw [disk_zero]
    exact cuspScalarRotationCoefficient_other_weight cusp (2 * halfWeight) (2 * halfWeight + 2)
      (by omega) vector base rotation
  · obtain ⟨primitive, difference⟩ := witness
    have smooth_difference : point • cuspDiskSmoothVector cusp halfWeight vector point =
        cuspSmoothAction cusp (atInfinity (binaryRotations rotationSeparatingCircle)) primitive -
          rotationSeparationPhase ^ (2 * halfWeight + 2) • primitive := by
      apply Subtype.ext
      change point • (cuspDiskSmoothVector cusp halfWeight vector point).val = _
      rw [cuspDiskSmoothVector_val]
      exact difference.symm
    have equation := congrArg (cuspScalarRotationCoefficient cusp (2 * halfWeight + 2) base)
      smooth_difference
    change cuspScalarRotationCoefficient cusp (2 * halfWeight + 2) base
      (point • cuspDiskSmoothVector cusp halfWeight vector point) =
      cuspScalarRotationCoefficient cusp (2 * halfWeight + 2) base
        (cuspSmoothAction cusp (atInfinity (binaryRotations rotationSeparatingCircle)) primitive -
          (rotationSeparatingCircle : ℂ) ^ (2 * halfWeight + 2) • primitive) at equation
    rw [map_smul, cuspScalarRotationCoefficient_difference, smul_eq_mul] at equation
    exact (mul_eq_zero.mp equation).resolve_left zero

theorem cuspScalarDisk_antiholomorphic_mean_zero (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ levelThreeValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) (base : BinaryAdelicGL) :
    ∀ᶠ point : ℂ in nhds 0,
      (∫ angle : Circle, (angle : ℂ) ^ (-2 : ℤ) * cuspScalarDiskOrbit cusp halfWeight vector base
        ((angle : ℂ) ^ (-2 : ℤ) * point) ∂binaryRotationMeasure) = 0 := by
  filter_upwards [cuspScalarDiskRotationCoefficient_above cusp halfWeight vector spherical rotation
    holomorphic base,
    Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with point vanishes inside
  have point_inside : ‖point‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using inside
  change (∫ angle : Circle, (angle : ℂ) ^ (-(2 * halfWeight + 2)) *
    cusp.realize (cuspDiskSmoothVector cusp halfWeight vector point)
      (base * atInfinity (binaryRotations angle)) ∂binaryRotationMeasure) = 0 at vanishes
  convert vanishes using 1
  apply integral_congr_ae
  filter_upwards [] with angle
  rw [cuspScalarDiskOrbit_rotation cusp halfWeight vector rotation base angle point point_inside,
    ← mul_assoc, ← zpow_add₀ (Circle.coe_ne_zero angle)]
  congr 2
  ring

end CloneScalarDiskMean

section CloneScalarHolomorphic

open GeneralEisenstein GeneralEisenstein.Adelic

theorem cuspScalarDiskOrbit_differentiableAt_zero (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ levelThreeValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) (base : BinaryAdelicGL) :
    DifferentiableAt ℂ (cuspScalarDiskOrbit cusp halfWeight vector base) 0 := by
  apply differentiableAt_complex_of_antiholomorphic_circleMean_zero
  · exact (cuspScalarDiskOrbit_analytic cusp halfWeight vector base).contDiffOn
      Metric.isOpen_ball.uniqueDiffOn
  · exact cuspScalarDisk_antiholomorphic_mean_zero cusp halfWeight vector spherical rotation
      holomorphic base

theorem cuspScalarWeightedRealization_differentiableAt_I (cusp : CuspidalRepresentation)
    (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ levelThreeValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) (base : BinaryAdelicGL) :
    DifferentiableAt ℂ (cuspScalarWeightedRealization cusp halfWeight vector base) Complex.I := by
  have disk_regular := cuspScalarDiskOrbit_differentiableAt_zero cusp halfWeight vector spherical
    rotation holomorphic base
  have at_coordinate : DifferentiableAt ℂ (cuspScalarDiskOrbit cusp halfWeight vector base)
      (binaryDiskCoordinate Complex.I) := by rwa [binaryDiskCoordinate_I]
  have composed := at_coordinate.comp Complex.I binaryDiskCoordinate_differentiableAt_I
  have factor : DifferentiableAt ℂ (fun point => (1 - binaryDiskCoordinate point) ^ (-(2 *
    halfWeight))) Complex.I :=
    ((differentiableAt_const 1).sub binaryDiskCoordinate_differentiableAt_I).zpow
      (Or.inl (by simp [binaryDiskCoordinate_I]))
  apply (factor.mul composed).congr_of_eventuallyEq
  have nearby : ∀ᶠ point : ℂ in nhds Complex.I, point + Complex.I ≠ 0 := by
    apply (isOpen_ne_fun (continuous_id.add continuous_const) continuous_const).mem_nhds
    intro equality
    have imaginary := congrArg Complex.im equality
    norm_num at imaginary
  filter_upwards [nearby] with point denominator
  change cuspScalarWeightedRealization cusp halfWeight vector base point =
    (1 - binaryDiskCoordinate point) ^ (-(2 * halfWeight)) *
      cuspScalarDiskOrbit cusp halfWeight vector base (binaryDiskCoordinate point)
  rw [cuspScalarDiskOrbit, binaryDiskPoint_coordinate point denominator, ← mul_assoc,
    ← zpow_add₀ (binaryDiskCoordinate_sub_ne_zero point denominator), neg_add_cancel, zpow_zero,
      one_mul]

/-- Holomorphicity of the actual scalar realization follows from smooth rotation differences. -/
theorem cuspScalarWeightedRealization_holomorphic (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ levelThreeValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) (base : BinaryAdelicGL) :
    DifferentiableOn ℂ (cuspScalarWeightedRealization cusp halfWeight vector base)
      UpperHalfPlane.upperHalfPlaneSet := by
  intro point positive
  let upper : UpperHalfPlane := ⟨point, positive⟩
  let pullback : ℂ → ℂ := fun argument => (upper.im : ℂ)⁻¹ * (argument - (upper.re : ℂ))
  have pullback_im (argument : ℂ) : (pullback argument).im = upper.im⁻¹ * argument.im := by
    simp [pullback, ← Complex.ofReal_inv]
  have pullback_basepoint : pullback point = Complex.I := by
    apply Complex.ext
    · simp [pullback, ← Complex.ofReal_inv, upper]
    · rw [pullback_im]
      exact inv_mul_cancel₀ (ne_of_gt positive)
  have recovers (argument : ℂ) : (upper.re : ℂ) + (upper.im : ℂ) * pullback argument = argument :=
    by
    dsimp only [pullback]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast ne_of_gt upper.im_pos), one_mul,
      add_sub_cancel]
  have at_base := cuspScalarWeightedRealization_differentiableAt_I cusp halfWeight vector spherical
    rotation holomorphic
    (base * atInfinity (binarySymmetricSection upper))
  have pullback_regular : DifferentiableAt ℂ pullback point :=
    (differentiableAt_id.sub_const (upper.re : ℂ)).const_mul (upper.im : ℂ)⁻¹
  have transformed := ((pullback_basepoint.symm ▸ at_base).comp point pullback_regular).const_smul
    (upper.im ^ halfWeight)
  apply DifferentiableAt.differentiableWithinAt
  apply transformed.congr_of_eventuallyEq
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds positive]
    with argument argument_positive
  have pulled_positive : 0 < (pullback argument).im := by
    rw [pullback_im]
    exact mul_pos (inv_pos.mpr upper.im_pos) argument_positive
  have formula := cuspScalarWeightedRealization_affine cusp halfWeight vector base upper
    ⟨pullback argument, pulled_positive⟩
  rw [recovers] at formula
  exact formula

end CloneScalarHolomorphic

end TernaryPeriodPolynomials.MultiplicityOne
