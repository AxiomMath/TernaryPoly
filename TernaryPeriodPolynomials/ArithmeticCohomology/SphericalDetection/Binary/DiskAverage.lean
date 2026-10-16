module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DiskOrbit
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Analytic.ShiftIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspDiskMatrixOrbit (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.H)
    (point : BinaryRealMatrix × ℂ) : cusp.H :=
  cusp.π (atInfinity (invertibleMatrix point.1)) (cuspDiskOrbit cusp halfWeight vector point.2)

theorem cuspDiskMatrixOrbit_analytic (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) :
    AnalyticAt ℝ (cuspDiskMatrixOrbit cusp halfWeight vector.val) ((1, 0) : BinaryRealMatrix × ℂ) := by
  have disk_regular : ContDiffAt ℝ ⊤ binaryDiskPoint 0 :=
    ((binaryDiskPoint_differentiableOn.analyticOnNhd Metric.isOpen_ball 0 (by simp)).restrictScalars
      (𝕜 := ℝ)).contDiffAt
  have section_regular : ContDiffAt ℝ ⊤
      (fun point : ℂ => binaryUpperSectionMatrix (binaryDiskPoint point)) 0 := by
    have at_base : ContDiffAt ℝ ⊤ binaryUpperSectionMatrix (binaryDiskPoint 0) := by
      rw [binaryDiskPoint_zero]
      exact binaryUpperSectionMatrix_contDiffOn.contDiffAt
        (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (by simp))
    exact at_base.comp 0 disk_regular
  let argument : BinaryRealMatrix × ℂ → BinaryRealMatrix :=
    fun point => point.1 * binaryUpperSectionMatrix (binaryDiskPoint point.2)
  have argument_regular : ContDiffAt ℝ ⊤ argument ((1, 0) : BinaryRealMatrix × ℂ) := by
    have section_joint := section_regular.comp ((1, 0) : BinaryRealMatrix × ℂ) contDiff_snd.contDiffAt
    apply contDiffAt_pi.mpr
    intro row
    apply contDiffAt_pi.mpr
    intro column
    change ContDiffAt ℝ ⊤ (fun point : BinaryRealMatrix × ℂ =>
      ∑ index, point.1 row index * binaryUpperSectionMatrix (binaryDiskPoint point.2) index column) ((1, 0) : BinaryRealMatrix × ℂ)
    apply ContDiffAt.sum
    intro index _
    have entry : ContDiffAt ℝ ⊤ (fun point : BinaryRealMatrix × ℂ => point.1 row index)
        ((1, 0) : BinaryRealMatrix × ℂ) := by fun_prop
    exact entry.mul (contDiffAt_pi.mp (contDiffAt_pi.mp section_joint index) column)
  have argument_base : argument ((1, 0) : BinaryRealMatrix × ℂ) = 1 := by
    simp [argument, binaryDiskPoint_zero, binaryUpperSectionMatrix_I]
  have orbit_regular := smooth_one_contDiffOn
    (function := fun matrix => cusp.π (atInfinity matrix) vector.val)
    ((cusp.smooth_exact vector.val).mp vector.property).1
  have matrix_open : IsOpen {matrix : BinaryRealMatrix | matrix.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  have orbit_at_one : ContDiffAt ℝ ⊤ (fun matrix : BinaryRealMatrix =>
      cusp.π (atInfinity (invertibleMatrix matrix)) vector.val) 1 :=
    orbit_regular.contDiffAt (matrix_open.mem_nhds (by simp))
  have orbit_composite := (argument_base.symm ▸ orbit_at_one).comp ((1, 0) : BinaryRealMatrix × ℂ) argument_regular
  have disk_joint := disk_regular.comp ((1, 0) : BinaryRealMatrix × ℂ) contDiff_snd.contDiffAt
  have imaginary_joint := Complex.imCLM.contDiff.contDiffAt.comp ((1, 0) : BinaryRealMatrix × ℂ) disk_joint
  have imaginary_power : ContDiffAt ℝ ⊤
      (fun point : BinaryRealMatrix × ℂ => (binaryDiskPoint point.2).im ^ halfWeight)
      ((1, 0) : BinaryRealMatrix × ℂ) :=
    (imaginary_joint.analyticAt.zpow (n := halfWeight) (by simp [binaryDiskPoint_zero])).contDiffAt
  have complex_power : ContDiffAt ℝ ⊤
      (fun point : BinaryRealMatrix × ℂ => (1 - point.2) ^ (2 * halfWeight)) ((1, 0) : BinaryRealMatrix × ℂ) :=
    ((contDiffAt_const.sub contDiff_snd.contDiffAt).analyticAt.zpow (by simp)).contDiffAt
  have regular := complex_power.smul (imaginary_power.smul orbit_composite)
  apply regular.analyticAt.congr
  have nearby : ∀ᶠ point : BinaryRealMatrix × ℂ in nhds ((1, 0) : BinaryRealMatrix × ℂ),
      point.1.det ≠ 0 ∧ ‖point.2‖ < 1 := by
    have member : {matrix : BinaryRealMatrix | matrix.det ≠ 0} ×ˢ Metric.ball (0 : ℂ) 1 ∈
        nhds ((1, 0) : BinaryRealMatrix × ℂ) :=
      (matrix_open.prod Metric.isOpen_ball).mem_nhds (by simp)
    filter_upwards [member] with point belongs
    exact ⟨belongs.1, by simpa only [Metric.mem_ball, dist_zero_right] using belongs.2⟩
  filter_upwards [nearby] with point member
  change (1 - point.2) ^ (2 * halfWeight) •
      ((binaryDiskPoint point.2).im ^ halfWeight • cusp.π (atInfinity (invertibleMatrix (argument point))) vector.val) = _
  dsimp only [argument]
  rw [invertibleMatrix_mul _ _ member.1
    (binaryUpperSectionMatrix_invertible _ (binaryDiskPoint_im_pos member.2)), atInfinity_mul, map_mul,
    Module.End.mul_apply]
  simp only [cuspDiskMatrixOrbit, cuspDiskOrbit, cuspWeightedAffineOrbit, cuspAffineOrbitVector,
    map_smul, LinearMap.map_smul_of_tower]

theorem cuspSpherical_smooth_of_analyticAt_one (cusp : CuspidalRepresentation) (vector : cusp.H)
    (spherical : vector ∈ cuspSphericalValues cusp)
    (analytic : AnalyticAt ℝ (fun matrix : BinaryRealMatrix =>
      cusp.π (atInfinity (invertibleMatrix matrix)) vector) 1) : vector ∈ cusp.smooth := by
  apply (cusp.smooth_exact vector).mpr
  refine ⟨cuspUnitary_orbit_smooth_of_one cusp vector analytic,
    finiteIntegralGLLevel 2, finiteIntegralGLLevel_isOpen 2, finiteIntegralGLLevel_isCompact 2, ?_⟩
  intro element
  obtain ⟨original, equality⟩ := element.property
  rw [← equality]
  exact spherical original

local instance diskAverageMeasurable : MeasurableSpace Circle := borel Circle
local instance diskAverageBorel : BorelSpace Circle := ⟨rfl⟩

theorem cuspDiskOrbit_exists_smooth_average_radius (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
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
  have orbit_continuous : Continuous (fun angle => cuspDiskOrbit cusp halfWeight vector.val (circlePoint angle)) :=
    (cuspDiskOrbit_holomorphic cusp halfWeight vector.val holomorphic).continuousOn.comp_continuous
      circle_continuous circle_inside
  have integrable : Integrable (fun angle => kernel angle •
      cuspDiskOrbit cusp halfWeight vector.val (circlePoint angle)) binaryRotationMeasure :=
    (kernel_continuous.smul orbit_continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let average := ∫ angle : Circle, kernel angle •
    cuspDiskOrbit cusp halfWeight vector.val (circlePoint angle) ∂binaryRotationMeasure
  have average_spherical : average ∈ cuspSphericalValues cusp := by
    apply (cuspSphericalProjection_eq_self_iff cusp _).mp
    dsimp only [average]
    rw [← (cuspSphericalProjection cusp).integral_comp_comm integrable]
    apply integral_congr_ae
    filter_upwards [] with angle
    rw [map_smul, (cuspSphericalProjection_eq_self_iff cusp _).mpr
      (cuspDiskOrbit_spherical cusp halfWeight vector.val spherical (circlePoint angle))]
  apply cuspSpherical_smooth_of_analyticAt_one cusp average average_spherical
  have joint := analyticAt_weighted_shift_integral binaryRotationMeasure
    (cuspDiskMatrixOrbit cusp halfWeight vector.val) series ((1, 0) : BinaryRealMatrix × ℂ)
    outerRadius expansion (fun angle => ((0 : BinaryRealMatrix), circlePoint angle))
    (continuous_const.prodMk circle_continuous) kernel kernel_continuous radius radius positive inside (by
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
    (∫ angle, kernel angle • cuspDiskOrbit cusp halfWeight vector.val (circlePoint angle) ∂binaryRotationMeasure)
  rw [← (cuspUnitaryOperator cusp (atInfinity (invertibleMatrix matrix))).integral_comp_comm integrable]
  apply integral_congr_ae
  filter_upwards [] with angle
  exact (map_smul _ _ _).symm

end TernaryPeriodPolynomials.SphericalDetection.Helpers
