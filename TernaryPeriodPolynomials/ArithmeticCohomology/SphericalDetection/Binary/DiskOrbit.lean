module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DiskGeometry
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.RotationProjection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspWeightedAffineOrbit_det_one (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ (2 * halfWeight) • vector)
    (matrix : BinaryRealGL) (determinant : (Matrix.GeneralLinearGroup.det matrix).val = 1)
    (point : UpperHalfPlane) :
    cusp.π (atInfinity matrix) (cuspWeightedAffineOrbit cusp halfWeight vector point) =
      UpperHalfPlane.denom matrix point ^ (2 * halfWeight) •
        cuspWeightedAffineOrbit cusp halfWeight vector ((matrix • point : UpperHalfPlane) : ℂ) := by
  simp only [cuspWeightedAffineOrbit, LinearMap.map_smul_of_tower,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [cuspRotationWeight_affine_transform cusp vector (2 * halfWeight) rotation matrix determinant,
    smul_smul, smul_smul]
  simp only [UpperHalfPlane.coe_im]
  congr 1
  change ((point.im ^ halfWeight : ℝ) : ℂ) * binaryPhaseValue matrix point ^ (2 * halfWeight) =
    UpperHalfPlane.denom matrix point ^ (2 * halfWeight) *
      (((matrix • point : UpperHalfPlane).im ^ halfWeight : ℝ) : ℂ)
  rw [binary_weighted_phase_identity matrix determinant point halfWeight]
  have cancel : UpperHalfPlane.denom matrix point ^ (2 * halfWeight) *
      UpperHalfPlane.denom matrix point ^ (-2 * halfWeight) = 1 := by
    rw [← zpow_add₀ (UpperHalfPlane.denom_ne_zero matrix point)]
    convert zpow_zero (UpperHalfPlane.denom matrix point) using 1
    congr 1
    ring
  rw [← mul_assoc, ← mul_assoc, cancel, one_mul]

/-- The holomorphic disk orbit with its lowest rotation character factored out. -/
def cuspDiskOrbit (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H) (point : ℂ) : cusp.H :=
  (1 - point) ^ (2 * halfWeight) •
    cuspWeightedAffineOrbit cusp halfWeight vector (binaryDiskPoint point)

theorem cuspDiskOrbit_zero (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.H) :
    cuspDiskOrbit cusp halfWeight vector 0 = vector := by
  simp [cuspDiskOrbit, binaryDiskPoint_zero, cuspWeightedAffineOrbit, cuspAffineOrbitVector_I]

theorem cuspDiskOrbit_spherical (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.H)
    (spherical : vector ∈ cuspSphericalValues cusp) (point : ℂ) :
    cuspDiskOrbit cusp halfWeight vector point ∈ cuspSphericalValues cusp := by
  unfold cuspDiskOrbit cuspWeightedAffineOrbit cuspAffineOrbitVector
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact (cuspSphericalValues cusp).smul_mem _ ((cuspSphericalValues cusp).smul_mem _
    (cuspSphericalValues_real_stable cusp _ vector spherical))

theorem cuspDiskOrbit_holomorphic (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet) :
    DifferentiableOn ℂ (cuspDiskOrbit cusp halfWeight vector) (Metric.ball 0 1) := by
  have composite := holomorphic.comp binaryDiskPoint_differentiableOn (by
    intro point inside
    apply binaryDiskPoint_im_pos
    simpa only [Metric.mem_ball, dist_zero_right] using inside)
  have factor : DifferentiableOn ℂ (fun point : ℂ => (1 - point) ^ (2 * halfWeight))
      (Metric.ball 0 1) := by
    intro point inside
    have bound : ‖point‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using inside
    have subtraction : DifferentiableAt ℂ (fun argument : ℂ => 1 - argument) point :=
      differentiableAt_const 1 |>.sub differentiableAt_id
    exact (subtraction.zpow (m := 2 * halfWeight)
      (Or.inl (binaryDiskPoint_denominator_ne_zero bound))).differentiableWithinAt
  exact factor.smul composite

theorem cuspDiskOrbit_rotation (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ (2 * halfWeight) • vector)
    (angle : Circle) (point : ℂ) (inside : ‖point‖ < 1) :
    cusp.π (atInfinity (binaryRotations angle)) (cuspDiskOrbit cusp halfWeight vector point) =
      (angle : ℂ) ^ (2 * halfWeight) •
        cuspDiskOrbit cusp halfWeight vector ((angle : ℂ) ^ (-2 : ℤ) * point) := by
  unfold cuspDiskOrbit
  rw [map_smul]
  have covariance := cuspWeightedAffineOrbit_det_one cusp halfWeight vector rotation
    (binaryRotations angle) (binaryRotations_det angle) (binaryDiskUpperPoint point inside)
  change cusp.π _ (cuspWeightedAffineOrbit cusp halfWeight vector (binaryDiskPoint point)) = _ at covariance
  rw [covariance, binaryDiskPoint_rotation, smul_smul, smul_smul, ← mul_zpow]
  change ((1 - point) * UpperHalfPlane.denom (binaryRotations angle) (binaryDiskPoint point)) ^
    (2 * halfWeight) • _ = _
  rw [binaryDiskPoint_rotation_denom angle point inside, mul_zpow]

/-- The disk orbit as an element of the exact supplied smooth submodule. -/
def cuspDiskSmoothVector (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (point : ℂ) : cusp.smooth :=
  ((1 - point) ^ (2 * halfWeight) * (((binaryDiskPoint point).im ^ halfWeight : ℝ) : ℂ)) •
    cuspSmoothAction cusp (atInfinity (invertibleMatrix (binaryUpperSectionMatrix (binaryDiskPoint point)))) vector

theorem cuspDiskSmoothVector_val (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (point : ℂ) :
    (cuspDiskSmoothVector cusp halfWeight vector point).val = cuspDiskOrbit cusp halfWeight vector.val point := by
  simp only [cuspDiskSmoothVector, cuspDiskOrbit, cuspWeightedAffineOrbit,
    RCLike.real_smul_eq_coe_smul (K := ℂ), Submodule.coe_smul, smul_smul]
  rfl

def cuspScalarDiskOrbit (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) (point : ℂ) : ℂ :=
  (1 - point) ^ (2 * halfWeight) *
    cuspScalarWeightedRealization cusp halfWeight vector base (binaryDiskPoint point)

theorem cuspDiskSmoothVector_realize (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) (point : ℂ) :
    cusp.realize (cuspDiskSmoothVector cusp halfWeight vector point) base =
      cuspScalarDiskOrbit cusp halfWeight vector base point := by
  simp only [cuspDiskSmoothVector, map_smul, Pi.smul_apply, smul_eq_mul,
    cuspSmoothAction_realize, cuspScalarDiskOrbit, cuspScalarWeightedRealization,
    cuspScalarAffineRealization, Complex.real_smul, mul_assoc]

theorem cuspScalarDiskOrbit_analytic (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) :
    AnalyticOnNhd ℝ (cuspScalarDiskOrbit cusp halfWeight vector base) (Metric.ball 0 1) := by
  have geometry := binaryDiskPoint_differentiableOn.analyticOnNhd Metric.isOpen_ball
  intro point inside
  have bound : ‖point‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using inside
  have composite := (cuspScalarWeightedRealization_analytic cusp halfWeight vector base
    (binaryDiskPoint point) (binaryDiskPoint_im_pos bound)).fun_comp
      ((geometry point inside).restrictScalars (𝕜 := ℝ))
  have factor : AnalyticAt ℝ (fun argument : ℂ => (1 - argument) ^ (2 * halfWeight)) point :=
    (analyticAt_const.sub analyticAt_id).zpow (binaryDiskPoint_denominator_ne_zero bound)
  exact factor.mul composite

end TernaryPeriodPolynomials.SphericalDetection.Helpers
