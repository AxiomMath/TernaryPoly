module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.ShiftedDiskPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance scalarDiskMeanMeasurable : MeasurableSpace Circle := borel Circle
local instance scalarDiskMeanBorel : BorelSpace Circle := ⟨rfl⟩

theorem cuspScalarRotationCoefficient_other_weight (cusp : CuspidalRepresentation)
    (weight target : ℤ) (distinct : weight ≠ target) (vector : cusp.smooth) (base : BinaryAdelicGL)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ weight • vector.val) :
    cuspScalarRotationCoefficient cusp target base vector = 0 := by
  have shifted : cuspSmoothAction cusp (atInfinity (binaryRotations rotationSeparatingCircle)) vector =
      rotationSeparationPhase ^ weight • vector := Subtype.ext (rotation rotationSeparatingCircle)
  have transformed := cuspScalarRotationCoefficient_translate cusp target vector base rotationSeparatingCircle
  rw [shifted, map_smul, smul_eq_mul, rotationSeparatingCircle_coe] at transformed
  have annihilates : (rotationSeparationPhase ^ weight - rotationSeparationPhase ^ target) *
      cuspScalarRotationCoefficient cusp target base vector = 0 := by linear_combination transformed
  exact (mul_eq_zero.mp annihilates).resolve_left (sub_ne_zero.mpr
    (fun equality => distinct (rotationSeparationPhase_zpow_injective equality)))

theorem cuspDiskSmoothVector_rotation (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (angle : Circle) (point : ℂ) (inside : ‖point‖ < 1) :
    cuspSmoothAction cusp (atInfinity (binaryRotations angle)) (cuspDiskSmoothVector cusp halfWeight vector point) =
      (angle : ℂ) ^ (2 * halfWeight) •
        cuspDiskSmoothVector cusp halfWeight vector ((angle : ℂ) ^ (-2 : ℤ) * point) := by
  apply Subtype.ext
  change cusp.π (atInfinity (binaryRotations angle)) (cuspDiskSmoothVector cusp halfWeight vector point).val =
    (angle : ℂ) ^ (2 * halfWeight) • (cuspDiskSmoothVector cusp halfWeight vector _).val
  rw [cuspDiskSmoothVector_val, cuspDiskSmoothVector_val]
  exact cuspDiskOrbit_rotation cusp halfWeight vector.val rotation angle point inside

theorem cuspScalarDiskOrbit_rotation (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (base : BinaryAdelicGL) (angle : Circle) (point : ℂ) (inside : ‖point‖ < 1) :
    cusp.realize (cuspDiskSmoothVector cusp halfWeight vector point) (base * atInfinity (binaryRotations angle)) =
      (angle : ℂ) ^ (2 * halfWeight) * cuspScalarDiskOrbit cusp halfWeight vector base
        ((angle : ℂ) ^ (-2 : ℤ) * point) := by
  have equality := congrArg (fun value : cusp.smooth => cusp.realize value base)
    (cuspDiskSmoothVector_rotation cusp halfWeight vector rotation angle point inside)
  simpa only [cuspSmoothAction_realize, map_smul, Pi.smul_apply, smul_eq_mul,
    cuspDiskSmoothVector_realize] using equality

theorem cuspScalarDiskRotationCoefficient_above (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) (base : BinaryAdelicGL) :
    ∀ᶠ point : ℂ in nhds 0,
      cuspScalarRotationCoefficient cusp (2 * halfWeight + 2) base
        (cuspDiskSmoothVector cusp halfWeight vector point) = 0 := by
  filter_upwards [cuspShiftedDiskOrbit_exists_smooth_difference cusp halfWeight vector spherical rotation holomorphic]
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
    have equation := congrArg (cuspScalarRotationCoefficient cusp (2 * halfWeight + 2) base) smooth_difference
    change cuspScalarRotationCoefficient cusp (2 * halfWeight + 2) base
      (point • cuspDiskSmoothVector cusp halfWeight vector point) =
      cuspScalarRotationCoefficient cusp (2 * halfWeight + 2) base
        (cuspSmoothAction cusp (atInfinity (binaryRotations rotationSeparatingCircle)) primitive -
          (rotationSeparatingCircle : ℂ) ^ (2 * halfWeight + 2) • primitive) at equation
    rw [map_smul, cuspScalarRotationCoefficient_difference, smul_eq_mul] at equation
    exact (mul_eq_zero.mp equation).resolve_left zero

theorem cuspScalarDisk_antiholomorphic_mean_zero (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet) (base : BinaryAdelicGL) :
    ∀ᶠ point : ℂ in nhds 0,
      (∫ angle : Circle, (angle : ℂ) ^ (-2 : ℤ) * cuspScalarDiskOrbit cusp halfWeight vector base
        ((angle : ℂ) ^ (-2 : ℤ) * point) ∂binaryRotationMeasure) = 0 := by
  filter_upwards [cuspScalarDiskRotationCoefficient_above cusp halfWeight vector spherical rotation holomorphic base,
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

end TernaryPeriodPolynomials.SphericalDetection.Helpers
