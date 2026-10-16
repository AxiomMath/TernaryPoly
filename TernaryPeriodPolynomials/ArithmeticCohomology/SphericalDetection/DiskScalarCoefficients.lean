module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.RotationSeriesKernel

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- Scalar and Hilbert coefficients agree by an actual smooth rotation-difference primitive. -/
theorem cuspScalarDiskRotationCoefficient (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector.val)
      UpperHalfPlane.upperHalfPlaneSet)
    (series : FormalMultilinearSeries ℂ ℂ cusp.H)
    (expansion : HasFPowerSeriesAt (cuspDiskOrbit cusp halfWeight vector.val) series 0)
    (target : ℕ) (base : BinaryAdelicGL) :
    ∀ᶠ point : ℂ in nhds 0,
      cuspScalarRotationCoefficient cusp (2 * halfWeight - 2 * (target : ℤ)) base
        (cuspDiskSmoothVector cusp halfWeight vector point) =
      point ^ target * cusp.realize
        ⟨series.coeff target, cuspDiskTaylorSeries_smooth cusp halfWeight vector spherical holomorphic
          series expansion target⟩ base := by
  let coefficient : cusp.smooth :=
    ⟨series.coeff target, cuspDiskTaylorSeries_smooth cusp halfWeight vector spherical holomorphic
      series expansion target⟩
  filter_upwards [cuspDiskTaylorSeries_primitive cusp halfWeight vector.val rotation series expansion target,
    cuspDiskTaylorSeries_primitive_smooth cusp halfWeight vector spherical holomorphic series expansion target]
    with point equation smooth
  let primitive : cusp.smooth := ⟨rotationSeriesPrimitive (2 * halfWeight) target series.coeff point, smooth⟩
  have comparison := cuspScalarRotationCoefficient_of_difference cusp
    (2 * halfWeight - 2 * (target : ℤ)) (cuspDiskSmoothVector cusp halfWeight vector point)
    (point ^ target • coefficient) primitive base rotationSeparatingCircle (by
      intro angle
      change cusp.π (atInfinity (binaryRotations angle)) (point ^ target • series.coeff target) = _
      rw [map_smul, cuspDiskTaylorSeries_weight cusp halfWeight vector.val rotation series expansion]
      exact smul_comm _ _ _) (by
      rw [cuspDiskSmoothVector_val]
      exact equation.symm)
  simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using comparison

end TernaryPeriodPolynomials.SphericalDetection.Helpers
