module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Eichler.BridgeCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CohomologicalEndpoints
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.HeckeImage

@[expose] public section


/-!
# Holomorphy of the scalar realization of the classical lower endpoint

The lower endpoint of the relative normal form of a cohomological binary cocycle is killed by
the raising operator, so its weighted affine orbit is holomorphic. A classical vector with the
same underlying Hilbert vector therefore has a holomorphic scalar weighted realization at every
adelic base point; this is the integrand `F` of the pointwise Eichler normal form.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- **The weighted affine orbit of the lower endpoint is holomorphic.** -/
theorem lowerEndpoint_orbit_holomorphic (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (odd : Odd degree)
    (cohomological : Cohomological cusp degree) (level : Subgroup BinaryFiniteGL)
    (halfWeight : ℤ) (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (lower upper : binarySmoothValues cusp (Fin (degree + 2)))
    (lower_mem : ∀ position, lower position ∈ cuspFiniteWeightValues cusp level
      (binaryUnitaryWeight degree (-2) position))
    (upper_mem : ∀ position, upper position ∈ cuspFiniteWeightValues cusp level
      (binaryUnitaryWeight degree 2 position))
    (closed : binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) (-2) lower =
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 2 upper) :
    DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight (lower 0).val)
      UpperHalfPlane.upperHalfPlaneSet := by
  have killed := (binaryRelative_endpoint_kernels cusp spherical odd cohomological level
    lower upper lower_mem upper_mem closed).1
  rw [← weight] at killed
  exact cuspWeightedAffineOrbit_holomorphic cusp halfWeight (lower 0).val
    ((lower 0).property.differentiableOn (by simp)) (congrArg Subtype.val killed)

/-- **The scalar weighted realization of the classical lower endpoint is holomorphic.** -/
theorem classicalEndpoint_scalar_holomorphic (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (odd : Odd degree)
    (cohomological : Cohomological cusp degree) (level : Subgroup BinaryFiniteGL)
    (halfWeight : ℤ) (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (lower upper : binarySmoothValues cusp (Fin (degree + 2)))
    (lower_mem : ∀ position, lower position ∈ cuspFiniteWeightValues cusp level
      (binaryUnitaryWeight degree (-2) position))
    (upper_mem : ∀ position, upper position ∈ cuspFiniteWeightValues cusp level
      (binaryUnitaryWeight degree 2 position))
    (closed : binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) (-2) lower =
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 2 upper)
    (classical : cuspClassicalVectors cusp halfWeight)
    (value : classical.val.val = (lower 0).val) (h : BinaryAdelicGL) :
    DifferentiableOn ℂ (endpointScalar cusp halfWeight classical.val h)
      UpperHalfPlane.upperHalfPlaneSet := by
  have orbit := lowerEndpoint_orbit_holomorphic cusp spherical odd cohomological level halfWeight
    weight lower upper lower_mem upper_mem closed
  rw [← value] at orbit
  exact endpointScalar_holomorphic cusp halfWeight classical.val classical.property.1
    classical.property.2.1 orbit h

/-- The classical lower endpoint is fixed by the finite congruence level. -/
theorem classicalVector_fixed (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (classical : cuspClassicalVectors cusp halfWeight) :
    classical.val.val ∈
      PlaneEisensteinContinuation.BinaryLevel.fixedSubspace cusp
        PlaneEisensteinContinuation.BinaryLevel.finiteCongruence :=
  spherical_mem_fixedSubspace cusp _ classical.property.1

end TernaryPeriodPolynomials.AnalyticClasses
