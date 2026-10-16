module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LadderNorms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspAffineDifferential_spherical (cusp : CuspidalRepresentation)
    (vector : cusp.H) (fixed : vector ∈ cuspSphericalValues cusp)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I)
    (direction : ℂ) :
    fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I direction ∈ cuspSphericalValues cusp := by
  have orbit_fixed :
      (fun point => cuspSphericalProjection cusp (cuspAffineOrbitVector cusp vector point)) =
        cuspAffineOrbitVector cusp vector := by
    funext point
    apply (cuspSphericalProjection_eq_self_iff cusp _).mpr
    exact cuspSphericalValues_real_stable cusp
      (invertibleMatrix (binaryUpperSectionMatrix point)) vector fixed
  have derivative := (((cuspSphericalProjection cusp).restrictScalars ℝ).hasFDerivAt.comp
    Complex.I regular.hasFDerivAt).fderiv
  change fderiv ℝ (fun point => cuspSphericalProjection cusp (cuspAffineOrbitVector cusp vector point)) Complex.I =
    ((cuspSphericalProjection cusp).restrictScalars ℝ).comp
      (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I) at derivative
  rw [orbit_fixed] at derivative
  apply (cuspSphericalProjection_eq_self_iff cusp _).mp
  exact (congrArg (fun linear : ℂ →L[ℝ] cusp.H => linear direction) derivative).symm

theorem cuspLoweringVector_spherical (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.H) (fixed : vector ∈ cuspSphericalValues cusp)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I) :
    cuspLoweringVector cusp weight vector ∈ cuspSphericalValues cusp := by
  exact (cuspSphericalValues cusp).add_mem
    ((cuspSphericalValues cusp).sub_mem (cuspAffineDifferential_spherical cusp vector fixed regular 1)
      ((cuspSphericalValues cusp).smul_mem Complex.I
        (cuspAffineDifferential_spherical cusp vector fixed regular Complex.I)))
    ((cuspSphericalValues cusp).smul_mem (Complex.I * (weight : ℂ) / 2) fixed)

theorem cuspRaisingVector_spherical (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cusp.H) (fixed : vector ∈ cuspSphericalValues cusp)
    (regular : DifferentiableAt ℝ (cuspAffineOrbitVector cusp vector) Complex.I) :
    cuspRaisingVector cusp weight vector ∈ cuspSphericalValues cusp := by
  exact (cuspSphericalValues cusp).add_mem
    ((cuspSphericalValues cusp).add_mem (cuspAffineDifferential_spherical cusp vector fixed regular 1)
      ((cuspSphericalValues cusp).smul_mem Complex.I
        (cuspAffineDifferential_spherical cusp vector fixed regular Complex.I)))
    ((cuspSphericalValues cusp).smul_mem (Complex.I * (weight : ℂ) / 2) fixed)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
