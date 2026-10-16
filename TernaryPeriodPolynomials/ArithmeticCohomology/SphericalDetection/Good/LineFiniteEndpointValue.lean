module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteCriticalValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteGlobalIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineFiniteVectorIntegral_endpointValue (cusp : CuspidalRepresentation)
    (spherical_cusp : SphericalCusp cusp) {degree : ℕ} (large : 3 < degree)
    (cohomological : Cohomological cusp degree) (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
    (form_nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations (-2 * halfWeight) form eigenvalues)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (eigen : ∀ prime : Nat.Primes, cuspPrimeHeckeSum cusp prime vector =
      ((prime.val : ℂ) ^ (halfWeight + 1) * eigenvalues prime) • vector) :
    goodLineFiniteVectorIntegral degree cusp cohomologicalPoint vector =
      (LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) 3)
          (((-2 * halfWeight : ℤ) : ℂ) - 2) /
        LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) 3)
          (((-2 * halfWeight : ℤ) : ℂ) - 1)) * cusp.realize vector 1 :=
  goodLineFiniteVectorIntegral_criticalValue cusp spherical_cusp (by omega) cohomological halfWeight weight
    form form_nonzero eigenvalues relations vector nonzero spherical eigen
    (goodLineFiniteVectorIntegrand_endpoint_integrable degree large cusp vector spherical)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
