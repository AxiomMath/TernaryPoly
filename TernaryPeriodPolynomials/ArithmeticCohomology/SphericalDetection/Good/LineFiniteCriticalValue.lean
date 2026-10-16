module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteEulerProduct
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.CriticalEulerProduct

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineFiniteVectorIntegral_criticalValue (cusp : CuspidalRepresentation)
    (spherical_cusp : SphericalCusp cusp) {degree : ℕ} (large : 1 < degree)
    (cohomological : Cohomological cusp degree) (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
    (form_nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations (-2 * halfWeight) form eigenvalues)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (eigen : ∀ prime : Nat.Primes, cuspPrimeHeckeSum cusp prime vector =
      ((prime.val : ℂ) ^ (halfWeight + 1) * eigenvalues prime) • vector)
    (integrable : Integrable (fun finite => standardGoodLineFiniteCuspWeight degree cohomologicalPoint finite *
      cusp.realize vector (atFinite (standardGoodLineFiniteCoordinates finite).block))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    goodLineFiniteVectorIntegral degree cusp cohomologicalPoint vector =
      (LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) 3)
          (((-2 * halfWeight : ℤ) : ℂ) - 2) /
        LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) 3)
          (((-2 * halfWeight : ℤ) : ℂ) - 1)) * cusp.realize vector 1 := by
  apply goodLineFiniteVectorIntegral_eq_eulerProduct degree cusp cohomologicalPoint vector nonzero spherical
    (cohomological_localExponent_convergent large)
    (fun place => ((Rat.HeightOneSpectrum.primesEquiv place).val : ℂ) ^ (halfWeight + 1) *
      eigenvalues (Rat.HeightOneSpectrum.primesEquiv place))
  · intro place _
    simpa only [cohomological_cuspLocalPadicCentralChar_eq_one cusp spherical_cusp cohomological place, one_mul] using
      cuspLocalPadicSphereOperator_one_of_hecke_eigen cusp vector spherical place _
        (eigen (Rat.HeightOneSpectrum.primesEquiv place))
  · exact integrable
  · exact cuspCriticalEulerProduct_hasProd cusp spherical_cusp cohomological halfWeight weight form form_nonzero eigenvalues relations

end TernaryPeriodPolynomials.SphericalDetection.Helpers
