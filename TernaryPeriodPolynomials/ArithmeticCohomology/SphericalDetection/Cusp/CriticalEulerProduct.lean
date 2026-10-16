module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PrimeAwayThree
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.EulerRatio

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspCriticalEulerProduct_hasProd (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree)
    (halfWeight : ℤ) (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations (-2 * halfWeight) form eigenvalues) :
    HasProd (fun place : {place : FinitePlace // place ≠ placeThree} =>
      cuspLocalPadicEulerFactor cusp place.val
        (((Rat.HeightOneSpectrum.primesEquiv place.val).val : ℂ) ^ (halfWeight + 1) *
          eigenvalues (Rat.HeightOneSpectrum.primesEquiv place.val))
        ((degree : ℂ) / 2 + 3 + cohomologicalPoint))
      (LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) 3)
          (((-2 * halfWeight : ℤ) : ℂ) - 2) /
        LSeries (removeEulerCoefficients (fun index => (UpperHalfPlane.qExpansion 1 form).coeff index) 3)
          (((-2 * halfWeight : ℤ) : ℂ) - 1)) := by
  have product := (finitePlaceAwayThreeEquivPrime.hasProd_iff).mpr
    (levelOneCuspForm_classicalEuler_outerRatio form nonzero eigenvalues relations 3)
  apply product.congr_fun
  intro place
  dsimp only [Function.comp_def]
  rw [finitePlaceAwayThreeEquivPrime_val, cuspLocalPadicEulerFactor_cohomological cusp spherical cohomological
    place.val halfWeight weight]
  have weight_eq : -2 * halfWeight = (degree : ℤ) + 3 := by omega
  rw [weight_eq]
  push_cast
  congr 2 <;> ring

theorem cuspCriticalEulerProduct_ne_zero (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree)
    (halfWeight : ℤ) (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight))
    (nonzero : form ≠ 0) (eigenvalues : Nat.Primes → ℂ)
    (relations : HasPrimeHeckeRelations (-2 * halfWeight) form eigenvalues) :
    (∏' place : {place : FinitePlace // place ≠ placeThree},
      cuspLocalPadicEulerFactor cusp place.val
        (((Rat.HeightOneSpectrum.primesEquiv place.val).val : ℂ) ^ (halfWeight + 1) *
          eigenvalues (Rat.HeightOneSpectrum.primesEquiv place.val))
        ((degree : ℂ) / 2 + 3 + cohomologicalPoint)) ≠ 0 := by
  rw [(cuspCriticalEulerProduct_hasProd cusp spherical cohomological halfWeight weight form nonzero eigenvalues relations).tprod_eq]
  have values := levelOneCuspForm_hecke_outerLValues_ne_zero_of_nonzero form nonzero 3 eigenvalues relations
  simp only [Complex.ofReal_sub, Complex.ofReal_intCast, Complex.ofReal_ofNat, Complex.ofReal_one] at values
  exact div_ne_zero values.1 values.2

end TernaryPeriodPolynomials.SphericalDetection.Helpers
