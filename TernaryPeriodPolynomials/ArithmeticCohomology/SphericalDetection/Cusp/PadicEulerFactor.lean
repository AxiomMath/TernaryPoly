module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicEulerQuotient

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspLocalPadicEulerFactor (cusp : CuspidalRepresentation) (place : FinitePlace)
    (eigenvalue exponent : ℂ) : ℂ :=
  let prime : ℂ := (Rat.HeightOneSpectrum.primesEquiv place).val
  let scale := padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent
  let central := cuspLocalPadicCentralChar cusp place
  (1 - eigenvalue / prime * scale + central / prime * scale ^ 2) /
    (1 - eigenvalue * scale + prime * central * scale ^ 2)

theorem cuspLocalPadicEulerFactor_ne_zero (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp) (place : FinitePlace)
    (exponent : ℂ) (convergent : 2 < exponent.re) (eigenvalue : ℂ)
    (eigen : cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalue • vector) :
    cuspLocalPadicEulerFactor cusp place eigenvalue exponent ≠ 0 := by
  have prime_nonzero : ((Rat.HeightOneSpectrum.primesEquiv place).val : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Rat.HeightOneSpectrum.primesEquiv place).property.ne_zero
  have denominator := cuspLocalPadicEulerDenominator_ne_zero cusp vector nonzero spherical place exponent convergent eigenvalue eigen
  have numerator := cuspLocalPadicEulerDenominator_ne_zero cusp vector nonzero spherical place (exponent + 1)
    (by simp only [Complex.add_re, Complex.one_re]; linarith) eigenvalue eigen
  dsimp only at denominator numerator
  rw [padicPrimitiveSeriesScale_add_one _ (Rat.HeightOneSpectrum.primesEquiv place).property.pos] at numerator
  have numerator_eq :
      1 - eigenvalue * (padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent /
          (Rat.HeightOneSpectrum.primesEquiv place).val) +
        (Rat.HeightOneSpectrum.primesEquiv place).val * cuspLocalPadicCentralChar cusp place *
          (padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent /
            (Rat.HeightOneSpectrum.primesEquiv place).val) ^ 2 =
      1 - eigenvalue / (Rat.HeightOneSpectrum.primesEquiv place).val *
          padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent +
        cuspLocalPadicCentralChar cusp place / (Rat.HeightOneSpectrum.primesEquiv place).val *
          padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent ^ 2 := by
    field_simp
  rw [numerator_eq] at numerator
  exact div_ne_zero numerator denominator

theorem cuspLocalPadicSphereOperator_one_of_hecke_eigen (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (place : FinitePlace) (eigenvalue : ℂ)
    (eigen : cuspPrimeHeckeSum cusp (Rat.HeightOneSpectrum.primesEquiv place) vector = eigenvalue • vector) :
    cuspLocalPadicSphereOperator cusp place 1 vector =
      (cuspLocalPadicCentralChar cusp place * eigenvalue) • vector := by
  rw [cuspLocalPadicSphereOperator_one cusp vector spherical place, eigen, smul_smul]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
