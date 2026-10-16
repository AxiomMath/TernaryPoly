module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicRealAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Euler.Denominator
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.SeriesScaleNorm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspLocalPadicEulerDenominator_ne_zero (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp) (place : FinitePlace)
    (exponent : ℂ) (convergent : 2 < exponent.re) (eigenvalue : ℂ)
    (eigen : cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalue • vector) :
    let prime : ℂ := (Rat.HeightOneSpectrum.primesEquiv place).val
    let scale := padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent
    1 - eigenvalue * scale + prime * cuspLocalPadicCentralChar cusp place * scale ^ 2 ≠ 0 := by
  obtain ⟨real, base, value_nonzero⟩ := cuspSmoothAction_real_exists_finite_value_ne_zero cusp vector nonzero
  have shifted_spherical := cuspSmoothAction_real_spherical cusp vector spherical real
  have shifted_eigen : cuspLocalPadicSphereOperator cusp place 1
      (cuspSmoothAction cusp (atInfinity real) vector) =
        eigenvalue • cuspSmoothAction cusp (atInfinity real) vector := by
    rw [cuspLocalPadicSphereOperator_real_commute, eigen, map_smul]
  have identity := cuspLocalPadicIntegral_mul_eulerFactor cusp
    (cuspSmoothAction cusp (atInfinity real) vector) shifted_spherical base place exponent convergent eigenvalue shifted_eigen
  dsimp only at identity ⊢
  apply quadraticEulerDenominator_ne_zero_of_identity _ _ _ _
    (normPower (GeneralLinearGroup.det (atFinite base)) exponent *
      cusp.realize (cuspSmoothAction cusp (atInfinity real) vector) (atFinite base)) _
  · exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv place).property.ne_zero
  · exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv place).property.ne_one
  · exact cusp.centralUnitary _
  · exact padicPrimitiveSeriesScale_norm_lt_one _ (Rat.HeightOneSpectrum.primesEquiv place).property.one_lt
      exponent (by linarith)
  · exact mul_ne_zero (normPower_ne_zero _ _) value_nonzero
  · simpa only [mul_left_comm] using identity

theorem cuspLocalPadicIntegral_eulerQuotient (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp) (base : BinaryFiniteGL) (place : FinitePlace)
    (exponent : ℂ) (convergent : 2 < exponent.re) (eigenvalue : ℂ)
    (eigen : cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalue • vector) :
    let prime : ℂ := (Rat.HeightOneSpectrum.primesEquiv place).val
    let scale := padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent
    let central := cuspLocalPadicCentralChar cusp place
    (∫ pair, cuspLocalPadicIntegrand cusp vector base place exponent pair
        ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) =
      ((1 - eigenvalue / prime * scale + central / prime * scale ^ 2) /
        (1 - eigenvalue * scale + prime * central * scale ^ 2)) *
        normPower (GeneralLinearGroup.det (atFinite base)) exponent * cusp.realize vector (atFinite base) := by
  have denominator := cuspLocalPadicEulerDenominator_ne_zero cusp vector nonzero spherical place exponent convergent eigenvalue eigen
  have identity := cuspLocalPadicIntegral_mul_eulerFactor cusp vector spherical base place exponent convergent eigenvalue eigen
  dsimp only at denominator identity ⊢
  have solved := (eq_div_iff denominator).mpr ((mul_comm _ _).trans identity)
  rw [solved]
  ring

end TernaryPeriodPolynomials.SphericalDetection.Helpers
