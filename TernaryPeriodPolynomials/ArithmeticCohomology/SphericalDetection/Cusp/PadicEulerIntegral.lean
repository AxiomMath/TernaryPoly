module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PrimitiveGeometric
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.SphereEulerSeries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspLocalPadicIntegral_mul_eulerFactor (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (base : BinaryFiniteGL) (place : FinitePlace)
    (exponent : ℂ) (convergent : 2 < exponent.re) (eigenvalue : ℂ)
    (eigen : cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalue • vector) :
    let prime : ℂ := (Rat.HeightOneSpectrum.primesEquiv place).val
    let scale := padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent
    let central := cuspLocalPadicCentralChar cusp place
    (1 - eigenvalue * scale + prime * central * scale ^ 2) *
        (∫ pair, cuspLocalPadicIntegrand cusp vector base place exponent pair
          ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) =
      normPower (GeneralLinearGroup.det (atFinite base)) exponent *
        ((1 - eigenvalue / prime * scale + central / prime * scale ^ 2) * cusp.realize vector (atFinite base)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  dsimp only
  have series := cuspLocalPadicIntegral_series cusp vector spherical base place exponent convergent
  have summable := series.1.congr (cuspLocalPadicSeriesTerm_geometric cusp vector base place exponent)
  simp_rw [cuspLocalPadicSeriesTerm_geometric] at series
  have identity := sphereRecurrence_shell_tsum_mul_factor
    (cuspLocalPadicSphereValue cusp vector base place)
    ((Rat.HeightOneSpectrum.primesEquiv place).val : ℂ) eigenvalue (cuspLocalPadicCentralChar cusp place)
    (padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent)
    (by exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv place).property.ne_zero)
    (cuspLocalPadicSphereValue_one cusp vector base place eigenvalue eigen)
    (cuspLocalPadicSphereValue_two cusp vector spherical base place eigenvalue eigen)
    (cuspLocalPadicSphereValue_recurrence cusp vector spherical base place eigenvalue eigen) summable
  rw [cuspLocalPadicSphereValue_zero] at identity
  rw [series.2, ← mul_assoc, mul_comm _ (normPower _ _), mul_assoc, identity]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
