module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PadicAdelicNorm
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.NormPowerIntegrability

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspLocalPadicIntegrand (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryFiniteGL) (place : FinitePlace) (exponent : ℂ) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) → ℂ := by
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  exact fun pair =>
    let matrix := base * finiteAtPadicGL 2 place (padicPlanePivotCoordinates pair.1 pair.2).block
    normPower (GeneralLinearGroup.det (atFinite matrix)) exponent * cusp.realize vector (atFinite matrix)

theorem cuspLocalPadicIntegrand_eq (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryFiniteGL) (place : FinitePlace) (exponent : ℂ) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ pair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val],
      cuspLocalPadicIntegrand cusp vector base place exponent pair =
        normPower (GeneralLinearGroup.det (atFinite base)) exponent *
          padicPlaneWeightedValue (padicNormPowerWeight exponent) (cuspLocalPadicValue cusp vector base place) pair := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro pair
  have factor (matrix : GeneralLinearGroup (Fin 2) ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) :
      normPower (GeneralLinearGroup.det (atFinite (base * finiteAtPadicGL 2 place matrix))) exponent =
        normPower (GeneralLinearGroup.det (atFinite base)) exponent *
          padicNormPowerWeight exponent ‖(GeneralLinearGroup.det matrix).val‖ := by
    have determinant := congrArg (GeneralLinearGroup.det (n := Fin 2))
      (atFinite_mul base (finiteAtPadicGL 2 place matrix))
    rw [map_mul] at determinant
    rw [determinant, normPower_mul, normPower_det_finiteAtPadicGL]
    rfl
  change normPower (GeneralLinearGroup.det (atFinite (base * finiteAtPadicGL 2 place
    (padicPlanePivotCoordinates pair.1 pair.2).block))) exponent * _ = _
  rw [factor]
  exact mul_assoc _ _ _

theorem cuspLocalPadicIntegrand_integrable (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (base : BinaryFiniteGL) (place : FinitePlace)
    (exponent : ℂ) (convergent : 2 < exponent.re) :
    Integrable (cuspLocalPadicIntegrand cusp vector base place exponent)
      ((finitePadicMeasure place).prod (finitePadicMeasure place)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have integrable := padicNormPowerWeight_integrable (finitePadicMeasure place) (finitePadicMeasure_normalized place)
    exponent convergent (cuspLocalPadicValue cusp vector base place)
    (cuspLocalPadicValue_right cusp vector spherical base place) (cuspLocalPadicValue_bounded cusp vector base place)
  have equality : cuspLocalPadicIntegrand cusp vector base place exponent = fun pair =>
      normPower (GeneralLinearGroup.det (atFinite base)) exponent *
        padicPlaneWeightedValue (padicNormPowerWeight exponent) (cuspLocalPadicValue cusp vector base place) pair :=
    funext (cuspLocalPadicIntegrand_eq cusp vector base place exponent)
  rw [equality]
  exact integrable.const_mul _

theorem cuspLocalPadicIntegral_series (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (base : BinaryFiniteGL) (place : FinitePlace)
    (exponent : ℂ) (convergent : 2 < exponent.re) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    Summable (padicPrimitiveSeriesTerm (padicNormPowerWeight exponent) (cuspLocalPadicValue cusp vector base place)) ∧
      (∫ pair, cuspLocalPadicIntegrand cusp vector base place exponent pair
        ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) =
        normPower (GeneralLinearGroup.det (atFinite base)) exponent *
          (cusp.realize vector (atFinite base) + ∑' power,
            padicPrimitiveSeriesTerm (padicNormPowerWeight exponent) (cuspLocalPadicValue cusp vector base place) power) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have local_integrable := padicNormPowerWeight_integrable (finitePadicMeasure place) (finitePadicMeasure_normalized place)
    exponent convergent (cuspLocalPadicValue cusp vector base place)
    (cuspLocalPadicValue_right cusp vector spherical base place) (cuspLocalPadicValue_bounded cusp vector base place)
  have series := padicPlaneIntegral_series (finitePadicMeasure place) (finitePadicMeasure_normalized place)
    (padicNormPowerWeight exponent) (cuspLocalPadicValue cusp vector base place)
    (cuspLocalPadicValue_right cusp vector spherical base place) local_integrable
  refine ⟨series.1, ?_⟩
  simp_rw [cuspLocalPadicIntegrand_eq]
  rw [integral_const_mul, series.2, padicNormPowerWeight_one, one_mul, cuspLocalPadicValue_one]

theorem cuspLocalPadicSeriesTerm_realize (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryFiniteGL) (place : FinitePlace) (exponent : ℂ) (power : ℕ) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    padicPrimitiveSeriesTerm (padicNormPowerWeight exponent) (cuspLocalPadicValue cusp vector base place) power =
      (((((Rat.HeightOneSpectrum.primesEquiv place).val ^ (power + 1) : ℕ) : ℝ≥0∞) -
        (((Rat.HeightOneSpectrum.primesEquiv place).val ^ power : ℕ) : ℝ≥0∞)).toReal) •
        (padicNormPowerWeight exponent (((Rat.HeightOneSpectrum.primesEquiv place).val : ℝ) ^ (power + 1))⁻¹ *
          cusp.realize (cuspLocalPadicPrimitiveOperator cusp place (power + 1) vector) (atFinite base)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  rw [cuspLocalPadicPrimitiveOperator_realize]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
