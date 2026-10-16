module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicEulerIntegral
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.SphereSeriesOperatorRelation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspLocalPadicSphereValue_step_one (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (base : BinaryFiniteGL) (place : FinitePlace) :
    cuspLocalPadicSphereValue cusp (cuspLocalPadicSphereOperator cusp place 1 vector) base place 1 =
      cuspLocalPadicSphereValue cusp vector base place 2 +
        ((Rat.HeightOneSpectrum.primesEquiv place).val + 1 : ℂ) * cuspLocalPadicCentralChar cusp place *
          cuspLocalPadicSphereValue cusp vector base place 0 := by
  have identity := congrArg (cuspFiniteEvaluation cusp base)
    (cuspLocalPadicSphereOperator_step_one cusp place vector spherical)
  simp only [map_add, map_nsmul, map_smul, smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at identity
  change _ = _ + (_ + 1) * (cuspLocalPadicCentralChar cusp place * _) at identity
  rw [mul_assoc]
  exact identity

theorem cuspLocalPadicSphereValue_step_succ (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (base : BinaryFiniteGL) (place : FinitePlace) (index : ℕ) :
    cuspLocalPadicSphereValue cusp (cuspLocalPadicSphereOperator cusp place 1 vector) base place (index + 2) =
      cuspLocalPadicSphereValue cusp vector base place (index + 3) +
        (Rat.HeightOneSpectrum.primesEquiv place).val * cuspLocalPadicCentralChar cusp place *
          cuspLocalPadicSphereValue cusp vector base place (index + 1) := by
  have identity := congrArg (cuspFiniteEvaluation cusp base)
    (cuspLocalPadicSphereOperator_step_succ cusp place vector spherical index)
  simp only [map_add, map_nsmul, map_smul, smul_eq_mul, nsmul_eq_mul] at identity
  rw [mul_assoc]
  exact identity

theorem cuspLocalPadicIntegral_operator_relation (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (base : BinaryFiniteGL) (place : FinitePlace)
    (exponent : ℂ) (convergent : 2 < exponent.re) :
    let prime : ℂ := (Rat.HeightOneSpectrum.primesEquiv place).val
    let scale := padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent
    let central := cuspLocalPadicCentralChar cusp place
    (1 + prime * central * scale ^ 2) *
        (∫ pair, cuspLocalPadicIntegrand cusp vector base place exponent pair
          ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) -
      scale * (∫ pair, cuspLocalPadicIntegrand cusp (cuspLocalPadicSphereOperator cusp place 1 vector)
        base place exponent pair ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) =
      normPower (GeneralLinearGroup.det (atFinite base)) exponent *
        ((1 + central / prime * scale ^ 2) * cusp.realize vector (atFinite base) -
          scale / prime * cusp.realize (cuspLocalPadicSphereOperator cusp place 1 vector) (atFinite base)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  dsimp only
  have first_series := cuspLocalPadicIntegral_series cusp vector spherical base place exponent convergent
  have second_series := cuspLocalPadicIntegral_series cusp (cuspLocalPadicSphereOperator cusp place 1 vector)
    (cuspLocalPadicSphereOperator_one_spherical cusp place vector spherical) base place exponent convergent
  have first_summable := first_series.1.congr (cuspLocalPadicSeriesTerm_geometric cusp vector base place exponent)
  have second_summable := second_series.1.congr
    (cuspLocalPadicSeriesTerm_geometric cusp (cuspLocalPadicSphereOperator cusp place 1 vector) base place exponent)
  simp_rw [cuspLocalPadicSeriesTerm_geometric] at first_series second_series
  have identity := sphereSeries_operator_relation
    (cuspLocalPadicSphereValue cusp vector base place)
    (cuspLocalPadicSphereValue cusp (cuspLocalPadicSphereOperator cusp place 1 vector) base place)
    ((Rat.HeightOneSpectrum.primesEquiv place).val : ℂ) (cuspLocalPadicCentralChar cusp place)
    (padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv place).val exponent)
    (by exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv place).property.ne_zero) rfl
    (cuspLocalPadicSphereValue_step_one cusp vector spherical base place)
    (cuspLocalPadicSphereValue_step_succ cusp vector spherical base place) first_summable second_summable
  rw [cuspLocalPadicSphereValue_zero, cuspLocalPadicSphereValue_zero] at identity
  rw [first_series.2, second_series.2]
  have scaled := congrArg (fun value : ℂ => normPower (GeneralLinearGroup.det (atFinite base)) exponent * value) identity
  change _ = _ at scaled
  convert scaled using 1
  · ring
  · rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
