module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteGlobalIntegrability
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.WeightedExponentialIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineFiniteLogNorm (pair : FiniteAwayThree × FiniteAwayThree) : ℝ :=
  Real.log (adeleNorm (GeneralLinearGroup.det
    (atFinite (standardGoodLineFinitePadicCoordinates pair).block)) : ℝ)

theorem goodLinePositiveWeight_eq_exp (exponent : ℂ) (pair : FiniteAwayThree × FiniteAwayThree) :
    goodLinePositiveWeight exponent pair = Real.exp (exponent.re * goodLineFiniteLogNorm pair) := by
  simp only [goodLinePositiveWeight, normPower, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, goodLineFiniteLogNorm]

theorem goodLineFiniteLogNorm_aemeasurable :
    AEMeasurable goodLineFiniteLogNorm (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  have measurable := ((goodLinePositiveWeight_integrable 4 (by norm_num)).aestronglyMeasurable.aemeasurable.log).div_const 4
  have equality (pair : FiniteAwayThree × FiniteAwayThree) :
      Real.log (goodLinePositiveWeight 4 pair) / 4 = goodLineFiniteLogNorm pair := by
    rw [goodLinePositiveWeight_eq_exp, Real.log_exp]
    norm_num
  simpa only [equality] using measurable

theorem goodLineFiniteLogNorm_exp_integrable (exponent : ℝ) (convergent : 3 < exponent) :
    Integrable (fun pair => Real.exp (exponent * goodLineFiniteLogNorm pair))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  exact (goodLinePositiveWeight_integrable (exponent : ℂ) convergent).congr
    (Filter.Eventually.of_forall (goodLinePositiveWeight_eq_exp (exponent : ℂ)))

theorem goodLineFinitePadicIntegrand_eq_exp (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (exponent : ℂ) (pair : FiniteAwayThree × FiniteAwayThree) :
    goodLineFinitePadicIntegrand cusp vector exponent pair =
      Complex.exp (exponent * (goodLineFiniteLogNorm pair : ℂ)) *
        cusp.realize vector (atFinite (standardGoodLineFinitePadicCoordinates pair).block) := rfl

theorem goodLineFinitePadicValue_aemeasurable (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) :
    AEMeasurable (fun pair => cusp.realize vector (atFinite (standardGoodLineFinitePadicCoordinates pair).block))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  have measurable := (goodLineFinitePadicIntegrand_continuous cusp vector spherical 0).aestronglyMeasurable.aemeasurable
    (μ := finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)
  have equality : goodLineFinitePadicIntegrand cusp vector 0 = fun pair =>
      cusp.realize vector (atFinite (standardGoodLineFinitePadicCoordinates pair).block) := by
    funext pair
    rw [goodLineFinitePadicIntegrand_eq_exp, zero_mul, Complex.exp_zero, one_mul]
  rwa [equality] at measurable

theorem goodLineFinitePadicIntegral_analyticAt (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (exponent : ℂ) (convergent : 3 < exponent.re) :
    AnalyticAt ℂ (fun exponent => ∫ pair, goodLineFinitePadicIntegrand cusp vector exponent pair
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) exponent := by
  obtain ⟨bound, bounded⟩ := cusp.bounded vector
  exact weightedExponentialIntegral_analyticAt (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)
    goodLineFiniteLogNorm (fun pair => cusp.realize vector (atFinite (standardGoodLineFinitePadicCoordinates pair).block))
    goodLineFiniteLogNorm_aemeasurable (goodLineFinitePadicValue_aemeasurable cusp vector spherical)
    bound (fun pair => bounded _) 3 goodLineFiniteLogNorm_exp_integrable exponent convergent

theorem goodLineFiniteVectorIntegral_analyticAt (degree : ℕ) (cusp : CuspidalRepresentation)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) (parameter : ℂ)
    (convergent : 3 < ((degree : ℂ) / 2 + 3 + parameter).re) :
    AnalyticAt ℂ (fun parameter => goodLineFiniteVectorIntegral degree cusp parameter vector) parameter := by
  have analytic := (goodLineFinitePadicIntegral_analyticAt cusp vector spherical _ convergent).comp
    (analyticAt_const.add analyticAt_id)
  have equality : (fun parameter => goodLineFiniteVectorIntegral degree cusp parameter vector) =
      fun parameter => ∫ pair, goodLineFinitePadicIntegrand cusp vector ((degree : ℂ) / 2 + 3 + parameter) pair
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
    funext parameter
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (goodLineFinitePadicIntegrand_eq degree cusp parameter vector spherical)
  rw [equality]
  exact analytic

theorem goodLineFiniteVectorIntegral_endpoint_analytic (degree : ℕ) (large : 3 < degree)
    (cusp : CuspidalRepresentation) (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp) :
    AnalyticAt ℂ (fun parameter => goodLineFiniteVectorIntegral degree cusp parameter vector) cohomologicalPoint := by
  apply goodLineFiniteVectorIntegral_analyticAt degree cusp vector spherical
  have degree_large : (3 : ℝ) < degree := by exact_mod_cast large
  norm_num [cohomologicalPoint, Complex.add_re, Complex.div_re]
  linarith

end TernaryPeriodPolynomials.SphericalDetection.Helpers
