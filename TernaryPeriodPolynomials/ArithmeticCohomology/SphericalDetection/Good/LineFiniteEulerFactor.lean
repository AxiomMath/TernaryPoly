module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteLocalSeries
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicEulerFactor

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineFiniteVectorIntegral_away_integrable (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (convergent : 2 < ((degree : ℂ) / 2 + 3 + parameter).re)
    (place : FinitePlace) (distinct : place ≠ placeThree) (eigenvalue : ℂ)
    (eigen : cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalue • vector)
    (integrable : Integrable (fun finite => standardGoodLineFiniteCuspWeight degree parameter finite *
      cusp.realize vector (atFinite (standardGoodLineFiniteCoordinates finite).block))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    Integrable (fun awayPair : FiniteAwayThreePlace place × FiniteAwayThreePlace place =>
      let base := (standardGoodLineFinitePadicCoordinates (awayPair.1.val, awayPair.2.val)).block
      normPower (GeneralLinearGroup.det (atFinite base)) ((degree : ℂ) / 2 + 3 + parameter) *
        cusp.realize vector (atFinite base))
      ((finiteAwayThreePlaceMeasure place).prod (finiteAwayThreePlaceMeasure place)) := by
  have converted := goodLineFinitePadicIntegrand_integrable degree cusp parameter vector spherical integrable
  have lifted := (finiteAwayThreePadicRadicalJoin_measurePreserving place distinct).integrable_comp_of_integrable converted
  have integrated := lifted.integral_prod_right
  simp_rw [Function.comp_def, goodLineFinitePadicIntegrand_split,
    cuspLocalPadicIntegral_eulerQuotient cusp vector nonzero spherical _ place _ convergent eigenvalue eigen] at integrated
  have factor_nonzero := cuspLocalPadicEulerFactor_ne_zero cusp vector nonzero spherical place
    ((degree : ℂ) / 2 + 3 + parameter) convergent eigenvalue eigen
  apply (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr factor_nonzero) _).mp
  simpa only [cuspLocalPadicEulerFactor, mul_assoc] using integrated

theorem goodLineFiniteVectorIntegral_local_eulerFactor (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (convergent : 2 < ((degree : ℂ) / 2 + 3 + parameter).re)
    (place : FinitePlace) (distinct : place ≠ placeThree) (eigenvalue : ℂ)
    (eigen : cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalue • vector)
    (integrable : Integrable (fun finite => standardGoodLineFiniteCuspWeight degree parameter finite *
      cusp.realize vector (atFinite (standardGoodLineFiniteCoordinates finite).block))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    goodLineFiniteVectorIntegral degree cusp parameter vector =
      cuspLocalPadicEulerFactor cusp place eigenvalue ((degree : ℂ) / 2 + 3 + parameter) *
        ∫ awayPair : FiniteAwayThreePlace place × FiniteAwayThreePlace place,
          let base := (standardGoodLineFinitePadicCoordinates (awayPair.1.val, awayPair.2.val)).block
          normPower (GeneralLinearGroup.det (atFinite base)) ((degree : ℂ) / 2 + 3 + parameter) *
            cusp.realize vector (atFinite base)
          ∂((finiteAwayThreePlaceMeasure place).prod (finiteAwayThreePlaceMeasure place)) := by
  rw [goodLineFiniteVectorIntegral_local_fubini degree cusp parameter vector spherical place distinct integrable]
  simp_rw [cuspLocalPadicIntegral_eulerQuotient cusp vector nonzero spherical _ place _ convergent eigenvalue eigen]
  simp_rw [cuspLocalPadicEulerFactor, mul_assoc]
  exact integral_const_mul _ _

end TernaryPeriodPolynomials.SphericalDetection.Helpers
