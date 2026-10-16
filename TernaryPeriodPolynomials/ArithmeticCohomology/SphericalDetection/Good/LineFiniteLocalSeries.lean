module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFinitePadicSplitting

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem goodLineFinitePadicIntegrand_integrable (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (integrable : Integrable (fun finite => standardGoodLineFiniteCuspWeight degree parameter finite *
      cusp.realize vector (atFinite (standardGoodLineFiniteCoordinates finite).block))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    Integrable (goodLineFinitePadicIntegrand cusp vector ((degree : ℂ) / 2 + 3 + parameter))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) :=
  integrable.congr (Filter.Eventually.of_forall (goodLineFinitePadicIntegrand_eq degree cusp parameter vector spherical))

theorem goodLineFiniteVectorIntegral_local_fubini (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (place : FinitePlace) (distinct : place ≠ placeThree)
    (integrable : Integrable (fun finite => standardGoodLineFiniteCuspWeight degree parameter finite *
      cusp.realize vector (atFinite (standardGoodLineFiniteCoordinates finite).block))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    goodLineFiniteVectorIntegral degree cusp parameter vector =
      ∫ awayPair : FiniteAwayThreePlace place × FiniteAwayThreePlace place,
        ∫ localPair, cuspLocalPadicIntegrand cusp vector
          (standardGoodLineFinitePadicCoordinates (awayPair.1.val, awayPair.2.val)).block place
          ((degree : ℂ) / 2 + 3 + parameter) localPair
          ∂((finitePadicMeasure place).prod (finitePadicMeasure place))
        ∂((finiteAwayThreePlaceMeasure place).prod (finiteAwayThreePlaceMeasure place)) := by
  have converted := goodLineFinitePadicIntegrand_integrable degree cusp parameter vector spherical integrable
  have lifted := (finiteAwayThreePadicRadicalJoin_measurePreserving place distinct).integrable_comp_of_integrable converted
  simp only [Function.comp_def] at lifted
  unfold goodLineFiniteVectorIntegral
  simp_rw [goodLineFinitePadicIntegrand_eq degree cusp parameter vector spherical]
  rw [← (finiteAwayThreePadicRadicalJoin_measurePreserving place distinct).integral_comp
    (finiteAwayThreePadicRadicalJoin place distinct).measurableEmbedding, integral_prod_symm _ lifted]
  simp_rw [goodLineFinitePadicIntegrand_split]

theorem goodLineFiniteVectorIntegral_local_series (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (convergent : 2 < ((degree : ℂ) / 2 + 3 + parameter).re)
    (place : FinitePlace) (distinct : place ≠ placeThree)
    (integrable : Integrable (fun finite => standardGoodLineFiniteCuspWeight degree parameter finite *
      cusp.realize vector (atFinite (standardGoodLineFiniteCoordinates finite).block))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    goodLineFiniteVectorIntegral degree cusp parameter vector =
      ∫ awayPair : FiniteAwayThreePlace place × FiniteAwayThreePlace place,
        let base := (standardGoodLineFinitePadicCoordinates (awayPair.1.val, awayPair.2.val)).block
        normPower (GeneralLinearGroup.det (atFinite base)) ((degree : ℂ) / 2 + 3 + parameter) *
          (cusp.realize vector (atFinite base) + ∑' power,
            padicPrimitiveSeriesTerm (padicNormPowerWeight ((degree : ℂ) / 2 + 3 + parameter))
              (cuspLocalPadicValue cusp vector base place) power)
        ∂((finiteAwayThreePlaceMeasure place).prod (finiteAwayThreePlaceMeasure place)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  rw [goodLineFiniteVectorIntegral_local_fubini degree cusp parameter vector spherical place distinct integrable]
  apply integral_congr_ae
  filter_upwards [] with awayPair
  exact (cuspLocalPadicIntegral_series cusp vector spherical _ place ((degree : ℂ) / 2 + 3 + parameter) convergent).2

end TernaryPeriodPolynomials.SphericalDetection.Helpers
