module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicIntegralSquare

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineFinitePadicTruncatedIntegral (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (exponent : ℂ) (places : Finset FinitePlace) : ℂ :=
  ∫ pair in goodLineFiniteSupportRegion places, goodLineFinitePadicIntegrand cusp vector exponent pair
    ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)

def goodLineFinitePadicAwayIntegral (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (exponent : ℂ) (place : FinitePlace) (places : Finset FinitePlace) : ℂ :=
  ∫ awayPair in goodLineAwayPlaceSupportRegion place places,
    let base := (standardGoodLineFinitePadicCoordinates (awayPair.1.val, awayPair.2.val)).block
    normPower (GeneralLinearGroup.det (atFinite base)) exponent * cusp.realize vector (atFinite base)
    ∂((finiteAwayThreePlaceMeasure place).prod (finiteAwayThreePlaceMeasure place))

theorem goodLineFinitePadicTruncatedIntegral_empty (cusp : CuspidalRepresentation) (vector : cusp.smooth) (exponent : ℂ) :
    goodLineFinitePadicTruncatedIntegral cusp vector exponent ∅ = cusp.realize vector 1 := by
  have volume : (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) (goodLineFiniteSupportRegion ∅) = 1 := by
    rw [goodLineFiniteSupportRegion_empty, Measure.prod_prod, finiteAwayThreeMeasure_normalized, one_mul]
  have values : Set.EqOn (goodLineFinitePadicIntegrand cusp vector exponent) (fun _ => cusp.realize vector 1)
      (goodLineFiniteSupportRegion ∅) := by
    intro pair member
    have block : (standardGoodLineFinitePadicCoordinates pair).block = 1 := by
      apply finitePadicGeneralLinearGroup_ext
      intro place
      let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
        ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
      rw [map_one]
      apply standardGoodLineFinitePadicCoordinates_block_integral
      · exact (finiteCompletionPadic_integral_iff place _).mpr (member.1 place (by simp))
      · exact (finiteCompletionPadic_integral_iff place _).mpr (member.2 place (by simp))
    change normPower (GeneralLinearGroup.det (atFinite (standardGoodLineFinitePadicCoordinates pair).block)) exponent *
      cusp.realize vector (atFinite (standardGoodLineFinitePadicCoordinates pair).block) = _
    rw [block, atFinite_one, map_one]
    rw [normPower_one, one_mul]
  rw [goodLineFinitePadicTruncatedIntegral,
    setIntegral_congr_fun (goodLineFiniteSupportRegion_measurable ∅) values, setIntegral_const, Measure.real,
    volume, ENNReal.toReal_one, one_smul]

theorem goodLineFinitePadicTruncatedIntegral_tendsto (degree : ℕ) (cusp : CuspidalRepresentation) (parameter : ℂ)
    (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (integrable : Integrable (fun finite => standardGoodLineFiniteCuspWeight degree parameter finite *
      cusp.realize vector (atFinite (standardGoodLineFiniteCoordinates finite).block))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    Tendsto (goodLineFinitePadicTruncatedIntegral cusp vector ((degree : ℂ) / 2 + 3 + parameter)) atTop
      (nhds (goodLineFiniteVectorIntegral degree cusp parameter vector)) := by
  have limit := goodLineFiniteSupportRegion_integral_tendsto _
    (goodLineFinitePadicIntegrand_integrable degree cusp parameter vector spherical integrable)
  unfold goodLineFiniteVectorIntegral
  simp_rw [goodLineFinitePadicIntegrand_eq degree cusp parameter vector spherical]
  exact limit

end TernaryPeriodPolynomials.SphericalDetection.Helpers
