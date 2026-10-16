module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PadicCoordinateSplitting

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def finitePadicRadicalJoin (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ((ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) ×
      (FiniteAwayPlace place × FiniteAwayPlace place)) ≃ₜ (FiniteAdeles × FiniteAdeles) :=
  (Homeomorph.prodProdProdComm _ _ _ _).trans
    ((finitePadicSplit place).symm.toHomeomorph.prodCongr (finitePadicSplit place).symm.toHomeomorph)

theorem finitePadicRadicalJoin_apply (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ pair : (ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) ×
      (FiniteAwayPlace place × FiniteAwayPlace place),
      finitePadicRadicalJoin place pair =
        ((finitePadicSplit place).symm (pair.1.1, pair.2.1), (finitePadicSplit place).symm (pair.1.2, pair.2.2)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro pair
  rfl

theorem finitePadicRadicalJoin_measurePreserving (place : FinitePlace) :
    MeasurePreserving (finitePadicRadicalJoin place)
      (((finitePadicMeasure place).prod (finitePadicMeasure place)).prod
        ((finiteAwayPlaceMeasure place).prod (finiteAwayPlaceMeasure place)))
      (finiteMeasure.prod finiteMeasure) :=
  ((finitePadicSplit_symm_measurePreserving place).prod (finitePadicSplit_symm_measurePreserving place)).comp
    (measurePreserving_prodTranspose (finitePadicMeasure place) (finitePadicMeasure place)
      (finiteAwayPlaceMeasure place) (finiteAwayPlaceMeasure place))

def finitePadicCuspIntegrand (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (exponent : ℂ) (pair : FiniteAdeles × FiniteAdeles) : ℂ :=
  let block := (finitePadicPlaneCoordinates pair.1 pair.2).block
  normPower (GeneralLinearGroup.det (atFinite block)) exponent * cusp.realize vector (atFinite block)

theorem finitePadicCuspIntegrand_split (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (exponent : ℂ) (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localPair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
      (awayPair : FiniteAwayPlace place × FiniteAwayPlace place),
      finitePadicCuspIntegrand cusp vector exponent (finitePadicRadicalJoin place (localPair, awayPair)) =
        cuspLocalPadicIntegrand cusp vector (finitePadicPlaneCoordinates awayPair.1.val awayPair.2.val).block
          place exponent localPair := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localPair awayPair
  unfold finitePadicCuspIntegrand
  rw [finitePadicRadicalJoin_apply, finitePadicPlaneCoordinates_split_block]
  rfl

theorem finitePadicCuspIntegral_fubini (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (exponent : ℂ) (place : FinitePlace)
    (integrable : Integrable (finitePadicCuspIntegrand cusp vector exponent) (finiteMeasure.prod finiteMeasure)) :
    (∫ pair, finitePadicCuspIntegrand cusp vector exponent pair ∂(finiteMeasure.prod finiteMeasure)) =
      ∫ awayPair : FiniteAwayPlace place × FiniteAwayPlace place,
        ∫ localPair, cuspLocalPadicIntegrand cusp vector
          (finitePadicPlaneCoordinates awayPair.1.val awayPair.2.val).block place exponent localPair
          ∂((finitePadicMeasure place).prod (finitePadicMeasure place))
        ∂((finiteAwayPlaceMeasure place).prod (finiteAwayPlaceMeasure place)) := by
  have lifted := (finitePadicRadicalJoin_measurePreserving place).integrable_comp_of_integrable integrable
  simp only [Function.comp_def] at lifted
  rw [← (finitePadicRadicalJoin_measurePreserving place).integral_comp
    (finitePadicRadicalJoin place).measurableEmbedding, integral_prod_symm _ lifted]
  simp_rw [finitePadicCuspIntegrand_split]

theorem finitePadicCuspIntegral_local_series (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (exponent : ℂ) (convergent : 2 < exponent.re)
    (place : FinitePlace)
    (integrable : Integrable (finitePadicCuspIntegrand cusp vector exponent) (finiteMeasure.prod finiteMeasure)) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (∫ pair, finitePadicCuspIntegrand cusp vector exponent pair ∂(finiteMeasure.prod finiteMeasure)) =
      ∫ awayPair : FiniteAwayPlace place × FiniteAwayPlace place,
        let base := (finitePadicPlaneCoordinates awayPair.1.val awayPair.2.val).block
        normPower (GeneralLinearGroup.det (atFinite base)) exponent *
          (cusp.realize vector (atFinite base) + ∑' power,
            padicPrimitiveSeriesTerm (padicNormPowerWeight exponent) (cuspLocalPadicValue cusp vector base place) power)
        ∂((finiteAwayPlaceMeasure place).prod (finiteAwayPlaceMeasure place)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  rw [finitePadicCuspIntegral_fubini cusp vector exponent place integrable]
  apply integral_congr_ae
  filter_upwards [] with awayPair
  exact (cuspLocalPadicIntegral_series cusp vector spherical _ place exponent convergent).2

end TernaryPeriodPolynomials.SphericalDetection.Helpers
