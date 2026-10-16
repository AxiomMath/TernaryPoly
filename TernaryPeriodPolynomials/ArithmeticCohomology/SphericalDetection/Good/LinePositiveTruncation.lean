module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePositiveWeight
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteTruncatedProduct

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance goodLinePositiveTruncationDecidableEq : DecidableEq FinitePlace := Classical.decEq _

theorem goodLinePositiveWeight_away_integrable (exponent : ℂ) (places : Finset FinitePlace)
    (place : FinitePlace) (distinct : place ≠ placeThree) (outside : place ∉ places)
    (integrable : IntegrableOn (goodLinePositiveWeight exponent) (goodLineFiniteSupportRegion places)
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    IntegrableOn (fun awayPair : FiniteAwayThreePlace place × FiniteAwayThreePlace place =>
      goodLinePositiveWeight exponent (awayPair.1.val, awayPair.2.val)) (goodLineAwayPlaceSupportRegion place places)
      ((finiteAwayThreePlaceMeasure place).prod (finiteAwayThreePlaceMeasure place)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have lifted := ((finiteAwayThreePadicRadicalJoin_measurePreserving place distinct).restrict_preimage
    (goodLineFiniteSupportRegion_measurable places)).integrable_comp_of_integrable integrable
  rw [goodLineFiniteSupportRegion_padic_preimage places place distinct outside, ← Measure.prod_restrict] at lifted
  have integrated := lifted.integral_prod_right
  simp only [Function.comp_def] at integrated
  simp_rw [goodLinePositiveWeight_split, integral_mul_const] at integrated
  change Integrable (fun awayPair : FiniteAwayThreePlace place × FiniteAwayThreePlace place =>
    (∫ pair in padicPlaneIntegrationRegion 0, padicPositiveWeight exponent pair
      ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) *
        goodLinePositiveWeight exponent (awayPair.1.val, awayPair.2.val)) _ at integrated
  simp only [padicPositiveWeight_square_integral, one_mul] at integrated
  exact integrated

theorem goodLinePositiveWeight_insert_integrable (exponent : ℂ) (convergent : 2 < exponent.re)
    (places : Finset FinitePlace) (place : FinitePlace) (distinct : place ≠ placeThree)
    (away_integrable : IntegrableOn (fun awayPair : FiniteAwayThreePlace place × FiniteAwayThreePlace place =>
      goodLinePositiveWeight exponent (awayPair.1.val, awayPair.2.val)) (goodLineAwayPlaceSupportRegion place places)
      ((finiteAwayThreePlaceMeasure place).prod (finiteAwayThreePlaceMeasure place))) :
    IntegrableOn (goodLinePositiveWeight exponent) (goodLineFiniteSupportRegion (insert place places))
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  apply (((finiteAwayThreePadicRadicalJoin_measurePreserving place distinct).restrict_preimage
    (goodLineFiniteSupportRegion_measurable (insert place places))).integrable_comp_emb
      (finiteAwayThreePadicRadicalJoin place distinct).measurableEmbedding).mp
  rw [goodLineFiniteSupportRegion_padic_preimage_insert, ← Measure.prod_restrict, Measure.restrict_univ]
  have local_integrable := padicPositiveWeight_integrable (finitePadicMeasure place)
    (finitePadicMeasure_normalized place) exponent convergent
  exact (local_integrable.mul_prod away_integrable).congr (Filter.Eventually.of_forall (fun pair =>
    (goodLinePositiveWeight_split exponent place distinct pair.1 pair.2).symm))

theorem goodLinePositiveWeight_truncated_integrable (exponent : ℂ) (convergent : 2 < exponent.re)
    (places : Finset FinitePlace) :
    IntegrableOn (goodLinePositiveWeight exponent) (goodLineFiniteSupportRegion places)
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  induction places using Finset.induction_on with
  | empty => exact goodLinePositiveWeight_empty_integrable exponent
  | @insert place places outside induction =>
      by_cases same : place = placeThree
      · subst place
        rwa [goodLineFiniteSupportRegion_insert_three]
      · exact goodLinePositiveWeight_insert_integrable exponent convergent places place same
          (goodLinePositiveWeight_away_integrable exponent places place same outside induction)

theorem goodLinePositiveWeight_away_integral (exponent : ℂ) (places : Finset FinitePlace)
    (place : FinitePlace) (distinct : place ≠ placeThree) (outside : place ∉ places) :
    (∫ pair in goodLineFiniteSupportRegion places, goodLinePositiveWeight exponent pair
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) =
    ∫ awayPair in goodLineAwayPlaceSupportRegion place places,
      goodLinePositiveWeight exponent (awayPair.1.val, awayPair.2.val)
      ∂((finiteAwayThreePlaceMeasure place).prod (finiteAwayThreePlaceMeasure place)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  rw [← (finiteAwayThreePadicRadicalJoin_measurePreserving place distinct).setIntegral_preimage_emb
    (finiteAwayThreePadicRadicalJoin place distinct).measurableEmbedding,
    goodLineFiniteSupportRegion_padic_preimage places place distinct outside]
  have split (pair : (ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) ×
      (FiniteAwayThreePlace place × FiniteAwayThreePlace place)) :
      goodLinePositiveWeight exponent (finiteAwayThreePadicRadicalJoin place distinct pair) =
        padicPositiveWeight exponent pair.1 * goodLinePositiveWeight exponent (pair.2.1.val, pair.2.2.val) :=
    goodLinePositiveWeight_split exponent place distinct pair.1 pair.2
  simp_rw [split]
  rw [setIntegral_prod_mul (padicPositiveWeight (prime := (Rat.HeightOneSpectrum.primesEquiv place).val) exponent)
    (fun awayPair : FiniteAwayThreePlace place × FiniteAwayThreePlace place =>
      goodLinePositiveWeight exponent (awayPair.1.val, awayPair.2.val))]
  change (∫ pair in padicPlaneIntegrationRegion 0, padicPositiveWeight exponent pair
    ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) * _ = _
  rw [padicPositiveWeight_square_integral, one_mul]

theorem goodLinePositiveWeight_insert_integral (exponent : ℂ) (places : Finset FinitePlace)
    (place : FinitePlace) (distinct : place ≠ placeThree) (outside : place ∉ places) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (∫ pair in goodLineFiniteSupportRegion (insert place places), goodLinePositiveWeight exponent pair
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) =
    (∫ pair, padicPositiveWeight exponent pair ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) *
      ∫ pair in goodLineFiniteSupportRegion places, goodLinePositiveWeight exponent pair
        ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  rw [← (finiteAwayThreePadicRadicalJoin_measurePreserving place distinct).setIntegral_preimage_emb
    (finiteAwayThreePadicRadicalJoin place distinct).measurableEmbedding,
    goodLineFiniteSupportRegion_padic_preimage_insert]
  have split (pair : (ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] ×
      ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val]) ×
      (FiniteAwayThreePlace place × FiniteAwayThreePlace place)) :
      goodLinePositiveWeight exponent (finiteAwayThreePadicRadicalJoin place distinct pair) =
        padicPositiveWeight exponent pair.1 * goodLinePositiveWeight exponent (pair.2.1.val, pair.2.2.val) :=
    goodLinePositiveWeight_split exponent place distinct pair.1 pair.2
  simp_rw [split]
  rw [setIntegral_prod_mul (padicPositiveWeight (prime := (Rat.HeightOneSpectrum.primesEquiv place).val) exponent)
    (fun awayPair : FiniteAwayThreePlace place × FiniteAwayThreePlace place =>
      goodLinePositiveWeight exponent (awayPair.1.val, awayPair.2.val)), setIntegral_univ, goodLinePositiveWeight_away_integral exponent places place distinct outside]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
