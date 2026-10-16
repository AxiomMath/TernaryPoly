module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.SupportRegionSplitting
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PositiveWeight

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLinePositiveWeight (exponent : ℂ) (pair : FiniteAwayThree × FiniteAwayThree) : ℝ :=
  ‖normPower (GeneralLinearGroup.det
    (atFinite (standardGoodLineFinitePadicCoordinates pair).block)) exponent‖

theorem goodLinePositiveWeight_nonneg (exponent : ℂ) (pair : FiniteAwayThree × FiniteAwayThree) :
    0 ≤ goodLinePositiveWeight exponent pair := norm_nonneg _

theorem goodLinePositiveWeight_split (exponent : ℂ) (place : FinitePlace) (distinct : place ≠ placeThree) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localPair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
      (awayPair : FiniteAwayThreePlace place × FiniteAwayThreePlace place),
      goodLinePositiveWeight exponent (finiteAwayThreePadicRadicalJoin place distinct (localPair, awayPair)) =
        padicPositiveWeight exponent localPair * goodLinePositiveWeight exponent (awayPair.1.val, awayPair.2.val) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localPair awayPair
  rw [goodLinePositiveWeight, standardGoodLineFinitePadicCoordinates_split_block,
    atFinite_mul, map_mul, normPower_mul, norm_mul, normPower_det_finiteAtPadicGL]
  exact mul_comm _ _

theorem goodLinePositiveWeight_empty (exponent : ℂ) (pair : FiniteAwayThree × FiniteAwayThree)
    (member : pair ∈ goodLineFiniteSupportRegion ∅) : goodLinePositiveWeight exponent pair = 1 := by
  have block : (standardGoodLineFinitePadicCoordinates pair).block = 1 := by
    apply finitePadicGeneralLinearGroup_ext
    intro place
    let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    rw [map_one]
    exact standardGoodLineFinitePadicCoordinates_block_integral pair place
      ((finiteCompletionPadic_integral_iff place _).mpr (member.1 place (by simp)))
      ((finiteCompletionPadic_integral_iff place _).mpr (member.2 place (by simp)))
  rw [goodLinePositiveWeight, block, atFinite_one, map_one, normPower_one, norm_one]

theorem goodLineFiniteSupportRegion_empty_measure :
    (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) (goodLineFiniteSupportRegion ∅) = 1 := by
  rw [goodLineFiniteSupportRegion_empty, Measure.prod_prod, finiteAwayThreeMeasure_normalized, one_mul]

theorem goodLinePositiveWeight_empty_integrable (exponent : ℂ) :
    IntegrableOn (goodLinePositiveWeight exponent) (goodLineFiniteSupportRegion ∅)
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure) := by
  apply (integrableOn_const (show (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)
    (goodLineFiniteSupportRegion ∅) ≠ ⊤ by rw [goodLineFiniteSupportRegion_empty_measure]; exact ENNReal.one_ne_top)
    (C := (1 : ℝ))).congr_fun
    (fun pair member => (goodLinePositiveWeight_empty exponent pair member).symm)
    (goodLineFiniteSupportRegion_measurable ∅)

theorem goodLinePositiveWeight_empty_integral (exponent : ℂ) :
    (∫ pair in goodLineFiniteSupportRegion ∅, goodLinePositiveWeight exponent pair
      ∂(finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) = 1 := by
  rw [setIntegral_congr_fun (goodLineFiniteSupportRegion_measurable ∅) (goodLinePositiveWeight_empty exponent),
    setIntegral_const, Measure.real, goodLineFiniteSupportRegion_empty_measure,
    ENNReal.toReal_one, smul_eq_mul, mul_one]

theorem padicPositiveWeight_square_integral (place : FinitePlace) (exponent : ℂ) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (∫ pair in padicPlaneIntegrationRegion 0, padicPositiveWeight exponent pair
      ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) = 1 := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have volume : ((finitePadicMeasure place).prod (finitePadicMeasure place))
      (padicPlaneIntegrationRegion 0) = 1 := by
    change ((finitePadicMeasure place).prod (finitePadicMeasure place))
      ({value | ‖value‖ ≤ 1} ×ˢ {value | ‖value‖ ≤ 1}) = 1
    rw [Measure.prod_prod, finitePadicMeasure_normalized, one_mul]
  rw [setIntegral_congr_fun (padicPlaneIntegrationRegion_measurable 0) (padicPositiveWeight_square exponent),
    setIntegral_const, Measure.real, volume, ENNReal.toReal_one, smul_eq_mul, mul_one]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
