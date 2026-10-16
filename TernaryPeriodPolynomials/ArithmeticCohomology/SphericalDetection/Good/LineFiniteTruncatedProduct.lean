module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteTruncatedFactor

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance finiteTruncatedProductDecidableEq : DecidableEq FinitePlace := Classical.decEq _

theorem finiteAwayThree_evaluation_zero (value : FiniteAwayThree) : finiteEvaluation placeThree value.val = 0 := by
  apply threeCompletionEquiv.injective
  rw [map_zero]
  exact value.property

theorem goodLineFiniteSupportRegion_insert_three (places : Finset FinitePlace) :
    goodLineFiniteSupportRegion (insert placeThree places) = goodLineFiniteSupportRegion places := by
  ext pair
  change (pair.1.val ∈ finiteIntegralOutside (insert placeThree places) ∧
    pair.2.val ∈ finiteIntegralOutside (insert placeThree places)) ↔ _
  rw [finiteIntegralOutside_insert_zero _ _ _ (finiteAwayThree_evaluation_zero pair.1),
    finiteIntegralOutside_insert_zero _ _ _ (finiteAwayThree_evaluation_zero pair.2)]
  rfl

theorem goodLineFinitePadicTruncatedIntegral_insert_three (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (exponent : ℂ) (places : Finset FinitePlace) :
    goodLineFinitePadicTruncatedIntegral cusp vector exponent (insert placeThree places) =
      goodLineFinitePadicTruncatedIntegral cusp vector exponent places := by
  rw [goodLineFinitePadicTruncatedIntegral, goodLineFiniteSupportRegion_insert_three]
  rfl

def cuspLocalPadicEulerFactorAwayThree (cusp : CuspidalRepresentation) (eigenvalues : FinitePlace → ℂ)
    (exponent : ℂ) (place : FinitePlace) : ℂ :=
  if place = placeThree then 1 else cuspLocalPadicEulerFactor cusp place (eigenvalues place) exponent

theorem goodLineFinitePadicTruncatedIntegral_product (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (exponent : ℂ) (convergent : 2 < exponent.re) (eigenvalues : FinitePlace → ℂ)
    (eigen : ∀ place, place ≠ placeThree → cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalues place • vector)
    (integrable : Integrable (goodLineFinitePadicIntegrand cusp vector exponent)
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) (places : Finset FinitePlace) :
    goodLineFinitePadicTruncatedIntegral cusp vector exponent places =
      (∏ place ∈ places, cuspLocalPadicEulerFactorAwayThree cusp eigenvalues exponent place) * cusp.realize vector 1 := by
  induction places using Finset.induction_on with
  | empty => rw [goodLineFinitePadicTruncatedIntegral_empty, Finset.prod_empty, one_mul]
  | @insert place places outside induction =>
    by_cases same : place = placeThree
    · subst place
      rw [goodLineFinitePadicTruncatedIntegral_insert_three, induction, Finset.prod_insert outside,
        cuspLocalPadicEulerFactorAwayThree, ite_eq_left rfl, one_mul]
    · rw [goodLineFinitePadicTruncatedIntegral_insert cusp vector nonzero spherical exponent convergent places place
        same outside (eigenvalues place) (eigen place same) integrable, induction, Finset.prod_insert outside,
        cuspLocalPadicEulerFactorAwayThree, ite_eq_right same, mul_assoc]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
