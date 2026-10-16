module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteTruncation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance finiteTruncatedFactorDecidableEq : DecidableEq FinitePlace := Classical.decEq _

theorem goodLineFinitePadicTruncatedIntegral_away (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (exponent : ℂ) (places : Finset FinitePlace) (place : FinitePlace)
    (distinct : place ≠ placeThree) (outside : place ∉ places)
    (integrable : Integrable (goodLineFinitePadicIntegrand cusp vector exponent)
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    goodLineFinitePadicTruncatedIntegral cusp vector exponent places =
      goodLineFinitePadicAwayIntegral cusp vector exponent place places := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have lifted := (finiteAwayThreePadicRadicalJoin_measurePreserving place distinct).integrable_comp_of_integrable integrable
  simp only [Function.comp_def] at lifted
  rw [goodLineFinitePadicTruncatedIntegral,
    ← (finiteAwayThreePadicRadicalJoin_measurePreserving place distinct).setIntegral_preimage_emb
      (finiteAwayThreePadicRadicalJoin place distinct).measurableEmbedding,
    goodLineFiniteSupportRegion_padic_preimage places place distinct outside]
  rw [setIntegral_prod_symm_of_integrable _ _ _ _ _ lifted.integrableOn]
  simp_rw [goodLineFinitePadicIntegrand_split, cuspLocalPadicIntegral_square]
  rfl

theorem goodLineFinitePadicTruncatedIntegral_insert_away (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (exponent : ℂ) (convergent : 2 < exponent.re) (places : Finset FinitePlace)
    (place : FinitePlace) (distinct : place ≠ placeThree) (eigenvalue : ℂ)
    (eigen : cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalue • vector)
    (integrable : Integrable (goodLineFinitePadicIntegrand cusp vector exponent)
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    goodLineFinitePadicTruncatedIntegral cusp vector exponent (insert place places) =
      cuspLocalPadicEulerFactor cusp place eigenvalue exponent *
        goodLineFinitePadicAwayIntegral cusp vector exponent place places := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have lifted := (finiteAwayThreePadicRadicalJoin_measurePreserving place distinct).integrable_comp_of_integrable integrable
  simp only [Function.comp_def] at lifted
  rw [goodLineFinitePadicTruncatedIntegral,
    ← (finiteAwayThreePadicRadicalJoin_measurePreserving place distinct).setIntegral_preimage_emb
      (finiteAwayThreePadicRadicalJoin place distinct).measurableEmbedding,
    goodLineFiniteSupportRegion_padic_preimage_insert places place distinct]
  rw [setIntegral_prod_symm_of_integrable _ _ _ _ _ lifted.integrableOn]
  simp_rw [setIntegral_univ, goodLineFinitePadicIntegrand_split,
    cuspLocalPadicIntegral_eulerQuotient cusp vector nonzero spherical _ place exponent convergent eigenvalue eigen]
  simp_rw [cuspLocalPadicEulerFactor, mul_assoc]
  exact integral_const_mul _ _

theorem goodLineFinitePadicTruncatedIntegral_insert (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (nonzero : vector ≠ 0) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (exponent : ℂ) (convergent : 2 < exponent.re) (places : Finset FinitePlace)
    (place : FinitePlace) (distinct : place ≠ placeThree) (outside : place ∉ places) (eigenvalue : ℂ)
    (eigen : cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalue • vector)
    (integrable : Integrable (goodLineFinitePadicIntegrand cusp vector exponent)
      (finiteAwayThreeMeasure.prod finiteAwayThreeMeasure)) :
    goodLineFinitePadicTruncatedIntegral cusp vector exponent (insert place places) =
      cuspLocalPadicEulerFactor cusp place eigenvalue exponent *
        goodLineFinitePadicTruncatedIntegral cusp vector exponent places := by
  rw [goodLineFinitePadicTruncatedIntegral_insert_away cusp vector nonzero spherical exponent convergent places place distinct eigenvalue eigen integrable,
    goodLineFinitePadicTruncatedIntegral_away cusp vector exponent places place distinct outside integrable]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
