module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.SupportRegionSplitting

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspLocalPadicIntegral_square (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryFiniteGL) (place : FinitePlace) (exponent : ℂ) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (∫ pair in {pair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] |
        ‖pair.1‖ ≤ 1 ∧ ‖pair.2‖ ≤ 1}, cuspLocalPadicIntegrand cusp vector base place exponent pair
        ∂((finitePadicMeasure place).prod (finitePadicMeasure place))) =
      normPower (GeneralLinearGroup.det (atFinite base)) exponent * cusp.realize vector (atFinite base) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  simp_rw [cuspLocalPadicIntegrand_eq]
  rw [integral_const_mul,
    (padicPlaneWeightedValue_integral_square (finitePadicMeasure place) (finitePadicMeasure_normalized place)
      (padicNormPowerWeight exponent) (cuspLocalPadicValue cusp vector base place)).2,
    padicNormPowerWeight_one, one_mul, cuspLocalPadicValue_one]

theorem setIntegral_prod_symm_of_integrable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (first : Measure X) (second : Measure Y) [SFinite first] [SFinite second]
    (value : X × Y → ℂ) (source : Set X) (target : Set Y)
    (integrable : IntegrableOn value (source ×ˢ target) (first.prod second)) :
    (∫ pair in source ×ˢ target, value pair ∂(first.prod second)) =
      ∫ y in target, ∫ x in source, value (x, y) ∂first ∂second := by
  change Integrable value ((first.prod second).restrict (source ×ˢ target)) at integrable
  rw [← Measure.prod_restrict] at integrable ⊢
  exact integral_prod_symm value integrable

end TernaryPeriodPolynomials.SphericalDetection.Helpers
