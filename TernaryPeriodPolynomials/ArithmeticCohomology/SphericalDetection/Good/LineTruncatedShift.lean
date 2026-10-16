module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LinePrismTruncation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineRadicalRealHomeomorph (radical : RadicalLattice) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  Homeomorph.addRight (3 * (radical.toAdd.2 : ℝ), 3 * (radical.toAdd.1 : ℝ))

theorem goodLineRadicalRealShift_measurePreserving (radical : RadicalLattice) :
    MeasurePreserving (goodLineRadicalRealShift radical) ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) :=
  measurePreserving_add_right _ (3 * (radical.toAdd.2 : ℝ), 3 * (radical.toAdd.1 : ℝ))

theorem setIntegral_goodLineRadicalRealShift {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : ℝ × ℝ → E) (radical : RadicalLattice) (domain : Set (ℝ × ℝ)) :
    (∫ real in domain, function (goodLineRadicalRealShift radical real) ∂((volume : Measure ℝ).prod volume)) =
    ∫ real in goodLineRadicalRealShift radical '' domain, function real ∂((volume : Measure ℝ).prod volume) := by
  have equality := (goodLineRadicalRealShift_measurePreserving radical).setIntegral_preimage_emb
    (goodLineRadicalRealHomeomorph radical).measurableEmbedding function
    (goodLineRadicalRealShift radical '' domain)
  have injective : Function.Injective (goodLineRadicalRealShift radical) :=
    (goodLineRadicalRealHomeomorph radical).injective
  rw [Set.preimage_image_eq domain injective] at equality
  exact equality

theorem setIntegral_goodLineKernel_shift {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (function : ℝ × ℝ → E) (parameter : ℂ) (radical : RadicalLattice) (domain : Set (ℝ × ℝ)) :
    (∫ real in domain, standardGoodLineRealKernel parameter real •
      function (goodLineRadicalRealShift radical real) ∂((volume : Measure ℝ).prod volume)) =
    ∫ real in goodLineRadicalRealShift radical '' domain,
      standardGoodLineRealKernel parameter (goodLineRadicalRealShift radical⁻¹ real) • function real
      ∂((volume : Measure ℝ).prod volume) := by
  have equality := setIntegral_goodLineRadicalRealShift
    (fun real => standardGoodLineRealKernel parameter (goodLineRadicalRealShift radical⁻¹ real) • function real)
    radical domain
  simpa only [goodLineRadicalRealShift_mul, inv_mul_cancel, goodLineRadicalRealShift_one] using equality

/-- Compact truncation retains both boundary strips as well as the interior kernel difference. -/
theorem setIntegral_goodLineKernel_difference {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (function : ℝ × ℝ → E) (continuous : Continuous function)
    (parameter : ℂ) (radical : RadicalLattice) (domain : Set (ℝ × ℝ)) (compact : IsCompact domain) :
    (∫ real in domain, standardGoodLineRealKernel parameter real •
      (function (goodLineRadicalRealShift radical real) - function real)
      ∂((volume : Measure ℝ).prod volume)) =
    (∫ real in (goodLineRadicalRealShift radical '' domain) \ domain,
        standardGoodLineRealKernel parameter (goodLineRadicalRealShift radical⁻¹ real) • function real
        ∂((volume : Measure ℝ).prod volume)) -
      (∫ real in domain \ (goodLineRadicalRealShift radical '' domain),
        standardGoodLineRealKernel parameter real • function real ∂((volume : Measure ℝ).prod volume)) +
      ∫ real in (goodLineRadicalRealShift radical '' domain) ∩ domain,
        (standardGoodLineRealKernel parameter (goodLineRadicalRealShift radical⁻¹ real) -
          standardGoodLineRealKernel parameter real) • function real ∂((volume : Measure ℝ).prod volume) := by
  let shifted := goodLineRadicalRealShift radical '' domain
  let original (real : ℝ × ℝ) := standardGoodLineRealKernel parameter real • function real
  let translated (real : ℝ × ℝ) :=
    standardGoodLineRealKernel parameter (goodLineRadicalRealShift radical⁻¹ real) • function real
  have shifted_compact : IsCompact shifted := compact.image (goodLineRadicalRealHomeomorph radical).continuous
  have original_integrable : IntegrableOn original domain ((volume : Measure ℝ).prod volume) :=
    ((standardGoodLineRealKernel_continuous parameter).smul continuous).continuousOn.integrableOn_compact compact
  have translated_integrable : IntegrableOn translated shifted ((volume : Measure ℝ).prod volume) :=
    (((standardGoodLineRealKernel_continuous parameter).comp
      (goodLineRadicalRealHomeomorph radical⁻¹).continuous).smul continuous).continuousOn.integrableOn_compact shifted_compact
  have shifted_function_integrable : IntegrableOn
      (fun real => standardGoodLineRealKernel parameter real • function (goodLineRadicalRealShift radical real))
      domain ((volume : Measure ℝ).prod volume) :=
    ((standardGoodLineRealKernel_continuous parameter).smul
      (continuous.comp (goodLineRadicalRealHomeomorph radical).continuous)).continuousOn.integrableOn_compact compact
  simp_rw [smul_sub]
  rw [integral_sub shifted_function_integrable original_integrable, setIntegral_goodLineKernel_shift]
  have outer := integral_inter_add_sdiff (f := translated) compact.measurableSet translated_integrable
  have inner := integral_inter_add_sdiff (f := original) shifted_compact.measurableSet original_integrable
  rw [Set.inter_comm domain shifted] at inner
  have difference := integral_sub
    (translated_integrable.mono_set Set.inter_subset_left)
    (original_integrable.mono_set Set.inter_subset_right)
  have integrands : (fun real => translated real - original real) = fun real =>
      (standardGoodLineRealKernel parameter (goodLineRadicalRealShift radical⁻¹ real) -
        standardGoodLineRealKernel parameter real) • function real := by
    funext real
    exact (sub_smul _ _ _).symm
  rw [integrands] at difference
  change (∫ real in shifted, translated real ∂((volume : Measure ℝ).prod volume)) -
      (∫ real in domain, original real ∂((volume : Measure ℝ).prod volume)) = _
  linear_combination (norm := abel) -outer + inner - difference

theorem setIntegral_goodLineKernel_difference_endpoint {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (function : ℝ × ℝ → E) (continuous : Continuous function)
    (radical : RadicalLattice) (domain : Set (ℝ × ℝ)) (compact : IsCompact domain) :
    (∫ real in domain, function (goodLineRadicalRealShift radical real) - function real
      ∂((volume : Measure ℝ).prod volume)) =
    (∫ real in (goodLineRadicalRealShift radical '' domain) \ domain, function real
      ∂((volume : Measure ℝ).prod volume)) -
      ∫ real in domain \ (goodLineRadicalRealShift radical '' domain), function real
        ∂((volume : Measure ℝ).prod volume) := by
  simpa only [standardGoodLineRealKernel_endpoint, one_smul, sub_self, zero_smul, integral_zero, add_zero] using
    setIntegral_goodLineKernel_difference function continuous cohomologicalPoint radical domain compact

end TernaryPeriodPolynomials.SphericalDetection.Helpers
