module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.RationalAutomorphy
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ContinuationSymmetries

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem unitaryNormalize_continuation_rational_germ
    {degree : ℕ} {inducingData : InducingData degree}
    {family continuation : ℂ → AdelicGL → ℂ}
    (flat_family : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (rationalMatrix : RationalGL3) (groupElement : AdelicGL) (parameter : ℂ) :
    (fun nearbyParameter => unitaryNormalize degree continuation nearbyParameter
      (rationalGroup rationalMatrix * groupElement)) =ᶠ[nhdsWithin parameter {parameter}ᶜ]
      (fun nearbyParameter => unitaryNormalize degree continuation nearbyParameter groupElement) := by
  have translated_spec := unitaryNormalize_continuation degree
    (continuation_rational_translate flat_family.1 continuation_spec rationalMatrix)
  have same_germ := continuation_germs_agree translated_spec
    (unitaryNormalize_continuation degree continuation_spec) groupElement parameter
  simpa only [unitaryNormalize, map_mul, normPower_mul, rationalGroup,
    GeneralLinearGroup.map_det, normPower_rational, one_mul] using same_germ

theorem unitaryNormalize_continuation_central_germ
    {degree : ℕ} {inducingData : InducingData degree}
    {family continuation : ℂ → AdelicGL → ℂ}
    (flat_family : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (idele : Adelesˣ) (groupElement : AdelicGL) (parameter : ℂ) :
    (fun nearbyParameter => unitaryNormalize degree continuation nearbyParameter
      (GeneralLinearGroup.scalar (Fin 3) idele * groupElement))
      =ᶠ[nhdsWithin parameter {parameter}ᶜ]
      (fun nearbyParameter => inducingData.chi.toMonoidHom idele *
        inducingData.cusp.centralCharacter idele *
          unitaryNormalize degree continuation nearbyParameter groupElement) := by
  apply continuation_germ_of_summand_symmetry
    (unitaryNormalize_continuation degree continuation_spec)
  intro nearbyParameter flag
  simp only [eisensteinSummand]
  rw [← mul_assoc, ← GeneralLinearGroup.scalar_commute idele, mul_assoc]
  exact unitaryNormalize_central flat_family.1 nearbyParameter idele
    (rationalGroup flag.out⁻¹ * groupElement)

theorem unitaryNormalize_continuation_finite_level_germ
    {degree : ℕ} {inducingData : InducingData degree}
    {family continuation : ℂ → AdelicGL → ℂ}
    (flat_family : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (levelElement : finiteLevel) (groupElement : AdelicGL) (parameter : ℂ) :
    (fun nearbyParameter => unitaryNormalize degree continuation nearbyParameter
      (groupElement * atFinite levelElement.val)) =ᶠ[nhdsWithin parameter {parameter}ᶜ]
      (fun nearbyParameter => unitaryNormalize degree continuation nearbyParameter groupElement) := by
  simpa only [one_mul] using continuation_germ_of_summand_symmetry
    (unitaryNormalize_continuation degree continuation_spec) groupElement
      (groupElement * atFinite levelElement.val) 1 (by
        intro nearbyParameter flag
        simp only [eisensteinSummand, ← mul_assoc, one_mul]
        exact unitaryNormalize_finite_level flat_family.1 nearbyParameter levelElement
          (rationalGroup flag.out⁻¹ * groupElement)) parameter

theorem continuation_rational_order
    {degree : ℕ} {inducingData : InducingData degree}
    {family continuation : ℂ → AdelicGL → ℂ}
    (flat_family : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (rationalMatrix : RationalGL3) (groupElement : AdelicGL) (parameter : ℂ) :
    meromorphicOrderAt
      (fun nearbyParameter => continuation nearbyParameter (rationalGroup rationalMatrix * groupElement))
        parameter = meromorphicOrderAt (fun nearbyParameter => continuation nearbyParameter groupElement)
          parameter :=
  meromorphicOrderAt_congr
    (continuation_rational_germ flat_family continuation_spec rationalMatrix groupElement parameter)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
