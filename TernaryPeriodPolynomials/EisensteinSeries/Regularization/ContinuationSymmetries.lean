module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.CentralCharacter

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem continuation_germ_of_summand_symmetry
    {sectionFamily continuation : ℂ → AdelicGL → ℂ}
    (continuation_spec : IsEisensteinContinuation sectionFamily continuation)
    (sourceElement targetElement : AdelicGL) (multiplier : ℂ)
    (summand_symmetry : ∀ parameter flag,
      eisensteinSummand sectionFamily parameter targetElement flag =
        multiplier * eisensteinSummand sectionFamily parameter sourceElement flag)
    (parameter : ℂ) :
    (fun nearbyParameter => continuation nearbyParameter targetElement) =ᶠ[
      nhdsWithin parameter {parameter}ᶜ]
      (fun nearbyParameter => multiplier * continuation nearbyParameter sourceElement) := by
  obtain ⟨threshold, convergence⟩ := continuation_spec.2
  let base : ℂ := (threshold + 1 : ℝ)
  have base_large : threshold < base.re := by
    dsimp [base]
    exact lt_add_one threshold
  have same_near_base :
      (fun nearbyParameter => continuation nearbyParameter targetElement) =ᶠ[nhds base]
        (fun nearbyParameter => multiplier * continuation nearbyParameter sourceElement) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).eventually_mem
      base_large] with nearbyParameter nearby_large
    have scaled_sum := (convergence nearbyParameter nearby_large sourceElement).mul_left
      multiplier
    have actual_sum := convergence nearbyParameter nearby_large targetElement
    have summands_equal :
        (fun flag => multiplier * eisensteinSummand sectionFamily nearbyParameter
          sourceElement flag) = eisensteinSummand sectionFamily nearbyParameter
            targetElement := by
      funext flag
      exact (summand_symmetry nearbyParameter flag).symm
    rw [summands_equal] at scaled_sum
    exact actual_sum.unique scaled_sum
  have difference_meromorphic : MeromorphicOn
      (fun nearbyParameter => continuation nearbyParameter targetElement -
        multiplier * continuation nearbyParameter sourceElement) Set.univ := by
    intro nearbyParameter _
    exact (continuation_spec.1 targetElement nearbyParameter).sub
      ((MeromorphicAt.const multiplier nearbyParameter).mul
        (continuation_spec.1 sourceElement nearbyParameter))
  have zero_order_base : meromorphicOrderAt
      (fun nearbyParameter => continuation nearbyParameter targetElement -
        multiplier * continuation nearbyParameter sourceElement) base = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [same_near_base.filter_mono nhdsWithin_le_nhds] with
      nearbyParameter same_value
    exact sub_eq_zero.mpr same_value
  have zero_order_parameter : meromorphicOrderAt
      (fun nearbyParameter => continuation nearbyParameter targetElement -
        multiplier * continuation nearbyParameter sourceElement) parameter = ⊤ := by
    by_contra order_ne_top
    exact (difference_meromorphic.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ parameter) (Set.mem_univ base) order_ne_top)
        zero_order_base
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp zero_order_parameter] with
    nearbyParameter difference_zero
  exact sub_eq_zero.mp difference_zero

theorem continuation_central_character_germ
    {degree : ℕ} {inducingData : InducingData degree}
    {sectionFamily continuation : ℂ → AdelicGL → ℂ}
    (flat_family : IsFlatSection inducingData sectionFamily)
    (continuation_spec : IsEisensteinContinuation sectionFamily continuation)
    (idele : Adelesˣ) (groupElement : AdelicGL) (parameter : ℂ) :
    (fun nearbyParameter => continuation nearbyParameter
      (GeneralLinearGroup.scalar (Fin 3) idele * groupElement)) =ᶠ[
        nhdsWithin parameter {parameter}ᶜ]
      (fun nearbyParameter =>
        inducingData.chi.toMonoidHom idele * inducingData.cusp.centralCharacter idele *
          normPower idele ((degree : ℂ) + 3) * continuation nearbyParameter groupElement) := by
  apply continuation_germ_of_summand_symmetry continuation_spec
  intro nearbyParameter flag
  simp only [eisensteinSummand]
  rw [← mul_assoc, ← GeneralLinearGroup.scalar_commute idele, mul_assoc]
  exact induced_central_character (flat_family.1 nearbyParameter) idele
    (rationalGroup flag.out⁻¹ * groupElement)

theorem continuation_finite_level_germ
    {degree : ℕ} {inducingData : InducingData degree}
    {sectionFamily continuation : ℂ → AdelicGL → ℂ}
    (flat_family : IsFlatSection inducingData sectionFamily)
    (continuation_spec : IsEisensteinContinuation sectionFamily continuation)
    (levelElement : finiteLevel) (groupElement : AdelicGL) (parameter : ℂ) :
    (fun nearbyParameter => continuation nearbyParameter
      (groupElement * atFinite levelElement.val)) =ᶠ[
        nhdsWithin parameter {parameter}ᶜ]
      (fun nearbyParameter => continuation nearbyParameter groupElement) := by
  simpa only [one_mul] using
    continuation_germ_of_summand_symmetry continuation_spec groupElement
      (groupElement * atFinite levelElement.val) 1 (by
        intro nearbyParameter flag
        simp only [eisensteinSummand, ← mul_assoc, one_mul]
        exact (flat_family.1 nearbyParameter).2.1 levelElement
          (rationalGroup flag.out⁻¹ * groupElement)) parameter

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
