module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Helpers

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem meromorphic_germs_agree_of_halfplane {first second : ℂ → ℂ}
    (first_meromorphic : ∀ parameter, MeromorphicAt first parameter)
    (second_meromorphic : ∀ parameter, MeromorphicAt second parameter)
    (halfplane_eq : ∃ threshold : ℝ, ∀ parameter : ℂ, threshold < parameter.re →
      first parameter = second parameter) (parameter : ℂ) :
    first =ᶠ[nhdsWithin parameter {parameter}ᶜ] second := by
  obtain ⟨threshold, equality⟩ := halfplane_eq
  let base : ℂ := (threshold + 1 : ℝ)
  have base_large : threshold < base.re := by
    dsimp [base]
    exact lt_add_one threshold
  have same_near_base : first =ᶠ[nhds base] second := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).eventually_mem
      base_large] with nearby nearby_large
    exact equality nearby nearby_large
  have difference_meromorphic : MeromorphicOn (fun nearby => first nearby - second nearby) Set.univ := by
    intro nearby _
    exact (first_meromorphic nearby).sub (second_meromorphic nearby)
  have zero_order_base : meromorphicOrderAt (fun nearby => first nearby - second nearby) base = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [same_near_base.filter_mono nhdsWithin_le_nhds] with nearby same_value
    exact sub_eq_zero.mpr same_value
  have zero_order_parameter : meromorphicOrderAt (fun nearby => first nearby - second nearby) parameter = ⊤ := by
    by_contra order_ne_top
    exact (difference_meromorphic.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ parameter) (Set.mem_univ base) order_ne_top) zero_order_base
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp zero_order_parameter] with nearby difference_zero
  exact sub_eq_zero.mp difference_zero

theorem standard_continuation_germs_agree
    {family firstContinuation secondContinuation : ℂ → AdelicGL → ℂ}
    (first_spec : IsStandardContinuation family firstContinuation)
    (second_spec : IsStandardContinuation family secondContinuation)
    (groupElement : AdelicGL) (parameter : ℂ) :
    (fun nearby => firstContinuation nearby groupElement) =ᶠ[nhdsWithin parameter {parameter}ᶜ]
      (fun nearby => secondContinuation nearby groupElement) := by
  apply meromorphic_germs_agree_of_halfplane (first_spec.1 groupElement) (second_spec.1 groupElement)
  obtain ⟨firstThreshold, first_eq⟩ := first_spec.2
  obtain ⟨secondThreshold, second_eq⟩ := second_spec.2
  refine ⟨max firstThreshold secondThreshold, ?_⟩
  intro nearby nearby_large
  exact (first_eq nearby (lt_of_le_of_lt (le_max_left _ _) nearby_large) groupElement).2.trans
    (second_eq nearby (lt_of_le_of_lt (le_max_right _ _) nearby_large) groupElement).2.symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
