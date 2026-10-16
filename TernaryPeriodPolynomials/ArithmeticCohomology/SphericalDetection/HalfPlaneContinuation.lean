module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Continuation
public import Mathlib.Analysis.Complex.Convex

@[expose] public section


open Filter Topology

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem meromorphic_eq_at_in_halfPlane {first second : ℂ → ℂ} (domain_bound : ℝ)
    (first_meromorphic : MeromorphicOn first {parameter : ℂ | domain_bound < parameter.re})
    (second_meromorphic : MeromorphicOn second {parameter : ℂ | domain_bound < parameter.re})
    (agreement_bound : ℝ) (agreement : ∀ parameter : ℂ,
      agreement_bound < parameter.re → domain_bound < parameter.re → first parameter = second parameter)
    (endpoint : ℂ) (inside : domain_bound < endpoint.re)
    (first_analytic : AnalyticAt ℂ first endpoint) (second_analytic : AnalyticAt ℂ second endpoint) :
    first endpoint = second endpoint := by
  let anchor : ℂ := ((max domain_bound agreement_bound + 1 : ℝ) : ℂ)
  have anchor_domain : domain_bound < anchor.re := by
    change domain_bound < max domain_bound agreement_bound + 1
    linarith [le_max_left domain_bound agreement_bound]
  have anchor_agreement : agreement_bound < anchor.re := by
    change agreement_bound < max domain_bound agreement_bound + 1
    linarith [le_max_right domain_bound agreement_bound]
  have difference_meromorphic : MeromorphicOn (first - second) {parameter : ℂ | domain_bound < parameter.re} := by
    intro parameter member
    exact (first_meromorphic parameter member).sub (second_meromorphic parameter member)
  have local_zero : ∀ᶠ parameter in 𝓝 anchor, (first - second) parameter = 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds anchor_domain,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds anchor_agreement] with parameter in_domain beyond
    exact sub_eq_zero.mpr (agreement parameter beyond in_domain)
  have initial_order : meromorphicOrderAt (first - second) anchor = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (local_zero.filter_mono nhdsWithin_le_nhds)
  have endpoint_order : meromorphicOrderAt (first - second) endpoint = ⊤ := by
    by_contra finite_order
    exact difference_meromorphic.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt domain_bound).isPreconnected inside anchor_domain finite_order initial_order
  have punctured_agreement : first =ᶠ[𝓝[≠] endpoint] second := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp endpoint_order] with parameter zero
    exact sub_eq_zero.mp zero
  exact ((first_analytic.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    second_analytic.continuousAt).mp punctured_agreement).eq_of_nhds

end TernaryPeriodPolynomials.SphericalDetection.Helpers
