module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.Analysis.Meromorphic.Order

@[expose] public section


open GeneralEisenstein
open GeneralEisenstein.Adelic MeasureTheory Filter Topology

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem meromorphic_eq_at_of_halfPlane {first second : ℂ → ℂ}
    (first_meromorphic : ∀ parameter, MeromorphicAt first parameter)
    (second_meromorphic : ∀ parameter, MeromorphicAt second parameter)
    (bound : ℝ) (agreement : ∀ parameter : ℂ,
      bound < parameter.re → first parameter = second parameter)
    (endpoint : ℂ) (first_analytic : AnalyticAt ℂ first endpoint)
    (second_analytic : AnalyticAt ℂ second endpoint) :
    first endpoint = second endpoint := by
  have difference_meromorphic : MeromorphicOn (first - second) Set.univ := by
    intro parameter _
    exact (first_meromorphic parameter).sub (second_meromorphic parameter)
  have halfPlane_open : IsOpen {parameter : ℂ | bound < parameter.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have inside : bound < ((bound + 1 : ℝ) : ℂ).re := by
    simp only [Complex.ofReal_re]
    linarith
  have local_zero : ∀ᶠ parameter in 𝓝 ((bound + 1 : ℝ) : ℂ),
      (first - second) parameter = 0 := by
    filter_upwards [halfPlane_open.mem_nhds inside] with parameter beyond
    exact sub_eq_zero.mpr (agreement parameter beyond)
  have initial_order : meromorphicOrderAt (first - second)
      ((bound + 1 : ℝ) : ℂ) = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (local_zero.filter_mono nhdsWithin_le_nhds)
  have endpoint_order : meromorphicOrderAt (first - second) endpoint = ⊤ := by
    by_contra finite_order
    have initial_finite := difference_meromorphic.meromorphicOrderAt_ne_top_of_isPreconnected
      (y := ((bound + 1 : ℝ) : ℂ)) isPreconnected_univ
      (Set.mem_univ endpoint) (Set.mem_univ _) finite_order
    exact initial_finite initial_order
  have punctured_agreement : first =ᶠ[𝓝[≠] endpoint] second := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp endpoint_order] with parameter zero
    exact sub_eq_zero.mp zero
  exact ((first_analytic.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    second_analytic.continuousAt).mp punctured_agreement).eq_of_nhds

theorem standardContinuation_eq_at {flat first second : ℂ → AdelicGL → ℂ}
    (first_continuation : IsStandardContinuation flat first)
    (second_continuation : IsStandardContinuation flat second)
    (argument : AdelicGL)
    (first_analytic : AnalyticAt ℂ (fun parameter => first parameter argument)
      cohomologicalPoint)
    (second_analytic : AnalyticAt ℂ (fun parameter => second parameter argument)
      cohomologicalPoint) :
    first cohomologicalPoint argument = second cohomologicalPoint argument := by
  rcases first_continuation with ⟨first_meromorphic, first_bound, first_integral⟩
  rcases second_continuation with ⟨second_meromorphic, second_bound, second_integral⟩
  apply meromorphic_eq_at_of_halfPlane
    (first_meromorphic argument) (second_meromorphic argument)
    (max first_bound second_bound) _ cohomologicalPoint first_analytic second_analytic
  intro parameter beyond
  rw [(first_integral parameter (lt_of_le_of_lt (le_max_left _ _) beyond) argument).2,
    (second_integral parameter (lt_of_le_of_lt (le_max_right _ _) beyond) argument).2]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
