module

public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.RationalComparison
public import Mathlib.Analysis.Meromorphic.Order

@[expose] public section


/- Ported from AxiomDeep (Claude Opus 5.5). -/
open GeneralEisenstein GeneralEisenstein.Adelic
open Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.GraphPieces.ContinuationUniqueness

theorem meromorphic_halfPlane_unique (first second : ℂ → ℂ)
    (firstMeromorphic : ∀ parameter, MeromorphicAt first parameter)
    (secondMeromorphic : ∀ parameter, MeromorphicAt second parameter)
    (threshold : ℝ) (halfPlaneEquality : ∀ parameter : ℂ,
      threshold < parameter.re → first parameter = second parameter)
    (point : ℂ) (firstRegular : AnalyticAt ℂ first point)
    (secondRegular : AnalyticAt ℂ second point) : first point = second point := by
  have differenceMeromorphic : MeromorphicOn (fun parameter =>
      first parameter - second parameter) Set.univ := by
    intro parameter membership
    exact (firstMeromorphic parameter).sub (secondMeromorphic parameter)
  let basePoint : ℂ := (threshold + 1 : ℝ)
  have basePointMembership : threshold < basePoint.re := by
    change threshold < threshold + 1
    linarith
  have halfPlaneOpen : IsOpen {parameter : ℂ | threshold < parameter.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have differenceZero : ∀ᶠ parameter in 𝓝 basePoint,
      first parameter - second parameter = 0 := by
    filter_upwards [halfPlaneOpen.mem_nhds basePointMembership] with parameter membership
    exact sub_eq_zero.mpr (halfPlaneEquality parameter membership)
  have basePointOrder : meromorphicOrderAt (fun parameter =>
      first parameter - second parameter) basePoint = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (differenceZero.filter_mono nhdsWithin_le_nhds)
  have pointOrder : meromorphicOrderAt (fun parameter =>
      first parameter - second parameter) point = ⊤ := by
    by_contra nonzeroOrder
    have basePointNonzero := differenceMeromorphic.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (Set.mem_univ point) (Set.mem_univ basePoint) nonzeroOrder
    exact basePointNonzero basePointOrder
  have puncturedEquality : first =ᶠ[𝓝[≠] point] second := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp pointOrder] with parameter equality
    exact sub_eq_zero.mp equality
  exact ((firstRegular.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    secondRegular.continuousAt).mp puncturedEquality).eq_of_nhds

theorem eisensteinContinuation_unique (extension first second : ℂ → AdelicGL → ℂ)
    (firstContinuation : IsEisensteinContinuation extension first)
    (secondContinuation : IsEisensteinContinuation extension second)
    (point : ℂ)
    (firstRegular : ∀ argument, AnalyticAt ℂ (fun parameter => first parameter argument) point)
    (secondRegular : ∀ argument, AnalyticAt ℂ (fun parameter => second parameter argument) point) :
    first point = second point := by
  obtain ⟨firstThreshold, firstSum⟩ := firstContinuation.2
  obtain ⟨secondThreshold, secondSum⟩ := secondContinuation.2
  funext argument
  apply meromorphic_halfPlane_unique _ _ (firstContinuation.1 argument)
    (secondContinuation.1 argument) (max firstThreshold secondThreshold) _ point
    (firstRegular argument) (secondRegular argument)
  intro parameter membership
  exact (firstSum parameter (lt_of_le_of_lt (le_max_left _ _) membership) argument).unique
    (secondSum parameter (lt_of_le_of_lt (le_max_right _ _) membership) argument)

theorem standardContinuation_unique (extension first second : ℂ → AdelicGL → ℂ)
    (firstContinuation : IsStandardContinuation extension first)
    (secondContinuation : IsStandardContinuation extension second)
    (point : ℂ)
    (firstRegular : ∀ argument, AnalyticAt ℂ (fun parameter => first parameter argument) point)
    (secondRegular : ∀ argument, AnalyticAt ℂ (fun parameter => second parameter argument) point) :
    first point = second point := by
  obtain ⟨firstThreshold, firstIntegral⟩ := firstContinuation.2
  obtain ⟨secondThreshold, secondIntegral⟩ := secondContinuation.2
  funext argument
  apply meromorphic_halfPlane_unique _ _ (firstContinuation.1 argument)
    (secondContinuation.1 argument) (max firstThreshold secondThreshold) _ point
    (firstRegular argument) (secondRegular argument)
  intro parameter membership
  exact (firstIntegral parameter (lt_of_le_of_lt (le_max_left _ _) membership)
    argument).2.trans (secondIntegral parameter
      (lt_of_le_of_lt (le_max_right _ _) membership) argument).2.symm

end TernaryPeriodPolynomials.GraphPieces.ContinuationUniqueness
