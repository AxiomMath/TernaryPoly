module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.ScalarConvergence
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.EisensteinValue
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.GlobalSeries
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointConstantTerm

theorem eisensteinSum_analyticAt {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) (parameter : ℂ)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    AnalyticAt ℂ (fun value => StandardJointContinuity.eisensteinSum extension value
      argument) parameter := by
  let lower : ℝ := (-(degree : ℝ) / 2 + parameter.re) / 2
  have lowerHalfPlane : -(degree : ℝ) / 2 < lower := by dsimp [lower]; linarith
  have aboveLower : lower < parameter.re := by dsimp [lower]; linarith
  exact TernaryPeriodPolynomials.PlaneEisensteinContinuation.GlobalSeries.analytic_of_summable flat argument (lower : ℂ)
    (CompactScalarConvergence.eisenstein_summable data extension flat (lower : ℂ)
      lowerHalfPlane argument) parameter aboveLower

theorem eisensteinContinuation_eq_sum {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (continues : IsEisensteinContinuation extension continuation)
    (argument : AdelicGL) (parameter : ℂ)
    (regular : AnalyticAt ℂ (fun value => continuation value argument) parameter)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    continuation parameter argument =
      StandardJointContinuity.eisensteinSum extension parameter argument := by
  obtain ⟨threshold, sums⟩ := continues.2
  let domain : Set ℂ := {value | -(degree : ℝ) / 2 < value.re}
  let difference : ℂ → ℂ := fun value => continuation value argument -
    StandardJointContinuity.eisensteinSum extension value argument
  have differenceMeromorphic : MeromorphicOn difference domain := by
    intro value membership
    exact (continues.1 argument value).sub
      (eisensteinSum_analyticAt data extension flat argument value membership).meromorphicAt
  let basePoint : ℂ := (max threshold (-(degree : ℝ) / 2) + 1 : ℝ)
  have aboveThreshold : threshold < basePoint.re := by
    change threshold < max threshold (-(degree : ℝ) / 2) + 1
    linarith [le_max_left threshold (-(degree : ℝ) / 2)]
  have baseMembership : basePoint ∈ domain := by
    change -(degree : ℝ) / 2 < max threshold (-(degree : ℝ) / 2) + 1
    linarith [le_max_right threshold (-(degree : ℝ) / 2)]
  have near : ∀ᶠ value in 𝓝 basePoint, difference value = 0 := by
    filter_upwards [
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds aboveThreshold,
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds baseMembership]
      with value thresholdMembership domainMembership
    exact sub_eq_zero.mpr ((sums value thresholdMembership argument).unique
      (CompactScalarConvergence.eisenstein_summable data extension flat value
        domainMembership argument).hasSum)
  have baseOrder : meromorphicOrderAt difference basePoint = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (near.filter_mono nhdsWithin_le_nhds)
  have parameterOrder : meromorphicOrderAt difference parameter = ⊤ := by
    by_contra nonzeroOrder
    have nonzeroBase := differenceMeromorphic.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt (-(degree : ℝ) / 2)).isPreconnected halfPlane
      baseMembership nonzeroOrder
    exact nonzeroBase baseOrder
  have puncturedEquality :
      (fun value => continuation value argument) =ᶠ[𝓝[≠] parameter]
        (fun value => StandardJointContinuity.eisensteinSum extension value argument) := by
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp parameterOrder] with value equality
    exact sub_eq_zero.mp equality
  exact ((regular.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (eisensteinSum_analyticAt data extension flat argument parameter halfPlane).continuousAt).mp
      puncturedEquality).eq_of_nhds

theorem continued_constantTerm_eq_standard {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (continues : IsEisensteinContinuation extension continuation)
    (parameter : ℂ) (regular : ∀ argument,
      AnalyticAt ℂ (fun value => continuation value argument) parameter)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) :
    (∫ coordinates in additiveDomain ×ˢ additiveDomain,
      continuation parameter (lineUnipotent coordinates.1 coordinates.2 * argument)
        ∂radicalMeasure) =
      ∫ coordinates, standardIntegrand extension parameter argument coordinates
        ∂radicalMeasure := by
  exact CompactScalarConvergence.eisenstein_constantTerm data extension flat parameter
    halfPlane argument (continuation parameter) (fun value => by
      rw [eisensteinContinuation_eq_sum data extension continuation flat continues
        value parameter (regular value) halfPlane]
      exact (CompactScalarConvergence.eisenstein_summable data extension flat
        parameter halfPlane value).hasSum)

theorem eisensteinValue_constantTerm {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (extension : EisensteinValue.flatFamilies data) (degreeBound : 4 ≤ degree)
    (argument : AdelicGL) :
    (∫ coordinates in additiveDomain ×ˢ additiveDomain,
      EisensteinValue.eisensteinValue data holomorphic extension
        (lineUnipotent coordinates.1 coordinates.2 * argument) ∂radicalMeasure) =
      ∫ coordinates, standardIntegrand extension.val cohomologicalPoint argument
        coordinates ∂radicalMeasure := by
  have degreeAsReal : (4 : ℝ) ≤ (degree : ℝ) := by exact_mod_cast degreeBound
  have halfPlane : -(degree : ℝ) / 2 < cohomologicalPoint.re := by
    norm_num [cohomologicalPoint]
    linarith
  exact continued_constantTerm_eq_standard data extension.val
    (EisensteinValue.chosenContinuation data holomorphic extension) extension.property
    (EisensteinValue.chosenContinuation_spec data holomorphic extension).1
    cohomologicalPoint (EisensteinValue.chosenContinuation_spec data holomorphic extension).2
    halfPlane argument

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointConstantTerm
