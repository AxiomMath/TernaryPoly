module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.ScalarConvergence
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.Value
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardContinuationRegularity

theorem germ_eq_integral {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation)
    (argument : AdelicGL) (parameter : ℂ) (halfPlane : -(degree : ℝ) / 2 < parameter.re) :
    (fun value => continuation value argument) =ᶠ[𝓝[≠] parameter]
      (fun value => ∫ coordinates, standardIntegrand extension value argument coordinates ∂radicalMeasure) := by
  obtain ⟨threshold, integrals⟩ := continues.2
  let domain : Set ℂ := {value | -(degree : ℝ) / 2 < value.re}
  let difference : ℂ → ℂ := fun value => continuation value argument -
    ∫ coordinates, standardIntegrand extension value argument coordinates ∂radicalMeasure
  have differenceMeromorphic : MeromorphicOn difference domain := by
    intro value membership
    exact (continues.1 argument value).sub
      (CompactScalarConvergence.standard_analyticAt data extension flat value membership argument).meromorphicAt
  let basePoint : ℂ := (max threshold (-(degree : ℝ) / 2) + 1 : ℝ)
  have aboveThreshold : threshold < basePoint.re := by
    change threshold < max threshold (-(degree : ℝ) / 2) + 1
    linarith [le_max_left threshold (-(degree : ℝ) / 2)]
  have baseMembership : basePoint ∈ domain := by
    change -(degree : ℝ) / 2 < max threshold (-(degree : ℝ) / 2) + 1
    linarith [le_max_right threshold (-(degree : ℝ) / 2)]
  have near : ∀ᶠ value in 𝓝 basePoint, difference value = 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds aboveThreshold]
      with value membership
    exact sub_eq_zero.mpr (integrals value membership argument).2
  have baseOrder : meromorphicOrderAt difference basePoint = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (near.filter_mono nhdsWithin_le_nhds)
  have parameterOrder : meromorphicOrderAt difference parameter = ⊤ := by
    by_contra nonzeroOrder
    have nonzeroBase := differenceMeromorphic.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_halfSpace_re_gt (-(degree : ℝ) / 2)).isPreconnected halfPlane
      baseMembership nonzeroOrder
    exact nonzeroBase baseOrder
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp parameterOrder] with value equality
  exact sub_eq_zero.mp equality

def repair (extension continuation : ℂ → AdelicGL → ℂ) (point : ℂ) : ℂ → AdelicGL → ℂ :=
  fun parameter argument => if parameter = point then
    ∫ coordinates, standardIntegrand extension point argument coordinates ∂radicalMeasure
    else continuation parameter argument

theorem repair_continues (extension continuation : ℂ → AdelicGL → ℂ)
    (continues : IsStandardContinuation extension continuation) (point : ℂ) :
    IsStandardContinuation extension (repair extension continuation point) := by
  constructor
  · intro argument parameter
    apply (continues.1 argument parameter).congr
    by_cases equality : parameter = point
    · subst parameter
      filter_upwards [self_mem_nhdsWithin] with value different
      change value ≠ point at different
      simp only [repair, ite_eq_right different]
    · filter_upwards [eventually_ne_nhdsWithin equality] with value different
      simp only [repair, ite_eq_right different]
  · obtain ⟨threshold, integrals⟩ := continues.2
    refine ⟨max threshold point.re, ?_⟩
    intro parameter membership argument
    have different : parameter ≠ point := by
      intro equality
      subst parameter
      exact (not_lt_of_ge (le_max_right threshold point.re)) membership
    simpa only [repair, ite_eq_right different] using
      integrals parameter (lt_of_le_of_lt (le_max_left _ _) membership) argument

theorem repair_analytic {degree : ℕ} (data : InducingData degree)
    (extension continuation : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (continues : IsStandardContinuation extension continuation)
    (point : ℂ) (halfPlane : -(degree : ℝ) / 2 < point.re) (argument : AdelicGL) :
    AnalyticAt ℂ (fun value => repair extension continuation point value argument) point := by
  apply (CompactScalarConvergence.standard_analyticAt data extension flat point halfPlane argument).congr
  have near := eventually_nhdsWithin_iff.mp
    (germ_eq_integral data extension continuation flat continues argument point halfPlane)
  filter_upwards [near] with value equality
  by_cases same : value = point
  · subst value
    simp [repair]
  · simpa only [repair, ite_eq_right same] using (equality same).symm

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardContinuationRegularity
