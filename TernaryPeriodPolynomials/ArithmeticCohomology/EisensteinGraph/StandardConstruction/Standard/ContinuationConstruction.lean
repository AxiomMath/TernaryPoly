module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.RecoveryConstruction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.ContinuationRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.CompactRegularity

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardContinuationConstruction

open StandardContinuationRegularity

theorem average_continues {degree : ℕ} (data : InducingData degree)
    (extension eisenstein : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (continues : IsEisensteinContinuation extension eisenstein)
    (regular : LineAverageContinuation.Regular eisenstein) :
    IsStandardContinuation extension (fun parameter => LineConstantTerm.average (eisenstein parameter)) := by
  refine ⟨regular.2, ?_⟩
  obtain ⟨threshold, sums⟩ := continues.2
  refine ⟨max threshold (-(degree : ℝ) / 2), ?_⟩
  intro parameter membership argument
  have halfPlane : -(degree : ℝ) / 2 < parameter.re :=
    lt_of_le_of_lt (le_max_right _ _) membership
  refine ⟨CompactScalarConvergence.standard_integrable data extension flat parameter halfPlane argument, ?_⟩
  change LineConstantTerm.average (eisenstein parameter) argument = _
  rw [LineConstantTerm.average_eq]
  exact CompactScalarConvergence.eisenstein_constantTerm data extension flat parameter halfPlane argument
    (eisenstein parameter) (sums parameter (lt_of_le_of_lt (le_max_left _ _) membership))

theorem exists_continuation {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) :
    ∃ continuation : ℂ → AdelicGL → ℂ, IsStandardContinuation extension continuation := by
  obtain ⟨eisenstein, continues, regular, _⟩ := LineRecoveryConstruction.exists_continuation flat
  exact ⟨_, average_continues data extension eisenstein flat continues regular⟩

theorem hasRegularStandard_of_holomorphic {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    StandardValue.HasRegularStandard extension := by
  obtain ⟨eisenstein, continues, regular, compactRegular⟩ := LineRecoveryConstruction.exists_continuation flat
  let continuation := fun parameter => LineConstantTerm.average (eisenstein parameter)
  have standard := average_continues data extension eisenstein flat continues regular
  let repaired := fun parameter argument =>
    toMeromorphicNFAt (fun value => continuation value argument) cohomologicalPoint parameter
  have off (parameter : ℂ) (different : parameter ≠ cohomologicalPoint) (argument : AdelicGL) :
      continuation parameter argument = repaired parameter argument :=
    (standard.1 argument cohomologicalPoint).eqOn_compl_singleton_toMeromorphicNFAt different
  have analytic (argument : AdelicGL) :
      AnalyticAt ℂ (fun parameter => repaired parameter argument) cohomologicalPoint :=
    (standard.1 argument cohomologicalPoint).meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp
      (LineCompactRegularity.average_nonnegative_order flat holomorphic continues compactRegular argument)
  refine ⟨repaired, ⟨?_, ?_⟩, analytic⟩
  · intro argument parameter
    by_cases equality : parameter = cohomologicalPoint
    · subst parameter
      exact (analytic argument).meromorphicAt
    · apply (standard.1 argument parameter).congr
      filter_upwards [eventually_ne_nhdsWithin equality] with value different
      exact off value different argument
  · obtain ⟨threshold, integrals⟩ := standard.2
    refine ⟨max threshold cohomologicalPoint.re, ?_⟩
    intro parameter membership argument
    have different : parameter ≠ cohomologicalPoint := by
      intro equality
      subst parameter
      exact (not_lt_of_ge (le_max_right threshold cohomologicalPoint.re)) membership
    rw [← off parameter different argument]
    exact integrals parameter (lt_of_le_of_lt (le_max_left _ _) membership) argument

theorem hasRegularStandard {degree : ℕ} (data : InducingData degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension) (large : 4 ≤ degree) :
    StandardValue.HasRegularStandard extension := by
  obtain ⟨continuation, continues⟩ := exists_continuation data extension flat
  refine ⟨repair extension continuation cohomologicalPoint,
    repair_continues extension continuation continues cohomologicalPoint, ?_⟩
  have degreeAsReal : (4 : ℝ) ≤ (degree : ℝ) := by exact_mod_cast large
  have halfPlane : -(degree : ℝ) / 2 < cohomologicalPoint.re := by
    norm_num [cohomologicalPoint]
    linarith
  exact repair_analytic data extension continuation flat continues cohomologicalPoint halfPlane

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardContinuationConstruction
