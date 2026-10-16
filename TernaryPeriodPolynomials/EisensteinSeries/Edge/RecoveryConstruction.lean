module

public import TernaryPeriodPolynomials.EisensteinSeries.Edge.GodementCompact
public import TernaryPeriodPolynomials.EisensteinSeries.Edge.PlaneAverageContinuation
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.RecoveryConstruction

@[expose] public section


/-!
# A regular continuation of every flat plane Eisenstein series

The recovery construction of the plane Eisenstein continuation (AxiomDeep
`PlaneEisensteinContinuation.PlaneContinuation`, carried with line regularity by Sol's
`LineRecoveryConstruction`) writes the continuation of a flat family as a finite combination,
with meromorphic coefficients, of finite-level averages of right translates of Godement theta
continuations. Each step preserves `PlaneAverageContinuation.Regular` and
`CompactContinuation.Regular`, so every flat family has a continuation with both properties
(`exists_continuation`).

Original work by Claude Opus 5.5 (AxiomCode), following the step structure of
the Sol reference implementation `StandardConstruction.LineRecoveryConstruction`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FlatProfilePackages
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein.RecoveryConstruction

theorem linearProfile {degree : ℕ} {data : InducingData degree}
    {function : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data function)
    (cutoff : Rectangular ℝ → ℝ) (smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) cutoff)
    (compact : HasCompactSupport cutoff)
    (supported : tsupport cutoff ⊆ {value : Rectangular ℝ | FullRank value}) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation
        (fun parameter point => VectorGodement.sectionFunction data
          (LinearProfileRecovery.test (flat.1 parameter) cutoff) parameter point) continuation ∧
      PlaneAverageContinuation.Regular continuation ∧ CompactContinuation.Regular continuation := by
  choose families image using fun key : UniversalFiniteProfiles.Key data =>
    exists_realFamily flat (UniversalFiniteProfiles.representative data key) cutoff smooth compact supported
  have equality : FlatProfileInterpolation.test data families (UniversalFiniteProfiles.boxes data) =
      fun parameter => LinearProfileRecovery.test (flat.1 parameter) cutoff := by
    funext parameter value
    rw [FlatProfileInterpolation.test_eq]
    simp only [image]
    rfl
  refine ⟨FlatProfileInterpolation.continuation data families (UniversalFiniteProfiles.boxes data), ?_,
    PlaneAverageContinuation.flatProfile_regular data families (UniversalFiniteProfiles.boxes data),
    GodementCompact.flatProfile_regular data families (UniversalFiniteProfiles.boxes data)⟩
  simpa only [equality] using FlatProfileInterpolation.continues data families (UniversalFiniteProfiles.boxes data)

theorem finiteRecovery {degree : ℕ} {data : InducingData degree}
    {function : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data function) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation
        (fun parameter point => FiniteRecoveryIntegral.sectionFunction (flat.1 parameter) point) continuation ∧
      PlaneAverageContinuation.Regular continuation ∧ CompactContinuation.Regular continuation := by
  obtain ⟨cutoff, smooth, compact, supported, nonzero, mass⟩ := ConstantRealMass.exists_cutoff
  obtain ⟨continuation, continues, regular, compactRegular⟩ := linearProfile flat cutoff smooth compact supported
  let coefficient : ℂ := (ConstantRealMass.baseMass cutoff)⁻¹
  have equality : (fun parameter point => coefficient * VectorGodement.sectionFunction data
      (LinearProfileRecovery.test (flat.1 parameter) cutoff) parameter point) =
      fun parameter point => FiniteRecoveryIntegral.sectionFunction (flat.1 parameter) point := by
    funext parameter point
    have value := (FiniteRecoveryIntegral.section_eq (flat.1 parameter) cutoff point).trans
      (congrArg (fun scalar : ℂ => scalar * FiniteRecoveryIntegral.sectionFunction (flat.1 parameter) point) (mass point))
    exact (congrArg (fun scalar : ℂ => coefficient * scalar) value).trans (inv_mul_cancel_left₀ nonzero _)
  refine ⟨fun parameter point => coefficient * continuation parameter point, ?_,
    PlaneAverageContinuation.regular_mul regular (fun _ => coefficient) (fun _ => analyticAt_const.meromorphicAt),
    CompactContinuation.regular_mul compactRegular (fun _ => coefficient) (fun _ => analyticAt_const.meromorphicAt)⟩
  exact equality ▸ ContinuationAlgebra.multiply continues (fun _ => coefficient)
    (fun _ => analyticAt_const.meromorphicAt)

theorem finiteProjection {degree : ℕ} {data : InducingData degree}
    {function : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data function) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation
        (fun parameter => FiniteSectionProjection.sectionFunction (flat.1 parameter)) continuation ∧
      PlaneAverageContinuation.Regular continuation ∧ CompactContinuation.Regular continuation := by
  obtain ⟨continuation, continues, regular, compactRegular⟩ := finiteRecovery flat
  exact ⟨fun parameter => FiniteSectionProjection.average data (continuation parameter),
    FiniteSectionProjection.average_continuation data continues,
    PlaneAverageContinuation.regular_average data regular, CompactContinuation.regular_average data compactRegular⟩

theorem combination {degree : ℕ} {data : InducingData degree} {Indices : Type} [Fintype Indices]
    {families : Indices → ℂ → AdelicGL → ℂ} (flat : ∀ index, IsFlatSection data (families index))
    (coefficients : ℂ → Indices → ℂ)
    (meromorphic : ∀ index parameter, MeromorphicAt (fun parameter => coefficients parameter index) parameter) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation (RecoveredAlgebraCombination.function flat coefficients) continuation ∧
      PlaneAverageContinuation.Regular continuation ∧ CompactContinuation.Regular continuation := by
  choose continuations continues regular compactRegular using fun index => finiteProjection (flat index)
  refine ⟨fun parameter point => ∑ index, coefficients parameter index * continuations index parameter point, ?_, ?_, ?_⟩
  · exact ContinuationAlgebra.finset_sum Finset.univ
      (fun index parameter point => coefficients parameter index *
        FiniteSectionProjection.sectionFunction ((flat index).1 parameter) point)
      (fun index parameter point => coefficients parameter index * continuations index parameter point)
      (fun index _ => ContinuationAlgebra.multiply (continues index)
        (fun parameter => coefficients parameter index) (meromorphic index))
  · exact PlaneAverageContinuation.regular_sum Finset.univ _
      (fun index _ => PlaneAverageContinuation.regular_mul (regular index)
        (fun parameter => coefficients parameter index) (meromorphic index))
  · exact CompactContinuation.regular_sum Finset.univ _
      (fun index _ => CompactContinuation.regular_mul (compactRegular index)
        (fun parameter => coefficients parameter index) (meromorphic index))

theorem exists_continuation {degree : ℕ} {data : InducingData degree}
    {original : ℂ → AdelicGL → ℂ} (flat : IsFlatSection data original) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation original continuation ∧ PlaneAverageContinuation.Regular continuation ∧ CompactContinuation.Regular continuation := by
  let basis := Module.finBasis ℂ (RecoveryTupleAlgebra.algebra data)
  obtain ⟨coefficients, cutoff, bound, meromorphic, inverse⟩ :=
    MeromorphicRecoveryAlgebra.exists_inverse_coefficients data basis
  choose families familiesFlat realizations using fun index =>
    FlatAlgebraRealization.exists_flat flat (basis index)
  obtain ⟨continuation, continues, regular, compactRegular⟩ := combination familiesFlat coefficients meromorphic
  refine ⟨continuation, ContinuationAlgebra.transfer continues cutoff ?_, regular, compactRegular⟩
  intro parameter above point
  exact congrFun (RecoveredAlgebraCombination.eq_original flat familiesFlat (fun index => basis index)
    coefficients realizations parameter (lt_trans bound above)
    (inverse ⟨parameter, lt_trans bound above⟩ above.le).1) point

end TernaryPeriodPolynomials.EdgeEisenstein.RecoveryConstruction
