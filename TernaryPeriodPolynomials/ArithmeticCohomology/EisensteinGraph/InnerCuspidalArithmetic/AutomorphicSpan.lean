module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.GoodFlags

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def realizedLineClasses (degree : ℕ) : Set (StratumH2 degree trivialCharacter .line) :=
  {coordinate | ∃ datum : CohomologicalCuspData degree, ∃ source,
    IsSourceCocycle datum.inducingData .line source ∧
    ∃ cycle : MaximalCycles degree trivialCharacter .line,
      Evaluates datum.inducingData .line source cycle ∧
      coordinate = classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree trivialCharacter) .line)
        cycle}

theorem automorphicLineSpan_eq_realizedSpan (degree : ℕ) :
    automorphicLineSpan degree = Submodule.span ℂ (realizedLineClasses degree) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro coordinate ⟨datum, membership⟩
    have summandIncluded : boundarySummand datum.inducingData .line ≤
        Submodule.span ℂ (realizedLineClasses degree) := by
      apply Submodule.span_le.mpr
      rintro image ⟨source, sourceCocycle, cycle, evaluation, sameClass⟩
      exact Submodule.subset_span ⟨datum, source, sourceCocycle, cycle,
        evaluation, sameClass⟩
    exact summandIncluded membership
  · apply Submodule.span_le.mpr
    rintro coordinate ⟨datum, source, sourceCocycle, cycle, evaluation, sameClass⟩
    apply boundarySummand_le_automorphicLineSpan datum
    exact Submodule.subset_span ⟨source, sourceCocycle, cycle, evaluation, sameClass⟩

theorem mem_automorphicLineSpan_iff_finite_sources (degree : ℕ)
    (coordinate : StratumH2 degree trivialCharacter .line) :
    coordinate ∈ automorphicLineSpan degree ↔
      ∃ coefficients : realizedLineClasses degree →₀ ℂ,
        coefficients.sum (fun image scalar => scalar • image.val) = coordinate := by
  rw [automorphicLineSpan_eq_realizedSpan,
    Finsupp.span_eq_range_linearCombination ℂ (realizedLineClasses degree)]
  simp only [LinearMap.mem_range, Finsupp.linearCombination_apply]

theorem cuspidalRecognition_line_mem_automorphicLineSpan {degree : ℕ}
    {coordinates : BoundaryCoordinates degree trivialCharacter}
    (recognition : CuspidalRecognition degree coordinates) :
    coordinates.2 ∈ automorphicLineSpan degree := by
  rcases recognition with ⟨hecke, heckeRealizes, count, data, projectors, data_spec⟩
  rcases data_spec with ⟨projector_prop, sum_identity⟩
  rw [← sum_identity]
  apply Submodule.sum_mem
  intro index _
  have projected_mem : projectors index coordinates ∈ LinearMap.range (projectors index) :=
    LinearMap.mem_range_self (projectors index) coordinates
  rw [(projector_prop index).1] at projected_mem
  have line_mem : (projectors index coordinates).2 ∈
      boundarySummand (data index).inducingData .line := by
    change (projectors index coordinates).1 ∈
        boundarySummand (data index).inducingData .plane ∧
      (projectors index coordinates).2 ∈
        boundarySummand (data index).inducingData .line at projected_mem
    exact projected_mem.2
  exact boundarySummand_le_automorphicLineSpan (data index) line_mem

theorem inner_bad_line_mem_automorphicLineSpan_of_cuspidalRecognition
    {degree : ℕ} (coordinate : StratumH2 degree trivialCharacter .line)
    (recognition : CuspidalRecognition degree (0, coordinate)) :
    coordinate ∈ automorphicLineSpan degree := by
  simpa using cuspidalRecognition_line_mem_automorphicLineSpan recognition

def innerBadLineClasses (degree : ℕ) :
    Submodule ℂ (StratumH2 degree trivialCharacter .line) :=
  (LinearMap.ker (endpointH2 degree trivialCharacter .line)) ⊓
    ⨅ flag : {flag : Flags .line // GoodFlag .line flag},
      LinearMap.ker (fixedPointH2 rationalLevel
        (rationalCoefficientComponent degree trivialCharacter) flag.val)

theorem mem_innerBadLineClasses_iff (degree : ℕ)
    (coordinate : StratumH2 degree trivialCharacter .line) :
    coordinate ∈ innerBadLineClasses degree ↔
      VanishesOnGood degree trivialCharacter .line coordinate ∧
      InnerBoundary degree trivialCharacter .line coordinate := by
  change (endpointH2 degree trivialCharacter .line coordinate = 0 ∧
    coordinate ∈ ⨅ flag : {flag : Flags .line // GoodFlag .line flag},
      LinearMap.ker (fixedPointH2 rationalLevel
        (rationalCoefficientComponent degree trivialCharacter) flag.val)) ↔ _
  constructor
  · rintro ⟨inner, good⟩
    have goodRestrictions := (Submodule.mem_iInf
      (M := H2 rationalLevel
        (functionRepresentation (rationalCoefficientComponent degree trivialCharacter)
          (Flags .line))) _).mp good
    refine ⟨(vanishesOnGood_iff_fixedPointH2 coordinate).mpr ?_,
      (innerBoundary_iff_endpointH2 coordinate).mpr inner⟩
    intro flag goodFlag
    exact goodRestrictions ⟨flag, goodFlag⟩
  · rintro ⟨good, inner⟩
    refine ⟨(innerBoundary_iff_endpointH2 coordinate).mp inner, ?_⟩
    apply (Submodule.mem_iInf
      (M := H2 rationalLevel
        (functionRepresentation (rationalCoefficientComponent degree trivialCharacter)
          (Flags .line))) _).mpr
    intro flag
    exact (vanishesOnGood_iff_fixedPointH2 coordinate).mp good flag.val flag.property

theorem innerBadLine_le_realizedSpan_iff (degree : ℕ) :
    innerBadLineClasses degree ≤ Submodule.span ℂ (realizedLineClasses degree) ↔
      ∀ coordinate : StratumH2 degree trivialCharacter .line,
        VanishesOnGood degree trivialCharacter .line coordinate →
        InnerBoundary degree trivialCharacter .line coordinate →
        coordinate ∈ automorphicLineSpan degree := by
  rw [← automorphicLineSpan_eq_realizedSpan]
  constructor
  · intro inclusion coordinate good inner
    exact inclusion ((mem_innerBadLineClasses_iff degree coordinate).mpr ⟨good, inner⟩)
  · intro spanning coordinate membership
    obtain ⟨good, inner⟩ := (mem_innerBadLineClasses_iff degree coordinate).mp membership
    exact spanning coordinate good inner

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
