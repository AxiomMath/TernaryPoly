module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.SourceStandard
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardWitness

@[expose] public section


/-! Ported from the Sol reference implementation. -/

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardExistence

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open StandardConstruction

theorem scalar_standard_continuation {degree : ℕ} (data : InducingData degree)
    (family : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data family) :
    ∃ continuation : ℂ → AdelicGL → ℂ, IsStandardContinuation family continuation :=
  StandardContinuationConstruction.exists_continuation data family flat

theorem scalar_standard_regular_of_holomorphic {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (family : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data family) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsStandardContinuation family continuation ∧
        ∀ matrix, AnalyticAt ℂ (fun parameter => continuation parameter matrix) cohomologicalPoint :=
  StandardContinuationConstruction.hasRegularStandard_of_holomorphic data family flat holomorphic

theorem source_standard_exists_of_large_degree {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (source : SourceCochain degree) (closed : IsSourceCocycle data .plane source) :
    ∃ family continuation : ℂ → SourceCochain degree,
      (∀ vertices monomial, IsFlatSection data
        (fun parameter matrix => (family parameter vertices matrix).val.coeff monomial)) ∧
      family cohomologicalPoint = source ∧
      (∀ vertices monomial, IsStandardContinuation
        (fun parameter matrix => (family parameter vertices matrix).val.coeff monomial)
        (fun parameter matrix => (continuation parameter vertices matrix).val.coeff monomial)) ∧
      (∀ vertices matrix monomial, AnalyticAt ℂ
        (fun parameter => (continuation parameter vertices matrix).val.coeff monomial) cohomologicalPoint) ∧
      IsSourceCocycle data .line (continuation cohomologicalPoint) := by
  let plane : SourceSpace.sourceCocycles data .plane := ⟨source, closed⟩
  obtain ⟨line, family, continuation, flat, endpoint, actual, analytic, value⟩ :=
    EndpointSourceStandard.related_total data large holomorphic plane
  refine ⟨family, continuation, flat, endpoint, actual, analytic, ?_⟩
  rw [value]
  exact line.property

theorem standard_source_relation_single_valued {degree : ℕ} (data : InducingData degree)
    (plane : SourceSpace.sourceCocycles data .plane)
    (first second : SourceSpace.sourceCocycles data .line)
    (first_related : StandardRelation.Related data plane first)
    (second_related : StandardRelation.Related data plane second) : first = second := by
  obtain ⟨first_family, first_continuation, first_flat, first_endpoint, first_actual,
    first_analytic, first_value⟩ := first_related
  obtain ⟨second_family, second_continuation, second_flat, second_endpoint, second_actual,
    second_analytic, second_value⟩ := second_related
  have family_eq := StandardUniqueness.sourceFlatFamilies_eq_of_endpoint data
    first_family second_family first_flat second_flat (first_endpoint.trans second_endpoint.symm)
  rw [← family_eq] at second_actual
  have continuation_eq := StandardUniqueness.sourceStandardEndpoints_eq first_family
    first_continuation second_continuation first_actual second_actual first_analytic second_analytic
  apply Subtype.ext
  exact first_value.symm.trans (continuation_eq.trans second_value)

theorem standard_source_relation_eq_sourceStandard {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (plane : SourceSpace.sourceCocycles data .plane)
    (line : SourceSpace.sourceCocycles data .line)
    (related : StandardRelation.Related data plane line) :
    line = EndpointSourceStandard.sourceStandard data large holomorphic plane :=
  standard_source_relation_single_valued data plane line _ related
    (EndpointSourceStandard.sourceStandard_related data large holomorphic plane)

theorem continuationWitness_exists_of_large_degree {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (source : SourceCochain degree) (closed : IsSourceCocycle data .plane source) :
    Nonempty (StandardWitness.ContinuationWitness data source) := by
  obtain ⟨family, continuation, flat, endpoint, actual, analytic, line_closed⟩ :=
    source_standard_exists_of_large_degree large data holomorphic source closed
  let line : SourceSpace.sourceCocycles data .line := ⟨continuation cohomologicalPoint, line_closed⟩
  exact ⟨⟨family, continuation, SourceSpace.evaluatedSource data .line line,
    flat, endpoint, actual, analytic, SourceSpace.evaluatedSource_realizes data .line line⟩⟩

theorem realizesStandard_sourceStandard_value {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (actual : RealizesStandard data standard)
    (plane : SourceSpace.sourceCocycles data .plane) :
    standard (SourceQuotient.sourceToSummand data .plane plane) =
      SourceQuotient.sourceToSummand data .line
        (EndpointSourceStandard.sourceStandard data large holomorphic plane) := by
  obtain ⟨line, related, value⟩ := (StandardRelation.realizesStandard_iff data standard).mp actual plane
  rw [standard_source_relation_eq_sourceStandard large data holomorphic plane line related] at value
  exact value

end TernaryPeriodPolynomials.EisensteinGraph.StandardExistence
