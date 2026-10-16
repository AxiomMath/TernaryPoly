module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardUniqueness

@[expose] public section


/-! Ported from the Sol reference implementation. -/

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardWitness

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

theorem realizesStandard_has_witness {degree : ℕ} (data : InducingData degree)
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (actual : RealizesStandard data standard)
    (source : SourceCochain degree) (closed : IsSourceCocycle data .plane source)
    (representative : MaximalCycles degree data.chi .plane)
    (evaluation : Evaluates data .plane source representative)
    (member : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) representative ∈
        boundarySummand data .plane) :
    ∃ (family continued : ℂ → SourceCochain degree)
      (output : MaximalCycles degree data.chi .line),
      (∀ vertices monomial, IsFlatSection data
        (fun parameter matrix => (family parameter vertices matrix).val.coeff monomial)) ∧
      family cohomologicalPoint = source ∧
      (∀ vertices monomial, IsStandardContinuation
        (fun parameter matrix => (family parameter vertices matrix).val.coeff monomial)
        (fun parameter matrix => (continued parameter vertices matrix).val.coeff monomial)) ∧
      (∀ vertices matrix monomial, AnalyticAt ℂ
        (fun parameter => (continued parameter vertices matrix).val.coeff monomial) cohomologicalPoint) ∧
      Evaluates data .line (continued cohomologicalPoint) output ∧
      (standard ⟨classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) representative, member⟩).val =
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent degree data.chi) .line) output := by
  rcases actual source closed representative evaluation member with ⟨family, continued, spec⟩
  rcases spec with ⟨flat, endpoint, continuation, analytic, _, output, output_evaluation, equality⟩
  exact ⟨family, continued, output, flat, endpoint, continuation, analytic, output_evaluation, equality⟩

structure ContinuationWitness {degree : ℕ} (data : InducingData degree) (source : SourceCochain degree) where
  family : ℂ → SourceCochain degree
  continued : ℂ → SourceCochain degree
  output : MaximalCycles degree data.chi .line
  flat : ∀ vertices monomial, IsFlatSection data
    (fun parameter matrix => (family parameter vertices matrix).val.coeff monomial)
  endpoint : family cohomologicalPoint = source
  actual : ∀ vertices monomial, IsStandardContinuation
    (fun parameter matrix => (family parameter vertices matrix).val.coeff monomial)
    (fun parameter matrix => (continued parameter vertices matrix).val.coeff monomial)
  analytic : ∀ vertices matrix monomial, AnalyticAt ℂ
    (fun parameter => (continued parameter vertices matrix).val.coeff monomial) cohomologicalPoint
  evaluation : Evaluates data .line (continued cohomologicalPoint) output

theorem realizesStandard_continuationWitness {degree : ℕ} (data : InducingData degree)
    (standard : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (actual : RealizesStandard data standard)
    (source : SourceCochain degree) (closed : IsSourceCocycle data .plane source)
    (representative : MaximalCycles degree data.chi .plane)
    (evaluation : Evaluates data .plane source representative)
    (member : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) representative ∈
        boundarySummand data .plane) :
    ∃ witness : ContinuationWitness data source,
      (standard ⟨classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) representative, member⟩).val =
        classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent degree data.chi) .line) witness.output := by
  rcases actual source closed representative evaluation member with ⟨family, continued, spec⟩
  rcases spec with ⟨flat, endpoint, continuation, analytic, _, output, output_evaluation, equality⟩
  exact ⟨⟨family, continued, output, flat, endpoint, continuation, analytic, output_evaluation⟩, equality⟩

theorem ContinuationWitness.output_eq {degree : ℕ} {data : InducingData degree}
    {source : SourceCochain degree} (first second : ContinuationWitness data source) :
    first.output = second.output := by
  have family_eq := StandardUniqueness.sourceFlatFamilies_eq_of_endpoint data first.family second.family
    first.flat second.flat (first.endpoint.trans second.endpoint.symm)
  have second_actual := second.actual
  rw [← family_eq] at second_actual
  have standard_eq := StandardUniqueness.sourceStandardEndpoints_eq first.family first.continued second.continued
    first.actual second_actual first.analytic second.analytic
  have second_evaluation := second.evaluation
  rw [← standard_eq] at second_evaluation
  exact StandardUniqueness.evaluations_unique data .line _ first.output second.output
    first.evaluation second_evaluation

theorem realizesStandard_apply_eq {degree : ℕ} (data : InducingData degree)
    (first second : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (first_actual : RealizesStandard data first) (second_actual : RealizesStandard data second)
    (source : SourceCochain degree) (closed : IsSourceCocycle data .plane source)
    (representative : MaximalCycles degree data.chi .plane)
    (evaluation : Evaluates data .plane source representative)
    (member : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) representative ∈
        boundarySummand data .plane) :
    first ⟨classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) representative, member⟩ =
    second ⟨classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) representative, member⟩ := by
  let first_exists :=
    realizesStandard_continuationWitness data first first_actual source closed representative evaluation member
  let second_exists :=
    realizesStandard_continuationWitness data second second_actual source closed representative evaluation member
  let first_witness : ContinuationWitness data source := Classical.choose first_exists
  let second_witness : ContinuationWitness data source := Classical.choose second_exists
  have first_output := Classical.choose_spec first_exists
  have second_output := Classical.choose_spec second_exists
  have representatives_eq := first_witness.output_eq second_witness
  apply Subtype.ext
  exact first_output.trans ((congrArg (classOf rationalLevel
    (flagRepresentation (rationalCoefficientComponent degree data.chi) .line)) representatives_eq).trans
    second_output.symm)

theorem realizesStandard_unique {degree : ℕ} (data : InducingData degree)
    (first second : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (first_actual : RealizesStandard data first) (second_actual : RealizesStandard data second) :
    first = second := by
  let generators : Set (StratumH2 degree data.chi .plane) :=
    {component | ∃ source, IsSourceCocycle data .plane source ∧ ∃ representative,
      Evaluates data .plane source representative ∧ component = classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) representative}
  have span_eq : boundarySummand data .plane = Submodule.span ℂ generators := rfl
  apply (Submodule.linearMap_eq_iff_of_eq_span first second span_eq).mpr
  rintro ⟨component, source, closed, representative, evaluation, rfl⟩
  exact realizesStandard_apply_eq data first second first_actual second_actual source closed
    representative evaluation _

end TernaryPeriodPolynomials.EisensteinGraph.StandardWitness
