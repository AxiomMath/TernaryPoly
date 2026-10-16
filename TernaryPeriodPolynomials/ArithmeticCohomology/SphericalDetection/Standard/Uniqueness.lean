module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.FlatSectionSupport

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem flatSection_eq_of_endpoint {degree : ℕ} (data : InducingData degree)
    (first second : ℂ → AdelicGL → ℂ) (first_flat : IsFlatSection data first)
    (second_flat : IsFlatSection data second)
    (endpoint : first cohomologicalPoint = second cohomologicalPoint) : first = second := by
  funext parameter argument
  obtain ⟨radical_first, radical_second, scalar, block, compact, compact_member, factorization⟩ :=
    adelicGL_exists_induction_coordinates argument
  rw [factorization]
  exact flatSection_eq_on_parabolicCompact data first second first_flat second_flat endpoint
    parameter block scalar radical_first radical_second compact compact_member

theorem polynomialFlatSection_eq_of_endpoint {degree : ℕ} (data : InducingData degree)
    (first second : ℂ → SourceCochain degree)
    (first_flat : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (first parameter vertices argument).val.coeff monomial))
    (second_flat : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (second parameter vertices argument).val.coeff monomial))
    (endpoint : first cohomologicalPoint = second cohomologicalPoint) : first = second := by
  funext parameter vertices argument
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  have scalar_endpoint : (fun argument => (first cohomologicalPoint vertices argument).val.coeff monomial) =
      (fun argument => (second cohomologicalPoint vertices argument).val.coeff monomial) := by
    rw [endpoint]
  exact congrFun (congrFun (flatSection_eq_of_endpoint data _ _
    (first_flat vertices monomial) (second_flat vertices monomial) scalar_endpoint) parameter) argument

/-- The actual standard endpoint is independent of both the flat extension and the continuation. -/
theorem standardEndpoint_eq_of_same_source {degree : ℕ} (data : InducingData degree)
    (first_flat second_flat first_standard second_standard : ℂ → SourceCochain degree)
    (first_sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (first_flat parameter vertices argument).val.coeff monomial))
    (second_sections : ∀ vertices monomial, IsFlatSection data
      (fun parameter argument => (second_flat parameter vertices argument).val.coeff monomial))
    (endpoint : first_flat cohomologicalPoint = second_flat cohomologicalPoint)
    (first_continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (first_flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (first_standard parameter vertices argument).val.coeff monomial))
    (second_continuations : ∀ vertices monomial, IsStandardContinuation
      (fun parameter argument => (second_flat parameter vertices argument).val.coeff monomial)
      (fun parameter argument => (second_standard parameter vertices argument).val.coeff monomial))
    (first_analytic : ∀ vertices argument monomial, AnalyticAt ℂ
      (fun parameter => (first_standard parameter vertices argument).val.coeff monomial) cohomologicalPoint)
    (second_analytic : ∀ vertices argument monomial, AnalyticAt ℂ
      (fun parameter => (second_standard parameter vertices argument).val.coeff monomial) cohomologicalPoint) :
    first_standard cohomologicalPoint = second_standard cohomologicalPoint := by
  have same_flat := polynomialFlatSection_eq_of_endpoint data first_flat second_flat
    first_sections second_sections endpoint
  rw [same_flat] at first_continuations
  exact polynomialStandardContinuation_eq_at second_flat first_standard second_standard
    first_continuations second_continuations first_analytic second_analytic

theorem realizesStandard_eq_on_source {degree : ℕ} (data : InducingData degree)
    (first second : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (first_realizes : RealizesStandard data first) (second_realizes : RealizesStandard data second)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (cycle : MaximalCycles degree data.chi .plane) (evaluates : Evaluates data .plane source cycle)
    (member : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane)
      cycle ∈ boundarySummand data .plane) :
    first ⟨classOf rationalLevel (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) cycle, member⟩ =
      second ⟨classOf rationalLevel (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane) cycle, member⟩ := by
  have first_realized := first_realizes source cocycle cycle evaluates member
  obtain ⟨first_flat, first_standard, first_sections, first_endpoint, first_continuations,
    first_analytic, _, first_cycle, first_evaluates, first_represents⟩ := first_realized
  have second_realized := second_realizes source cocycle cycle evaluates member
  obtain ⟨second_flat, second_standard, second_sections, second_endpoint, second_continuations,
    second_analytic, _, second_cycle, second_evaluates, second_represents⟩ := second_realized
  have endpoint := standardEndpoint_eq_of_same_source data first_flat second_flat first_standard second_standard
    first_sections second_sections (first_endpoint.trans second_endpoint.symm) first_continuations second_continuations
    first_analytic second_analytic
  rw [← endpoint] at second_evaluates
  have same_cycle := evaluates_unique data .line (first_standard cohomologicalPoint) first_cycle second_cycle
    first_evaluates second_evaluates
  apply Subtype.ext
  rw [first_represents, second_represents, same_cycle]

/-- The standard operator on the entire supplied cuspidal boundary summand is unique. -/
theorem realizesStandard_unique {degree : ℕ} (data : InducingData degree)
    (first second : boundarySummand data .plane →ₗ[ℂ] boundarySummand data .line)
    (first_realizes : RealizesStandard data first) (second_realizes : RealizesStandard data second) : first = second := by
  let kernel_image := (LinearMap.ker (first - second)).map (boundarySummand data .plane).subtype
  have contains : boundarySummand data .plane ≤ kernel_image := by
    apply Submodule.span_le.mpr
    rintro value ⟨source, cocycle, cycle, evaluates, rfl⟩
    have member : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane)
        cycle ∈ boundarySummand data .plane :=
      Submodule.subset_span ⟨source, cocycle, cycle, evaluates, rfl⟩
    refine ⟨⟨_, member⟩, ?_, rfl⟩
    change first ⟨_, member⟩ - second ⟨_, member⟩ = 0
    exact sub_eq_zero.mpr (realizesStandard_eq_on_source data first second first_realizes second_realizes
      source cocycle cycle evaluates member)
  apply LinearMap.ext
  intro coordinate
  obtain ⟨preimage, in_kernel, same_value⟩ := contains coordinate.property
  have same_coordinate : preimage = coordinate := Subtype.ext same_value
  rw [same_coordinate] at in_kernel
  exact sub_eq_zero.mp in_kernel

end TernaryPeriodPolynomials.SphericalDetection.Helpers
