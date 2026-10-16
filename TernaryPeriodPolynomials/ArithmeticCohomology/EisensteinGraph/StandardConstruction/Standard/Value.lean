module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.EisensteinValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.Invariance

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section


namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardValue

def HasRegularStandard (extension : ℂ → AdelicGL → ℂ) : Prop :=
  ∃ continuation : ℂ → AdelicGL → ℂ,
    IsStandardContinuation extension continuation ∧
      ∀ argument, AnalyticAt ℂ (fun parameter => continuation parameter argument)
        cohomologicalPoint

def regularFamilies {degree : ℕ} (data : InducingData degree) :
    Submodule ℂ (EisensteinValue.flatFamilies data) where
  carrier := {extension | HasRegularStandard extension.val}
  zero_mem' := ⟨fun _ _ => 0, FlatExtensions.standardContinuation_zero,
    fun _ => analyticAt_const⟩
  add_mem' {first second} firstRegular secondRegular := by
    obtain ⟨firstContinuation, firstContinues, firstAnalytic⟩ := firstRegular
    obtain ⟨secondContinuation, secondContinues, secondAnalytic⟩ := secondRegular
    exact ⟨fun parameter argument => firstContinuation parameter argument +
      secondContinuation parameter argument,
      LinearFamilies.standardContinuation_add _ _ _ _ firstContinues secondContinues,
      fun argument => (firstAnalytic argument).add (secondAnalytic argument)⟩
  smul_mem' scalar extension extensionRegular := by
    obtain ⟨continuation, continues, regular⟩ := extensionRegular
    exact ⟨fun parameter argument => scalar * continuation parameter argument,
      LinearFamilies.standardContinuation_smul scalar _ _ continues,
      fun argument => (regular argument).const_smul (c := scalar)⟩

def chosenContinuation {degree : ℕ} (data : InducingData degree)
    (extension : regularFamilies data) : ℂ → AdelicGL → ℂ :=
  Classical.choose extension.property

theorem chosenContinuation_spec {degree : ℕ} (data : InducingData degree)
    (extension : regularFamilies data) :
    IsStandardContinuation extension.val.val (chosenContinuation data extension) ∧
      ∀ argument, AnalyticAt ℂ
        (fun parameter => chosenContinuation data extension parameter argument)
        cohomologicalPoint :=
  Classical.choose_spec extension.property

def standardValue {degree : ℕ} (data : InducingData degree) :
    regularFamilies data →ₗ[ℂ] (AdelicGL → ℂ) where
  toFun extension := chosenContinuation data extension cohomologicalPoint
  map_add' first second := by
    have firstSpec := chosenContinuation_spec data first
    have secondSpec := chosenContinuation_spec data second
    have sumSpec := chosenContinuation_spec data (first + second)
    exact ContinuationUniqueness.standardContinuation_unique (first + second).val.val
      (chosenContinuation data (first + second))
      (fun parameter argument => chosenContinuation data first parameter argument +
        chosenContinuation data second parameter argument)
      sumSpec.1 (LinearFamilies.standardContinuation_add _ _ _ _ firstSpec.1 secondSpec.1)
      cohomologicalPoint sumSpec.2
      (fun argument => (firstSpec.2 argument).add (secondSpec.2 argument))
  map_smul' scalar extension := by
    have extensionSpec := chosenContinuation_spec data extension
    have multipleSpec := chosenContinuation_spec data (scalar • extension)
    exact ContinuationUniqueness.standardContinuation_unique (scalar • extension).val.val
      (chosenContinuation data (scalar • extension))
      (fun parameter argument => scalar * chosenContinuation data extension parameter argument)
      multipleSpec.1 (LinearFamilies.standardContinuation_smul scalar _ _ extensionSpec.1)
      cohomologicalPoint multipleSpec.2
      (fun argument => (extensionSpec.2 argument).const_smul (c := scalar))

theorem standardValue_realizes {degree : ℕ} (data : InducingData degree)
    (extension : regularFamilies data) (continuation : ℂ → AdelicGL → ℂ)
    (continues : IsStandardContinuation extension.val.val continuation)
    (regular : ∀ argument, AnalyticAt ℂ (fun parameter => continuation parameter argument)
      cohomologicalPoint) :
    standardValue data extension = continuation cohomologicalPoint := by
  have chosenSpec := chosenContinuation_spec data extension
  exact ContinuationUniqueness.standardContinuation_unique _ _ _ chosenSpec.1 continues
    cohomologicalPoint chosenSpec.2 regular

def radicalLevelFunctions : Submodule ℂ (AdelicGL → ℂ) where
  carrier := {function |
    (∀ first second argument,
      function (lineUnipotent first second * argument) = function argument) ∧
    (∀ levelElement : finiteLevel, ∀ argument,
      function (argument * atFinite levelElement.val) = function argument)}
  zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
  add_mem' {first second} firstInvariant secondInvariant := by
    constructor
    · intro firstCoordinate secondCoordinate argument
      change first _ + second _ = first _ + second _
      rw [firstInvariant.1, secondInvariant.1]
    · intro levelElement argument
      change first _ + second _ = first _ + second _
      rw [firstInvariant.2, secondInvariant.2]
  smul_mem' scalar function invariant := by
    constructor
    · intro firstCoordinate secondCoordinate argument
      change scalar • function _ = scalar • function _
      rw [invariant.1]
    · intro levelElement argument
      change scalar • function _ = scalar • function _
      rw [invariant.2]

theorem standardValue_invariant {degree : ℕ} (data : InducingData degree)
    (extension : regularFamilies data) :
    standardValue data extension ∈ radicalLevelFunctions := by
  have continuationSpec := chosenContinuation_spec data extension
  exact ⟨StandardInvariance.continuation_lineRadical _ _ continuationSpec.1
      cohomologicalPoint continuationSpec.2,
    StandardInvariance.continuation_finite data _ _ extension.val.property
      continuationSpec.1 cohomologicalPoint continuationSpec.2⟩

def invariantStandardValue {degree : ℕ} (data : InducingData degree) :
    regularFamilies data →ₗ[ℂ] radicalLevelFunctions :=
  (standardValue data).codRestrict radicalLevelFunctions (standardValue_invariant data)

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.StandardValue
