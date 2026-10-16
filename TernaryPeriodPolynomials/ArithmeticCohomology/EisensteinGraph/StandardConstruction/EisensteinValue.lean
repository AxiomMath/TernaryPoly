module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.LinearFamilies

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EisensteinValue

def flatFamilies {degree : ℕ} (data : InducingData degree) :
    Submodule ℂ (ℂ → AdelicGL → ℂ) where
  carrier := {extension | IsFlatSection data extension}
  zero_mem' := FlatExtensions.flat_zero data
  add_mem' {first second} firstFlat secondFlat :=
    LinearFamilies.flat_add data first second firstFlat secondFlat
  smul_mem' scalar extension extensionFlat := by
    change IsFlatSection data (scalar • extension)
    simpa only [Pi.smul_def, smul_eq_mul] using
      LinearFamilies.flat_smul data scalar extension extensionFlat

def chosenContinuation {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (extension : flatFamilies data) :
    ℂ → AdelicGL → ℂ :=
  Classical.choose (holomorphic.2 extension.val extension.property)

theorem chosenContinuation_spec {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (extension : flatFamilies data) :
    IsEisensteinContinuation extension.val (chosenContinuation data holomorphic extension) ∧
      ∀ argument, AnalyticAt ℂ
        (fun parameter => chosenContinuation data holomorphic extension parameter argument)
        cohomologicalPoint :=
  Classical.choose_spec (holomorphic.2 extension.val extension.property)

theorem chosenContinuation_add {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (first second : flatFamilies data) :
    chosenContinuation data holomorphic (first + second) cohomologicalPoint =
      chosenContinuation data holomorphic first cohomologicalPoint +
        chosenContinuation data holomorphic second cohomologicalPoint := by
  have firstSpec := chosenContinuation_spec data holomorphic first
  have secondSpec := chosenContinuation_spec data holomorphic second
  have sumSpec := chosenContinuation_spec data holomorphic (first + second)
  exact ContinuationUniqueness.eisensteinContinuation_unique (first + second).val
    (chosenContinuation data holomorphic (first + second))
    (fun parameter argument => chosenContinuation data holomorphic first parameter argument +
      chosenContinuation data holomorphic second parameter argument)
    sumSpec.1 (LinearFamilies.eisensteinContinuation_add first.val second.val _ _
      firstSpec.1 secondSpec.1) cohomologicalPoint sumSpec.2
    (fun argument => (firstSpec.2 argument).add (secondSpec.2 argument))

theorem chosenContinuation_smul {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (scalar : ℂ)
    (extension : flatFamilies data) :
    chosenContinuation data holomorphic (scalar • extension) cohomologicalPoint =
      scalar • chosenContinuation data holomorphic extension cohomologicalPoint := by
  have extensionSpec := chosenContinuation_spec data holomorphic extension
  have multipleSpec := chosenContinuation_spec data holomorphic (scalar • extension)
  exact ContinuationUniqueness.eisensteinContinuation_unique (scalar • extension).val
    (chosenContinuation data holomorphic (scalar • extension))
    (fun parameter argument => scalar *
      chosenContinuation data holomorphic extension parameter argument)
    multipleSpec.1 (LinearFamilies.eisensteinContinuation_smul scalar extension.val _
      extensionSpec.1) cohomologicalPoint multipleSpec.2
    (fun argument => (extensionSpec.2 argument).const_smul (c := scalar))

def eisensteinValue {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    flatFamilies data →ₗ[ℂ] (AdelicGL → ℂ) where
  toFun extension := chosenContinuation data holomorphic extension cohomologicalPoint
  map_add' := chosenContinuation_add data holomorphic
  map_smul' := chosenContinuation_smul data holomorphic

theorem eisensteinValue_realizes {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (extension : flatFamilies data)
    (continuation : ℂ → AdelicGL → ℂ)
    (continues : IsEisensteinContinuation extension.val continuation)
    (regular : ∀ argument,
      AnalyticAt ℂ (fun parameter => continuation parameter argument) cohomologicalPoint) :
    eisensteinValue data holomorphic extension = continuation cohomologicalPoint := by
  have chosenSpec := chosenContinuation_spec data holomorphic extension
  exact ContinuationUniqueness.eisensteinContinuation_unique extension.val
    (chosenContinuation data holomorphic extension) continuation chosenSpec.1 continues
    cohomologicalPoint chosenSpec.2 regular

theorem eisensteinValue_holomorphyIndependent {degree : ℕ} (data : InducingData degree)
    (firstProof secondProof : PlaneEisensteinHolomorphic data) :
    eisensteinValue data firstProof = eisensteinValue data secondProof := by
  apply LinearMap.ext
  intro extension
  have secondSpec := chosenContinuation_spec data secondProof extension
  exact eisensteinValue_realizes data firstProof extension _ secondSpec.1 secondSpec.2

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EisensteinValue
