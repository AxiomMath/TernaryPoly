module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RationalEisenstein
public import Mathlib.Algebra.Module.Projective

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SectionSpace

def inducedSections {degree : ℕ} (data : InducingData degree) (side : Side)
    (parameter : ℂ) : Submodule ℂ (AdelicGL → ℂ) where
  carrier := {function | IsInduced data side parameter function}
  zero_mem' := FlatExtensions.induced_zero data side parameter
  add_mem' {first second} firstInduced secondInduced :=
    LinearFamilies.induced_add data side parameter first second firstInduced secondInduced
  smul_mem' scalar function induced := by
    change IsInduced data side parameter (scalar • function)
    simpa only [Pi.smul_def, smul_eq_mul] using
      LinearFamilies.induced_smul data side parameter scalar function induced

def endpointEvaluation {degree : ℕ} (data : InducingData degree) :
    EisensteinValue.flatFamilies data →ₗ[ℂ]
      inducedSections data .plane cohomologicalPoint where
  toFun extension := ⟨extension.val cohomologicalPoint,
    extension.property.1 cohomologicalPoint⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem endpointEvaluation_surjective {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    Function.Surjective (endpointEvaluation data) := by
  intro sectionValue
  obtain ⟨extension, flat, realizes⟩ := holomorphic.1 sectionValue.val sectionValue.property
  refine ⟨⟨extension, flat⟩, ?_⟩
  exact Subtype.ext realizes

theorem flatExtension_exists {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    ∃ extension : inducedSections data .plane cohomologicalPoint →ₗ[ℂ]
        EisensteinValue.flatFamilies data,
      (endpointEvaluation data).comp extension = LinearMap.id := by
  exact (endpointEvaluation data).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (endpointEvaluation_surjective data holomorphic))

def linearFlatExtension {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    inducedSections data .plane cohomologicalPoint →ₗ[ℂ]
      EisensteinValue.flatFamilies data :=
  Classical.choose (flatExtension_exists data holomorphic)

theorem linearFlatExtension_endpoint {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : inducedSections data .plane cohomologicalPoint) :
    (linearFlatExtension data holomorphic sectionValue).val cohomologicalPoint =
      sectionValue.val := by
  have rightInverse := Classical.choose_spec (flatExtension_exists data holomorphic)
  exact congrArg Subtype.val (congrArg (fun operator => operator sectionValue) rightInverse)

def sectionEisensteinValue {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    inducedSections data .plane cohomologicalPoint →ₗ[ℂ]
      RationalEisenstein.automorphicFunctions :=
  (RationalEisenstein.automorphicEisensteinValue data holomorphic).comp
    (linearFlatExtension data holomorphic)

theorem sectionEisensteinValue_realizes {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : inducedSections data .plane cohomologicalPoint) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsEisensteinContinuation
        (linearFlatExtension data holomorphic sectionValue).val continuation ∧
      (∀ argument, AnalyticAt ℂ (fun parameter => continuation parameter argument)
        cohomologicalPoint) ∧
      (sectionEisensteinValue data holomorphic sectionValue).val =
        continuation cohomologicalPoint := by
  refine ⟨EisensteinValue.chosenContinuation data holomorphic
    (linearFlatExtension data holomorphic sectionValue), ?_, ?_, rfl⟩
  · exact (EisensteinValue.chosenContinuation_spec data holomorphic _).1
  · exact (EisensteinValue.chosenContinuation_spec data holomorphic _).2

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SectionSpace
