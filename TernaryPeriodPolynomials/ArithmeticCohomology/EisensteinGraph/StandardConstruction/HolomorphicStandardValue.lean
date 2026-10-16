module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.ContinuationConstruction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SectionSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.RankOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.StandardValue

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HolomorphicStandardValue

theorem continuation_eq_constantTerm {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (extension eisenstein standard : ℂ → AdelicGL → ℂ)
    (flat : IsFlatSection data extension)
    (eisensteinContinues : IsEisensteinContinuation extension eisenstein)
    (eisensteinAnalytic : ∀ argument,
      AnalyticAt ℂ (fun parameter => eisenstein parameter argument) cohomologicalPoint)
    (standardContinues : IsStandardContinuation extension standard)
    (standardAnalytic : ∀ argument,
      AnalyticAt ℂ (fun parameter => standard parameter argument) cohomologicalPoint)
    (argument : AdelicGL) :
    standard cohomologicalPoint argument =
      LineConstantTerm.average (eisenstein cohomologicalPoint) argument := by
  obtain ⟨raw, rawContinues, rawRegular, rawCompact⟩ := LineRecoveryConstruction.exists_continuation flat
  have rawStandard := StandardContinuationConstruction.average_continues data extension raw flat rawContinues rawRegular
  have integralLimit := LineCompactRegularity.average_tendsto flat holomorphic rawContinues rawRegular rawCompact
    eisensteinContinues eisensteinAnalytic argument
  have germ := ContinuationUniqueness.standardContinuation_germ extension standard
    (fun parameter => LineConstantTerm.average (raw parameter)) standardContinues rawStandard cohomologicalPoint argument
  exact tendsto_nhds_unique
    ((standardAnalytic argument).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (integralLimit.congr' germ.symm)

def regularFamily {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    EisensteinValue.flatFamilies data →ₗ[ℂ] StandardValue.regularFamilies data :=
  (LinearMap.id : EisensteinValue.flatFamilies data →ₗ[ℂ] EisensteinValue.flatFamilies data).codRestrict
    (StandardValue.regularFamilies data) (fun extension =>
      StandardContinuationConstruction.hasRegularStandard_of_holomorphic data extension.val extension.property holomorphic)

def flatStandard {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    EisensteinValue.flatFamilies data →ₗ[ℂ] StandardValue.radicalLevelFunctions :=
  (StandardValue.invariantStandardValue data).comp (regularFamily data holomorphic)

theorem flatStandard_constantTerm {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (extension : EisensteinValue.flatFamilies data) (argument : AdelicGL) :
    (flatStandard data holomorphic extension).val argument =
      LineConstantTerm.average (EisensteinValue.eisensteinValue data holomorphic extension) argument := by
  have eisenstein := EisensteinValue.chosenContinuation_spec data holomorphic extension
  have standard := StandardValue.chosenContinuation_spec data (regularFamily data holomorphic extension)
  exact continuation_eq_constantTerm data holomorphic extension.val
    (EisensteinValue.chosenContinuation data holomorphic extension)
    (StandardValue.chosenContinuation data (regularFamily data holomorphic extension))
    extension.property eisenstein.1 eisenstein.2 standard.1 standard.2 argument

theorem eisensteinValue_integrable {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (extension : EisensteinValue.flatFamilies data) (argument : AdelicGL) :
    Integrable (fun pair : Adeles × Adeles =>
      EisensteinValue.eisensteinValue data holomorphic extension (lineUnipotent pair.1 pair.2 * argument))
      LineConstantTerm.parameterMeasure := by
  obtain ⟨raw, rawContinues, rawRegular, rawCompact⟩ := LineRecoveryConstruction.exists_continuation extension.property
  have eisenstein := EisensteinValue.chosenContinuation_spec data holomorphic extension
  exact LineCompactRegularity.endpoint_integrable extension.property holomorphic rawContinues rawRegular rawCompact
    eisenstein.1 eisenstein.2 argument

theorem flatStandard_rankOne {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (extension : EisensteinValue.flatFamilies data) (unit : Adelesˣ) (argument : AdelicGL) :
    (flatStandard data holomorphic extension).val (lineLevi unit 1 * argument) =
      (data.chi.toMonoidHom unit * normPower unit 2) *
        (flatStandard data holomorphic extension).val argument :=
  StandardRankOne.standardValue_rankOne data (regularFamily data holomorphic extension) unit argument

def sectionStandard {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    SectionSpace.inducedSections data .plane cohomologicalPoint →ₗ[ℂ]
      StandardValue.radicalLevelFunctions :=
  (flatStandard data holomorphic).comp (SectionSpace.linearFlatExtension data holomorphic)

theorem sectionStandard_constantTerm {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) (argument : AdelicGL) :
    (sectionStandard data holomorphic sectionValue).val argument =
      LineConstantTerm.average (SectionSpace.sectionEisensteinValue data holomorphic sectionValue).val argument :=
  flatStandard_constantTerm data holomorphic (SectionSpace.linearFlatExtension data holomorphic sectionValue) argument

theorem sectionStandard_realizes {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsStandardContinuation (SectionSpace.linearFlatExtension data holomorphic sectionValue).val continuation ∧
      (∀ argument, AnalyticAt ℂ (fun parameter => continuation parameter argument) cohomologicalPoint) ∧
      (sectionStandard data holomorphic sectionValue).val = continuation cohomologicalPoint := by
  let extension := regularFamily data holomorphic (SectionSpace.linearFlatExtension data holomorphic sectionValue)
  exact ⟨StandardValue.chosenContinuation data extension,
    (StandardValue.chosenContinuation_spec data extension).1,
    (StandardValue.chosenContinuation_spec data extension).2, rfl⟩

theorem sectionStandard_eq_previous {degree : ℕ} (data : InducingData degree)
    (large : 4 ≤ degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    (sectionStandard data holomorphic sectionValue).val =
      (EndpointStandardValue.sectionStandard data large holomorphic sectionValue).val := rfl

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HolomorphicStandardValue
