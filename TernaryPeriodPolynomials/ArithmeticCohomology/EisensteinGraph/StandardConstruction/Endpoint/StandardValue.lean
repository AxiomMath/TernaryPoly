module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Standard.ContinuationConstruction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.StandardInduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RealTranslations

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointStandardValue

theorem standardValue_eq_integral {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (extension : StandardValue.regularFamilies data) (argument : AdelicGL) :
    StandardValue.standardValue data extension argument =
      ∫ coordinates, standardIntegrand extension.val.val cohomologicalPoint argument coordinates ∂radicalMeasure := by
  have spec := StandardValue.chosenContinuation_spec data extension
  have equality := StandardContinuationRegularity.germ_eq_integral data extension.val.val
    (StandardValue.chosenContinuation data extension) extension.val.property spec.1 argument cohomologicalPoint
    (HilbertCohomological.point_in_halfPlane degree large)
  exact ((spec.2 argument).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (CompactScalarConvergence.standard_endpoint_analyticAt data extension.val.val extension.val.property
      large argument).continuousAt).mp equality |>.eq_of_nhds

def regularFamily {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree) :
    EisensteinValue.flatFamilies data →ₗ[ℂ] StandardValue.regularFamilies data :=
  (LinearMap.id : EisensteinValue.flatFamilies data →ₗ[ℂ] EisensteinValue.flatFamilies data).codRestrict
    (StandardValue.regularFamilies data) (fun extension =>
      StandardContinuationConstruction.hasRegularStandard data extension.val extension.property large)

def flatStandard {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree) :
    EisensteinValue.flatFamilies data →ₗ[ℂ] SectionSpace.inducedSections data .line cohomologicalPoint :=
  ((StandardValue.standardValue data).comp (regularFamily data large)).codRestrict
    (SectionSpace.inducedSections data .line cohomologicalPoint) (by
      intro extension
      have equality : StandardValue.standardValue data (regularFamily data large extension) =
          fun argument => ∫ coordinates,
            standardIntegrand extension.val cohomologicalPoint argument coordinates ∂radicalMeasure := by
        funext argument
        exact standardValue_eq_integral data large (regularFamily data large extension) argument
      change IsInduced data .line cohomologicalPoint
        (StandardValue.standardValue data (regularFamily data large extension))
      rw [equality]
      exact EndpointStandardInduction.integral_induced data large extension.val extension.property)

theorem flatStandard_eq_integral {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (extension : EisensteinValue.flatFamilies data) (argument : AdelicGL) :
    (flatStandard data large extension).val argument =
      ∫ coordinates, standardIntegrand extension.val cohomologicalPoint argument coordinates ∂radicalMeasure :=
  standardValue_eq_integral data large (regularFamily data large extension) argument

def sectionStandard {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    SectionSpace.inducedSections data .plane cohomologicalPoint →ₗ[ℂ]
      SectionSpace.inducedSections data .line cohomologicalPoint :=
  (flatStandard data large).comp (SectionSpace.linearFlatExtension data holomorphic)

theorem sectionStandard_eq_integral {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) (argument : AdelicGL) :
    (sectionStandard data large holomorphic sectionValue).val argument =
      ∫ coordinates : Adeles × Adeles,
        sectionValue.val (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument) ∂radicalMeasure := by
  change (flatStandard data large (SectionSpace.linearFlatExtension data holomorphic sectionValue)).val argument = _
  rw [flatStandard_eq_integral]
  simp only [standardIntegrand, SectionSpace.linearFlatExtension_endpoint]

theorem sectionStandard_right_real {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) (real : RealGL3) :
    sectionStandard data large holomorphic
        (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue) =
      RealTranslations.sectionRightReal data .line cohomologicalPoint real
        (sectionStandard data large holomorphic sectionValue) := by
  apply Subtype.ext
  funext argument
  change _ = (sectionStandard data large holomorphic sectionValue).val (argument * atInfinity real)
  rw [sectionStandard_eq_integral, sectionStandard_eq_integral]
  simp only [RealTranslations.sectionRightReal, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]

theorem sectionStandard_realizes {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    ∃ continuation : ℂ → AdelicGL → ℂ,
      IsStandardContinuation (SectionSpace.linearFlatExtension data holomorphic sectionValue).val continuation ∧
      (∀ argument, AnalyticAt ℂ (fun parameter => continuation parameter argument) cohomologicalPoint) ∧
      (sectionStandard data large holomorphic sectionValue).val = continuation cohomologicalPoint := by
  let extension := regularFamily data large (SectionSpace.linearFlatExtension data holomorphic sectionValue)
  exact ⟨StandardValue.chosenContinuation data extension,
    (StandardValue.chosenContinuation_spec data extension).1,
    (StandardValue.chosenContinuation_spec data extension).2, rfl⟩

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointStandardValue
