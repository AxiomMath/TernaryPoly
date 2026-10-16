module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.BinaryCovariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.Truncation

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertCohomological

theorem point_in_halfPlane (degree : ℕ) (degreeAtLeastFour : 4 ≤ degree) :
    -(degree : ℝ) / 2 < cohomologicalPoint.re := by
  have bound : (4 : ℝ) ≤ degree := by exact_mod_cast degreeAtLeastFour
  norm_num [cohomologicalPoint]
  linarith

theorem integrand_integrable {degree : ℕ} (data : InducingData degree)
    (degreeAtLeastFour : 4 ≤ degree)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    MeasureTheory.Integrable
      (HilbertStandard.integrand data cohomologicalPoint sectionValue.val
        sectionValue.property argument) radicalMeasure :=
  HilbertStandard.integrand_integrable data cohomologicalPoint sectionValue.val
    sectionValue.property (point_in_halfPlane degree degreeAtLeastFour) argument

def valueLinear {degree : ℕ} (data : InducingData degree)
    (degreeAtLeastFour : 4 ≤ degree) :
    SectionSpace.inducedSections data .plane cohomologicalPoint →ₗ[ℂ]
      (AdelicGL → data.cusp.H) :=
  HilbertStandardAlgebra.valueLinear data cohomologicalPoint
    (point_in_halfPlane degree degreeAtLeastFour)

theorem valueLinear_def {degree : ℕ} (data : InducingData degree)
    (degreeAtLeastFour : 4 ≤ degree)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    valueLinear data degreeAtLeastFour sectionValue argument =
      ∫ coordinates, HilbertStandard.integrand data cohomologicalPoint
        sectionValue.val sectionValue.property argument coordinates ∂radicalMeasure := rfl

theorem valueLinear_lineLevi {degree : ℕ} (data : InducingData degree)
    (degreeAtLeastFour : 4 ≤ degree)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (binary : BinaryAdelicGL) (argument : AdelicGL) :
    valueLinear data degreeAtLeastFour sectionValue (lineLevi 1 binary * argument) =
      normPower (GeneralLinearGroup.det binary)
        (binaryInductionExponent degree .line cohomologicalPoint) •
        data.cusp.π binary (valueLinear data degreeAtLeastFour sectionValue argument) :=
  HilbertBinaryCovariance.value_lineLevi data cohomologicalPoint
    sectionValue.val sectionValue.property binary argument

theorem valueLinear_analytic {degree : ℕ} (data : InducingData degree)
    (degreeAtLeastFour : 4 ≤ degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) :
    AnalyticAt ℂ (fun parameter =>
      HilbertStandard.value data parameter (extension parameter) (flat.1 parameter) argument)
      cohomologicalPoint :=
  HilbertFlat.standard_analytic_halfPlane data extension flat argument cohomologicalPoint
    (point_in_halfPlane degree degreeAtLeastFour)

theorem valueLinear_jointContinuous {degree : ℕ} (data : InducingData degree)
    (degreeAtLeastFour : 4 ≤ degree)
    (extension : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data extension)
    (argument : AdelicGL) :
    ContinuousAt (fun pair : ℂ × AdelicGL =>
      HilbertStandard.value data pair.1 (extension pair.1) (flat.1 pair.1) pair.2)
      (cohomologicalPoint, argument) :=
  HilbertTruncation.standard_joint_continuousAt data extension flat cohomologicalPoint
    argument (point_in_halfPlane degree degreeAtLeastFour)

theorem regularHilbertExtension {degree : ℕ} (data : InducingData degree)
    (degreeAtLeastFour : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    ∃ extension : EisensteinValue.flatFamilies data,
      extension.val cohomologicalPoint = sectionValue.val ∧
      AnalyticAt ℂ (fun parameter =>
        HilbertStandard.value data parameter (extension.val parameter)
          (extension.property.1 parameter) argument) cohomologicalPoint ∧
      HilbertStandard.value data cohomologicalPoint (extension.val cohomologicalPoint)
        (extension.property.1 cohomologicalPoint) argument =
        valueLinear data degreeAtLeastFour sectionValue argument := by
  let extension := SectionSpace.linearFlatExtension data holomorphic sectionValue
  refine ⟨extension, SectionSpace.linearFlatExtension_endpoint data holomorphic sectionValue,
    valueLinear_analytic data degreeAtLeastFour extension.val extension.property argument, ?_⟩
  change HilbertStandard.value data cohomologicalPoint (extension.val cohomologicalPoint)
      (extension.property.1 cohomologicalPoint) argument =
    HilbertStandard.value data cohomologicalPoint sectionValue.val sectionValue.property argument
  have endpointSection :
      (⟨extension.val cohomologicalPoint, extension.property.1 cohomologicalPoint⟩ :
        SectionSpace.inducedSections data .plane cohomologicalPoint) = sectionValue :=
    Subtype.ext (SectionSpace.linearFlatExtension_endpoint data holomorphic sectionValue)
  exact congrArg (fun value : SectionSpace.inducedSections data .plane cohomologicalPoint =>
    HilbertStandard.value data cohomologicalPoint value.val value.property argument)
      endpointSection

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.HilbertCohomological
