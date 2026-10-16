module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.SectionSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.StandardInduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.ScalarConvergence
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.RealTranslations

@[expose] public section


/-!
# The standard operator at the cohomological point (convergent)

For degrees at least four the standard integral of a flat family converges absolutely at the cohomological point; the standard value is that integral (CF5), with no meromorphic continuation of the standard operator.

Re-port of `TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointStandardValue` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
`PlaneEisensteinConvergent`; declarations that do not depend on the continuation hypothesis are
not copied (the original ones are used).  Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.EndpointStandardValue

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction


/-- The standard integral of a flat family at the cohomological point, as an induced line
section.  Its linearity is `integral_add`/`integral_smul` for the integrable integrands
(CF5). -/
def flatStandard {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree) :
    StandardConstruction.EisensteinValue.flatFamilies data →ₗ[ℂ]
      StandardConstruction.SectionSpace.inducedSections data .line cohomologicalPoint where
  toFun extension := ⟨fun argument => ∫ coordinates,
      standardIntegrand extension.val cohomologicalPoint argument coordinates ∂radicalMeasure,
    StandardConstruction.EndpointStandardInduction.integral_induced data large extension.val
      extension.property⟩
  map_add' first second := by
    apply Subtype.ext
    funext argument
    change ∫ coordinates, (standardIntegrand first.val cohomologicalPoint argument coordinates +
        standardIntegrand second.val cohomologicalPoint argument coordinates) ∂radicalMeasure =
      (∫ coordinates, standardIntegrand first.val cohomologicalPoint argument coordinates
        ∂radicalMeasure) +
      ∫ coordinates, standardIntegrand second.val cohomologicalPoint argument coordinates
        ∂radicalMeasure
    exact MeasureTheory.integral_add
      (StandardConstruction.CompactScalarConvergence.standard_endpoint_integrable data first.val
        first.property large argument)
      (StandardConstruction.CompactScalarConvergence.standard_endpoint_integrable data second.val
        second.property large argument)
  map_smul' scalar extension := by
    apply Subtype.ext
    funext argument
    change ∫ coordinates, scalar * standardIntegrand extension.val cohomologicalPoint argument
        coordinates ∂radicalMeasure =
      scalar * ∫ coordinates, standardIntegrand extension.val cohomologicalPoint argument
        coordinates ∂radicalMeasure
    exact MeasureTheory.integral_const_mul _ _

theorem flatStandard_eq_integral {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (extension : StandardConstruction.EisensteinValue.flatFamilies data) (argument : AdelicGL) :
    (flatStandard data large extension).val argument =
      ∫ coordinates, standardIntegrand extension.val cohomologicalPoint argument coordinates
        ∂radicalMeasure := rfl

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory Filter Topology
def sectionStandard {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data) :
    SectionSpace.inducedSections data .plane cohomologicalPoint →ₗ[ℂ]
      SectionSpace.inducedSections data .line cohomologicalPoint :=
  (flatStandard data large).comp (SectionSpace.linearFlatExtension data holomorphic)

theorem sectionStandard_eq_integral {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) (argument : AdelicGL) :
    (sectionStandard data large holomorphic sectionValue).val argument =
      ∫ coordinates : Adeles × Adeles,
        sectionValue.val (weyl⁻¹ * lineUnipotent coordinates.1 coordinates.2 * argument) ∂radicalMeasure := by
  change (flatStandard data large (SectionSpace.linearFlatExtension data holomorphic sectionValue)).val argument = _
  rw [flatStandard_eq_integral]
  simp only [standardIntegrand, SectionSpace.linearFlatExtension_endpoint]

theorem sectionStandard_right_real {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data)
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



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.EndpointStandardValue
