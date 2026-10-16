module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.EndpointSourceStandard
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.GlobalEisensteinCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.ConstantTerm
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.ScalarConvergence
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.Cohomological

@[expose] public section


/-!
# Constant terms of the standard operator (convergent)

The line constant term of the Eisenstein value is the standard value, by the half-plane constant-term identity `eisenstein_constantTerm` (no continuation).

Re-port of `TernaryPeriodPolynomials.EisensteinGraph.StandardConstantTermComparison` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
`PlaneEisensteinConvergent`; declarations that do not depend on the continuation hypothesis are
not copied (the original ones are used).  Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.StandardConstantTermComparison

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction


theorem sectionStandard_constantTerm {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : StandardConstruction.SectionSpace.inducedSections data .plane
      cohomologicalPoint)
    (argument : AdelicGL) :
    (EndpointStandardValue.sectionStandard data large holomorphic sectionValue).val argument =
      StandardConstruction.LineConstantTerm.average
        (SectionSpace.sectionEisensteinValue data holomorphic sectionValue).val argument := by
  rw [EndpointStandardValue.sectionStandard_eq_integral,
    StandardConstruction.LineConstantTerm.average_eq]
  have flat := (SectionSpace.linearFlatExtension data holomorphic sectionValue).property
  have constantTerm := StandardConstruction.CompactScalarConvergence.eisenstein_constantTerm data
    (SectionSpace.linearFlatExtension data holomorphic sectionValue).val flat cohomologicalPoint
    (StandardConstruction.HilbertCohomological.point_in_halfPlane degree large) argument
    (SectionSpace.sectionEisensteinValue data holomorphic sectionValue).val
    (fun value => (summable_cohomological holomorphic
      (SectionSpace.linearFlatExtension data holomorphic sectionValue).val flat value).hasSum)
  rw [constantTerm]
  simp only [standardIntegrand, SectionSpace.linearFlatExtension_endpoint]

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open StandardConstruction MeasureTheory
theorem polynomialStandard_coeff_constantTerm {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : PolynomialEisenstein.polynomialSections data)
    (argument : AdelicGL) (monomial : Fin 3 →₀ ℕ) :
    (EndpointPolynomialStandard.polynomialValue data large holomorphic sectionValue argument).val.coeff
        monomial =
      LineConstantTerm.average
        (fun point => (PolynomialEisenstein.polynomialValue data holomorphic sectionValue point).val.coeff
          monomial) argument := by
  rw [EndpointPolynomialStandard.polynomialValue_coeff, sectionStandard_constantTerm]
  congr 1
  funext point
  exact (PolynomialNaturality.polynomialValue_coeff data holomorphic sectionValue monomial point).symm

theorem sourceStandard_coeff_constantTerm {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane) (vertices : Fin 3 → RealGL3)
    (argument : AdelicGL) (monomial : Fin 3 →₀ ℕ) :
    ((EndpointSourceStandard.sourceStandard data large holomorphic source).val vertices argument).val.coeff
        monomial =
      ∫ pair in additiveDomain ×ˢ additiveDomain,
        (GlobalEisensteinCocycle.sourceValueAtReal data holomorphic source vertices
          (lineUnipotent pair.1 pair.2 * argument)).val.coeff monomial ∂radicalMeasure := by
  change (EndpointPolynomialStandard.polynomialValue data large holomorphic
    (PolynomialEisenstein.sourceSection data source vertices) argument).val.coeff monomial = _
  rw [polynomialStandard_coeff_constantTerm, LineConstantTerm.average_eq]
  rfl

theorem evaluatedStandard_coeff_constantTerm {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane) (vertices : Fin 3 → RationalGL3)
    (rational : RationalGL3) (monomial : Fin 3 →₀ ℕ) :
    ((SourceSpace.evaluatedSource data .line
        (EndpointSourceStandard.sourceStandard data large holomorphic source)).val.val vertices
        (QuotientGroup.mk rational)).val.coeff monomial =
      ∫ pair in additiveDomain ×ˢ additiveDomain,
        (GlobalEisensteinCocycle.sourceValueAtReal data holomorphic source
          (GlobalEisensteinCocycle.realVertices vertices)
          (lineUnipotent pair.1 pair.2 * rationalGroup rational⁻¹)).val.coeff monomial ∂radicalMeasure := by
  rw [SourceSpace.evaluatedSource_realizes]
  exact sourceStandard_coeff_constantTerm large data holomorphic source
    (GlobalEisensteinCocycle.realVertices vertices) (rationalGroup rational⁻¹) monomial



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.StandardConstantTermComparison
