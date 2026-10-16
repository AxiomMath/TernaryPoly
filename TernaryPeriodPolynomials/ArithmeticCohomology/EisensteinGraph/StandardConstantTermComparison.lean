module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.GlobalEisenstein
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardExistence

@[expose] public section


/-! Ported from the Sol reference implementation. -/

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstantTermComparison

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open StandardConstruction MeasureTheory

theorem sectionStandard_constantTerm {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    (EndpointStandardValue.sectionStandard data large holomorphic sectionValue).val argument =
      LineConstantTerm.average (SectionSpace.sectionEisensteinValue data holomorphic sectionValue).val
        argument := by
  obtain ⟨eisenstein, eisenstein_actual, eisenstein_analytic, eisenstein_value⟩ :=
    SectionSpace.sectionEisensteinValue_realizes data holomorphic sectionValue
  obtain ⟨standard, standard_actual, standard_analytic, standard_value⟩ :=
    EndpointStandardValue.sectionStandard_realizes data large holomorphic sectionValue
  rw [standard_value, eisenstein_value]
  exact HolomorphicStandardValue.continuation_eq_constantTerm data holomorphic
    (SectionSpace.linearFlatExtension data holomorphic sectionValue).val eisenstein standard
    (SectionSpace.linearFlatExtension data holomorphic sectionValue).property
    eisenstein_actual eisenstein_analytic standard_actual standard_analytic argument

theorem polynomialStandard_coeff_constantTerm {degree : ℕ} (large : 4 ≤ degree)
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
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
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
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
    (data : InducingData degree) (holomorphic : PlaneEisensteinHolomorphic data)
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

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstantTermComparison
