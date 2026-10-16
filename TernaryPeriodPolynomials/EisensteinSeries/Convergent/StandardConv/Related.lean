module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.StandardConv.Defs
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.PolynomialFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.EndpointSourceStandard
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.ScalarConvergence

@[expose] public section


/-!
# The standard line cocycle is `RelatedConv` to the plane cocycle

For a plane source cocycle `c` of degree `n ≥ 4`, the standard family `J(s)` is the absolutely
convergent standard integral of the flat extension of `c`, coefficient by coefficient.  It is
analytic on the half plane `-n/2 < Re s` (`CompactScalarConvergence.standard_analyticAt`) and equals
the integral there (`standard_integrable`), so it satisfies `IsStandardConvergent` and
`RelatedConv` holds with the convergent `sourceStandard`.  In contrast to
`ConvergentEisenstein.EndpointSourceStandard.sourceStandard_related`, no meromorphic continuation of
the standard operator is used (`StandardContinuationConstruction.hasRegularStandard` is avoided).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.StandardConv

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

/-- The standard integral of a flat family is a half-plane standard family. -/
theorem isStandardConvergent_integral {degree : ℕ} (data : InducingData degree)
    (F : ℂ → AdelicGL → ℂ) (flat : IsFlatSection data F) :
    IsStandardConvergent degree F
      (fun s g => ∫ u, standardIntegrand F s g u ∂radicalMeasure) := by
  refine ⟨fun g s hs => ?_, -(degree : ℝ) / 2, fun s hs g => ?_⟩
  · exact (CompactScalarConvergence.standard_analyticAt data F flat s hs g).meromorphicAt
  · exact ⟨CompactScalarConvergence.standard_integrable data F flat s hs g, rfl⟩

/-- The zero family is a half-plane standard family of the zero family. -/
theorem isStandardConvergent_zero (degree : ℕ) :
    IsStandardConvergent degree (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨fun g s _ => analyticAt_const.meromorphicAt, 0, fun s _ g => ?_⟩
  refine ⟨?_, ?_⟩
  · have zero : standardIntegrand (fun (_ : ℂ) (_ : AdelicGL) => (0 : ℂ)) s g =
        fun _ => (0 : ℂ) := rfl
    rw [zero]
    exact MeasureTheory.integrable_zero _ _ _
  · simp [standardIntegrand]

/-- The standard family of a polynomial-valued section: the standard integral of the flat
extension of each coefficient. -/
def polynomialStandardFamily {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : PolynomialEisenstein.polynomialSections data) :
    ℂ → AdelicGL → HomogeneousPoly degree :=
  fun s g => FlatExtensions.assemblePolynomial degree (fun monomial =>
    ∫ u, standardIntegrand (SectionSpace.linearFlatExtension data holomorphic
      (PolynomialEisenstein.coefficientSection data monomial sectionValue)).val s g u
      ∂radicalMeasure)

theorem polynomialStandardFamily_convergent {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : PolynomialEisenstein.polynomialSections data) (monomial : Fin 3 →₀ ℕ) :
    IsStandardConvergent degree
      (fun parameter argument => (PolynomialFamilies.polynomialFlatExtension data holomorphic sectionValue parameter
          argument).val.coeff monomial)
      (fun parameter argument => (polynomialStandardFamily data holomorphic sectionValue parameter argument).val.coeff monomial) := by
  change IsStandardConvergent degree
    (fun parameter argument => (FlatExtensions.assemblePolynomial degree _).val.coeff monomial)
    (fun parameter argument => (FlatExtensions.assemblePolynomial degree _).val.coeff monomial)
  by_cases homogeneous : Finsupp.degree monomial = degree
  · simp only [FlatExtensions.assemblePolynomial_coeff, ite_eq_left homogeneous]
    exact isStandardConvergent_integral data _
      (SectionSpace.linearFlatExtension data holomorphic
        (PolynomialEisenstein.coefficientSection data monomial sectionValue)).property
  · simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_right homogeneous] using
      isStandardConvergent_zero degree

theorem polynomialStandardFamily_analytic {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : PolynomialEisenstein.polynomialSections data) (argument : AdelicGL)
    (monomial : Fin 3 →₀ ℕ) :
    AnalyticAt ℂ (fun parameter => (polynomialStandardFamily data holomorphic sectionValue parameter argument).val.coeff monomial)
      cohomologicalPoint := by
  change AnalyticAt ℂ (fun parameter => (FlatExtensions.assemblePolynomial degree _).val.coeff monomial) cohomologicalPoint
  by_cases homogeneous : Finsupp.degree monomial = degree
  · simp only [FlatExtensions.assemblePolynomial_coeff, ite_eq_left homogeneous]
    exact CompactScalarConvergence.standard_analyticAt data _
      (SectionSpace.linearFlatExtension data holomorphic
        (PolynomialEisenstein.coefficientSection data monomial sectionValue)).property
      cohomologicalPoint (HilbertCohomological.point_in_halfPlane degree holomorphic.large)
      argument
  · simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_right homogeneous] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) cohomologicalPoint)

theorem polynomialStandardFamily_endpoint {degree : ℕ} (data : InducingData degree)
    (large : 4 ≤ degree) (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : PolynomialEisenstein.polynomialSections data) :
    polynomialStandardFamily data holomorphic sectionValue cohomologicalPoint =
      EndpointPolynomialStandard.polynomialValue data large holomorphic sectionValue := rfl

/-- **The convergent standard line cocycle is related to the plane cocycle.** -/
theorem sourceStandard_relatedConv {degree : ℕ} (data : InducingData degree)
    (large : 4 ≤ degree) (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane) :
    RelatedConv data source (EndpointSourceStandard.sourceStandard data large holomorphic source) := by
  refine ⟨PolynomialFamilies.sourceFlatExtension data holomorphic source,
    fun parameter vertices => polynomialStandardFamily data holomorphic
      (PolynomialEisenstein.sourceSection data source vertices) parameter, ?_,
    PolynomialFamilies.sourceFlatExtension_endpoint data holomorphic source, ?_, ?_, rfl⟩
  · intro vertices monomial
    exact PolynomialFamilies.polynomialFlatExtension_flat data holomorphic
      (PolynomialEisenstein.sourceSection data source vertices) monomial
  · intro vertices monomial
    exact polynomialStandardFamily_convergent data holomorphic
      (PolynomialEisenstein.sourceSection data source vertices) monomial
  · intro vertices argument monomial
    exact polynomialStandardFamily_analytic data holomorphic
      (PolynomialEisenstein.sourceSection data source vertices) argument monomial

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.StandardConv
