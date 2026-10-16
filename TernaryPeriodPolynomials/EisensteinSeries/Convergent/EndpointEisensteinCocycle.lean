module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.PolynomialNaturality
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.GlobalEisensteinCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.EisensteinCocycle

@[expose] public section


/-!
# The global Eisenstein cocycle at the cohomological point (convergent)

For degrees at least four the Eisenstein value used by the construction is the absolutely convergent sum over flags (`sectionEisensteinValue_eq_sum`, by definition); real covariance and the global cocycle follow.

Re-port of `TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointEisensteinCocycle` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
`PlaneEisensteinConvergent`; declarations that do not depend on the continuation hypothesis are
not copied (the original ones are used).  Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.EndpointEisensteinCocycle

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointEisensteinCocycle


theorem sectionEisensteinValue_eq_sum {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) (_degreeBound : 4 ≤ degree)
    (sectionValue : StandardConstruction.SectionSpace.inducedSections data .plane
      cohomologicalPoint)
    (argument : AdelicGL) :
    (SectionSpace.sectionEisensteinValue data holomorphic sectionValue).val argument =
      ∑' flag : Flags .plane, sectionValue.val (rationalGroup flag.out⁻¹ * argument) := by
  change ∑' flag : Flags .plane, eisensteinSummand
    (SectionSpace.linearFlatExtension data holomorphic sectionValue).val cohomologicalPoint
      argument flag = _
  simp only [eisensteinSummand, SectionSpace.linearFlatExtension_endpoint]

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
theorem sectionEisensteinValue_right_real {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) (degreeBound : 4 ≤ degree)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (real : RealGL3) (argument : AdelicGL) :
    (SectionSpace.sectionEisensteinValue data holomorphic
      (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue)).val
      argument =
        (SectionSpace.sectionEisensteinValue data holomorphic sectionValue).val
          (argument * atInfinity real) := by
  rw [sectionEisensteinValue_eq_sum data holomorphic degreeBound,
    sectionEisensteinValue_eq_sum data holomorphic degreeBound]
  change (∑' flag : Flags .plane,
    sectionValue.val ((rationalGroup flag.out⁻¹ * argument) * atInfinity real)) = _
  simp only [mul_assoc]

theorem polynomialValue_right_real {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) (degreeBound : 4 ≤ degree)
    (sectionValue : PolynomialEisenstein.polynomialSections data)
    (real : RealGL3) (argument : AdelicGL) :
    PolynomialEisenstein.polynomialValue data holomorphic
      (PolynomialNaturality.rightReal data real sectionValue) argument =
        PolynomialEisenstein.polynomialValue data holomorphic sectionValue
          (argument * atInfinity real) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  rw [PolynomialNaturality.polynomialValue_coeff,
    PolynomialNaturality.polynomialValue_coeff, PolynomialNaturality.coefficient_rightReal]
  exact sectionEisensteinValue_right_real data holomorphic degreeBound _ real argument

theorem sourceValue_real_covariant {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) (degreeBound : 4 ≤ degree)
    (source : SourceSpace.sourceCocycles data .plane) (real : RealGL3)
    (vertices : Fin 3 → RealGL3) (argument : AdelicGL) :
    GlobalEisensteinCocycle.sourceValueAtReal data holomorphic source
      (fun index => real * vertices index) argument =
        realCoefficientComponent degree data.chi real
          (GlobalEisensteinCocycle.sourceValueAtReal data holomorphic source vertices
            (argument * atInfinity real)) := by
  unfold GlobalEisensteinCocycle.sourceValueAtReal
  rw [PolynomialNaturality.sourceSection_transformed,
    PolynomialNaturality.polynomialValue_coefficientMap,
    polynomialValue_right_real data holomorphic degreeBound]

def globalCocycle {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) (degreeBound : 4 ≤ degree)
    (source : SourceSpace.sourceCocycles data .plane) :
    cocycles rationalLevel (rationalCoefficientComponent degree data.chi) :=
  GlobalEisensteinCocycle.globalCocycle_of_realCovariance data holomorphic source
    (sourceValue_real_covariant data holomorphic degreeBound source)

theorem globalCocycle_realizes {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) (degreeBound : 4 ≤ degree)
    (source : SourceSpace.sourceCocycles data .plane) (vertices : Fin 3 → RationalGL3) :
    (globalCocycle data holomorphic degreeBound source).val.val vertices =
      GlobalEisensteinCocycle.evaluatedSourceValue data holomorphic source vertices := rfl

def globalCocycleLinear {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) (degreeBound : 4 ≤ degree) :
    SourceSpace.sourceCocycles data .plane →ₗ[ℂ]
      cocycles rationalLevel (rationalCoefficientComponent degree data.chi) where
  toFun := globalCocycle data holomorphic degreeBound
  map_add' first second := by
    apply Subtype.ext
    apply Subtype.ext
    funext vertices
    change PolynomialEisenstein.polynomialValue data holomorphic
      (PolynomialEisenstein.sourceSection data (first + second)
        (GlobalEisensteinCocycle.realVertices vertices)) _ = _
    have sections : PolynomialEisenstein.sourceSection data (first + second)
        (GlobalEisensteinCocycle.realVertices vertices) =
      PolynomialEisenstein.sourceSection data first
        (GlobalEisensteinCocycle.realVertices vertices) +
      PolynomialEisenstein.sourceSection data second
        (GlobalEisensteinCocycle.realVertices vertices) := rfl
    rw [sections, map_add]
    rfl
  map_smul' scalar source := by
    apply Subtype.ext
    apply Subtype.ext
    funext vertices
    change PolynomialEisenstein.polynomialValue data holomorphic
      (PolynomialEisenstein.sourceSection data (scalar • source)
        (GlobalEisensteinCocycle.realVertices vertices)) _ = _
    have sections : PolynomialEisenstein.sourceSection data (scalar • source)
        (GlobalEisensteinCocycle.realVertices vertices) =
      scalar • PolynomialEisenstein.sourceSection data source
        (GlobalEisensteinCocycle.realVertices vertices) := rfl
    rw [sections, map_smul]
    rfl

def globalClass {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) (degreeBound : 4 ≤ degree)
    (source : SourceSpace.sourceCocycles data .plane) : WholeGlobalH2 degree data.chi :=
  classOf rationalLevel (rationalCoefficientComponent degree data.chi)
    (globalCocycle data holomorphic degreeBound source)

def globalClassLinear {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) (degreeBound : 4 ≤ degree) :
    SourceSpace.sourceCocycles data .plane →ₗ[ℂ] WholeGlobalH2 degree data.chi :=
  (classOf rationalLevel (rationalCoefficientComponent degree data.chi)).comp
    (globalCocycleLinear data holomorphic degreeBound)

theorem globalClassLinear_apply {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) (degreeBound : 4 ≤ degree)
    (source : SourceSpace.sourceCocycles data .plane) :
    globalClassLinear data holomorphic degreeBound source =
      globalClass data holomorphic degreeBound source := rfl

theorem globalClass_fullRestriction {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) (degreeBound : 4 ≤ degree)
    (source : SourceSpace.sourceCocycles data .plane) :
    Helpers.canonicalRestriction degree data.chi
      (globalClass data holomorphic degreeBound source) =
        fullBoundaryClass degree data.chi
          (globalBoundaryCocycle degree data.chi
            (globalCocycle data holomorphic degreeBound source)) :=
  Helpers.canonicalRestriction_realizes degree data.chi _

theorem globalClass_boundaryCoordinates {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) (degreeBound : 4 ≤ degree)
    (source : SourceSpace.sourceCocycles data .plane) :
    Helpers.canonicalCoordinates degree data.chi
      (Helpers.canonicalRestriction degree data.chi
        (globalClass data holomorphic degreeBound source)) =
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane)
        (restrictionCocycle degree data.chi .plane
          (globalCocycle data holomorphic degreeBound source)),
       classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .line)
        (restrictionCocycle degree data.chi .line
          (globalCocycle data holomorphic degreeBound source))) := by
  rw [globalClass_fullRestriction, Helpers.canonicalCoordinates_realizes]
  rfl



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.EndpointEisensteinCocycle
