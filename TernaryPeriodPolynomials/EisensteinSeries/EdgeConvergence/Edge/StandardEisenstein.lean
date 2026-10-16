module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.EisensteinCocycle

@[expose] public section


/-!
# The global Eisenstein cocycle at `n = 3`: interface

`EndpointEisensteinCocycle.globalCocycle` needs `4 ≤ n` in exactly one place: the right real
equivariance `E(R(h) f) = R(h) E(f)` of the Eisenstein operator for non-compact `h`
(`sectionEisensteinValue_right_real`, via the convergent coset sum at `s₀`). Everything else in
`EndpointEisensteinCocycle` (linearity, restriction to the boundary, boundary coordinates) is formal.
`EdgeEisensteinOperator` isolates that equivariance, and `edgeGlobalCocycle` / `edgeGlobalClass` are the
global Eisenstein cocycle and class for any `n` given it, exactly as in `EndpointEisensteinCocycle`.
The equivariance is proved by the same two-variable argument as the standard operator
(`RightEquivariance`), with the coset sum `∑_γ ρ_h(γ y)^z F_s(γ y h)` in place of the radical integral.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence.EdgeStandardEisenstein

/-- Right real equivariance of the Eisenstein operator `sectionEisensteinValue`. -/
structure EdgeEisensteinOperator {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) : Prop where
  right_real : ∀ (real : RealGL3)
      (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
      (argument : AdelicGL),
    (SectionSpace.sectionEisensteinValue data holomorphic
      (RealTranslations.sectionRightReal data .plane cohomologicalPoint real sectionValue)).val
      argument =
        (SectionSpace.sectionEisensteinValue data holomorphic sectionValue).val
          (argument * atInfinity real)

/-- For `4 ≤ n` the Eisenstein sum converges at `s₀` and the operator satisfies the interface. -/
theorem edgeEisensteinOperator_of_large {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (degreeBound : 4 ≤ degree) :
    EdgeEisensteinOperator data holomorphic where
  right_real real sectionValue argument :=
    EndpointEisensteinCocycle.sectionEisensteinValue_right_real data holomorphic degreeBound
      sectionValue real argument

variable {degree : ℕ} (data : InducingData degree)
  (holomorphic : PlaneEisensteinHolomorphic data)

theorem polynomialValue_right_real (edge : EdgeEisensteinOperator data holomorphic)
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
  exact edge.right_real real _ argument

theorem sourceValue_real_covariant (edge : EdgeEisensteinOperator data holomorphic)
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
    polynomialValue_right_real data holomorphic edge]

/-- The global Eisenstein cocycle of a plane source cocycle. -/
def edgeGlobalCocycle (edge : EdgeEisensteinOperator data holomorphic)
    (source : SourceSpace.sourceCocycles data .plane) :
    cocycles rationalLevel (rationalCoefficientComponent degree data.chi) :=
  GlobalEisensteinCocycle.globalCocycle_of_realCovariance data holomorphic source
    (sourceValue_real_covariant data holomorphic edge source)

theorem edgeGlobalCocycle_realizes (edge : EdgeEisensteinOperator data holomorphic)
    (source : SourceSpace.sourceCocycles data .plane) (vertices : Fin 3 → RationalGL3) :
    (edgeGlobalCocycle data holomorphic edge source).val.val vertices =
      GlobalEisensteinCocycle.evaluatedSourceValue data holomorphic source vertices := rfl

/-- The global Eisenstein class of a plane source cocycle. -/
def edgeGlobalClass (edge : EdgeEisensteinOperator data holomorphic)
    (source : SourceSpace.sourceCocycles data .plane) : WholeGlobalH2 degree data.chi :=
  classOf rationalLevel (rationalCoefficientComponent degree data.chi)
    (edgeGlobalCocycle data holomorphic edge source)

theorem edgeGlobalClass_fullRestriction (edge : EdgeEisensteinOperator data holomorphic)
    (source : SourceSpace.sourceCocycles data .plane) :
    Helpers.canonicalRestriction degree data.chi (edgeGlobalClass data holomorphic edge source) =
      fullBoundaryClass degree data.chi
        (globalBoundaryCocycle degree data.chi (edgeGlobalCocycle data holomorphic edge source)) :=
  Helpers.canonicalRestriction_realizes degree data.chi _

theorem edgeGlobalClass_boundaryCoordinates (edge : EdgeEisensteinOperator data holomorphic)
    (source : SourceSpace.sourceCocycles data .plane) :
    Helpers.canonicalCoordinates degree data.chi
      (Helpers.canonicalRestriction degree data.chi
        (edgeGlobalClass data holomorphic edge source)) =
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .plane)
        (restrictionCocycle degree data.chi .plane
          (edgeGlobalCocycle data holomorphic edge source)),
       classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent degree data.chi) .line)
        (restrictionCocycle degree data.chi .line
          (edgeGlobalCocycle data holomorphic edge source))) := by
  rw [edgeGlobalClass_fullRestriction, Helpers.canonicalCoordinates_realizes]
  rfl

end TernaryPeriodPolynomials.EdgeConvergence.EdgeStandardEisenstein
