module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.EndpointStandardValue
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.PolynomialNaturality
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.PolynomialStandard

@[expose] public section


/-!
# Polynomial-valued standard values at the cohomological point (convergent)

The polynomial-valued standard operator of a polynomial-valued induced section and the standard cocycle `sourceValue` of a plane source cocycle.

Re-port of `TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointPolynomialStandard` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
`PlaneEisensteinConvergent`; declarations that do not depend on the continuation hypothesis are
not copied (the original ones are used).  Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.EndpointPolynomialStandard

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialEisenstein
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialNaturality


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialEisenstein TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialNaturality
def polynomialValue {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data) :
    polynomialSections data →ₗ[ℂ] (AdelicGL → HomogeneousPoly degree) where
  toFun sectionValue argument := FlatExtensions.assemblePolynomial degree
    (fun monomial =>
      (EndpointStandardValue.sectionStandard data large holomorphic
        (coefficientSection data monomial sectionValue)).val argument)
  map_add' first second := by
    funext argument
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    simp only [Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      FlatExtensions.assemblePolynomial_coeff, map_add, Submodule.coe_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' scalar sectionValue := by
    funext argument
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    simp only [Submodule.coe_smul, MvPolynomial.coeff_smul,
      FlatExtensions.assemblePolynomial_coeff, map_smul, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp

theorem polynomialValue_coeff {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : PolynomialEisenstein.polynomialSections data)
    (monomial : Fin 3 →₀ ℕ) (argument : AdelicGL) :
    (polynomialValue data large holomorphic sectionValue argument).val.coeff monomial =
      (EndpointStandardValue.sectionStandard data large holomorphic
        (PolynomialEisenstein.coefficientSection data monomial sectionValue)).val argument := by
  change (FlatExtensions.assemblePolynomial degree _).val.coeff monomial = _
  rw [FlatExtensions.assemblePolynomial_coeff]
  split_ifs with homogeneous
  · rfl
  · have zeroCoefficient : PolynomialEisenstein.coefficientSection data monomial sectionValue = 0 := by
      apply Subtype.ext
      funext argument
      exact (sectionValue.val argument).property.coeff_eq_zero homogeneous
    rw [zeroCoefficient, map_zero]
    rfl

theorem polynomialValue_tensor {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data) (polynomial : HomogeneousPoly degree)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    polynomialValue data large holomorphic (tensorSection data polynomial sectionValue)
      argument = (EndpointStandardValue.sectionStandard data large holomorphic sectionValue).val argument • polynomial := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  rw [polynomialValue_coeff, coefficient_tensor, map_smul]
  simp [mul_comm]

theorem polynomialValue_sum_basis {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : PolynomialEisenstein.polynomialSections data) (argument : AdelicGL) :
    (∑ monomial ∈ FlatExtensions.degreeMonomials degree,
      (EndpointStandardValue.sectionStandard data large holomorphic
        (PolynomialEisenstein.coefficientSection data monomial sectionValue)).val argument •
          basisVector degree monomial) =
        polynomialValue data large holomorphic sectionValue argument := by
  have equality := congrArg (fun value =>
    polynomialValue data large holomorphic value argument) (section_sum_basis data sectionValue)
  simpa only [map_sum, Finset.sum_apply, polynomialValue_tensor] using equality

theorem polynomialValue_coefficientMap {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (operator : Module.End ℂ (HomogeneousPoly degree))
    (sectionValue : PolynomialEisenstein.polynomialSections data) (argument : AdelicGL) :
    polynomialValue data large holomorphic (coefficientMap data operator sectionValue)
      argument = operator (polynomialValue data large holomorphic sectionValue argument) := by
  have equality := congrArg operator (polynomialValue_sum_basis data large holomorphic sectionValue argument)
  simpa only [coefficientMap, map_sum, Finset.sum_apply, polynomialValue_tensor, map_smul] using equality

theorem polynomialValue_source_closed {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane)
    (vertices : Fin 4 → RealGL3) (argument : AdelicGL) :
    polynomialValue data large holomorphic
        (sourceSection data source ![vertices 1, vertices 2, vertices 3]) argument -
      polynomialValue data large holomorphic
        (sourceSection data source ![vertices 0, vertices 2, vertices 3]) argument +
      polynomialValue data large holomorphic
        (sourceSection data source ![vertices 0, vertices 1, vertices 3]) argument -
      polynomialValue data large holomorphic
        (sourceSection data source ![vertices 0, vertices 1, vertices 2]) argument = 0 := by
  have closed := congrArg (polynomialValue data large holomorphic)
    (sourceSection_closed data source vertices)
  change polynomialValue data large holomorphic
      (sourceSection data source ![vertices 1, vertices 2, vertices 3] -
          sourceSection data source ![vertices 0, vertices 2, vertices 3] +
        sourceSection data source ![vertices 0, vertices 1, vertices 3] -
          sourceSection data source ![vertices 0, vertices 1, vertices 2]) =
      polynomialValue data large holomorphic 0 at closed
  rw [LinearMap.map_sub (polynomialValue data large holomorphic)
      (sourceSection data source ![vertices 1, vertices 2, vertices 3] -
          sourceSection data source ![vertices 0, vertices 2, vertices 3] +
        sourceSection data source ![vertices 0, vertices 1, vertices 3])
      (sourceSection data source ![vertices 0, vertices 1, vertices 2]),
    LinearMap.map_add (polynomialValue data large holomorphic)
      (sourceSection data source ![vertices 1, vertices 2, vertices 3] -
        sourceSection data source ![vertices 0, vertices 2, vertices 3])
      (sourceSection data source ![vertices 0, vertices 1, vertices 3]),
    LinearMap.map_sub (polynomialValue data large holomorphic)
      (sourceSection data source ![vertices 1, vertices 2, vertices 3])
      (sourceSection data source ![vertices 0, vertices 2, vertices 3]),
    LinearMap.map_zero (polynomialValue data large holomorphic)] at closed
  simpa only [map_sub, map_add, map_zero, Pi.sub_apply, Pi.add_apply, Pi.zero_apply] using
    congrFun closed argument

theorem polynomialValue_induced {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data) (sectionValue : polynomialSections data)
    (monomial : Fin 3 →₀ ℕ) :
    IsInduced data .line cohomologicalPoint (fun argument =>
      (polynomialValue data large holomorphic sectionValue argument).val.coeff monomial) := by
  simp only [polynomialValue_coeff]
  exact (EndpointStandardValue.sectionStandard data large holomorphic (coefficientSection data monomial sectionValue)).property

theorem polynomialValue_right_real {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data) (sectionValue : polynomialSections data)
    (real : RealGL3) (argument : AdelicGL) :
    polynomialValue data large holomorphic (rightReal data real sectionValue) argument =
      polynomialValue data large holomorphic sectionValue (argument * atInfinity real) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  rw [polynomialValue_coeff, polynomialValue_coeff, coefficient_rightReal,
    EndpointStandardValue.sectionStandard_right_real]
  rfl

def sourceValue {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data) (source : SourceSpace.sourceCocycles data .plane) :
    (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree :=
  fun vertices => polynomialValue data large holomorphic (sourceSection data source vertices)

theorem sourceValue_real_covariant {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data) (source : SourceSpace.sourceCocycles data .plane)
    (real : RealGL3) (vertices : Fin 3 → RealGL3) (argument : AdelicGL) :
    sourceValue data large holomorphic source (fun index => real * vertices index) argument =
      realCoefficientComponent degree data.chi real
        (sourceValue data large holomorphic source vertices (argument * atInfinity real)) := by
  unfold sourceValue
  rw [sourceSection_transformed, polynomialValue_coefficientMap, polynomialValue_right_real]

theorem sourceValue_closed {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinConvergent data) (source : SourceSpace.sourceCocycles data .plane)
    (vertices : Fin 4 → RealGL3) (argument : AdelicGL) :
    sourceValue data large holomorphic source ![vertices 1, vertices 2, vertices 3] argument -
      sourceValue data large holomorphic source ![vertices 0, vertices 2, vertices 3] argument +
      sourceValue data large holomorphic source ![vertices 0, vertices 1, vertices 3] argument -
      sourceValue data large holomorphic source ![vertices 0, vertices 1, vertices 2] argument = 0 :=
  polynomialValue_source_closed data large holomorphic source vertices argument



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.EndpointPolynomialStandard
