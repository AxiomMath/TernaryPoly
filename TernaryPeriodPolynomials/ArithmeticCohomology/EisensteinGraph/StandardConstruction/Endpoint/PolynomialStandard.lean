module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Endpoint.StandardValue
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PolynomialNaturality
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PolynomialFamilies

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialEisenstein TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialNaturality

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointPolynomialStandard

def polynomialValue {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
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
    (holomorphic : PlaneEisensteinHolomorphic data)
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
    (holomorphic : PlaneEisensteinHolomorphic data) (polynomial : HomogeneousPoly degree)
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
    (holomorphic : PlaneEisensteinHolomorphic data)
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
    (holomorphic : PlaneEisensteinHolomorphic data)
    (operator : Module.End ℂ (HomogeneousPoly degree))
    (sectionValue : PolynomialEisenstein.polynomialSections data) (argument : AdelicGL) :
    polynomialValue data large holomorphic (coefficientMap data operator sectionValue)
      argument = operator (polynomialValue data large holomorphic sectionValue argument) := by
  have equality := congrArg operator (polynomialValue_sum_basis data large holomorphic sectionValue argument)
  simpa only [coefficientMap, map_sum, Finset.sum_apply, polynomialValue_tensor, map_smul] using equality


theorem polynomialValue_source_closed {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
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
    (holomorphic : PlaneEisensteinHolomorphic data) (sectionValue : polynomialSections data)
    (monomial : Fin 3 →₀ ℕ) :
    IsInduced data .line cohomologicalPoint (fun argument =>
      (polynomialValue data large holomorphic sectionValue argument).val.coeff monomial) := by
  simp only [polynomialValue_coeff]
  exact (EndpointStandardValue.sectionStandard data large holomorphic (coefficientSection data monomial sectionValue)).property

theorem polynomialValue_right_real {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (sectionValue : polynomialSections data)
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
    (holomorphic : PlaneEisensteinHolomorphic data) (source : SourceSpace.sourceCocycles data .plane) :
    (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree :=
  fun vertices => polynomialValue data large holomorphic (sourceSection data source vertices)

theorem sourceValue_real_covariant {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (source : SourceSpace.sourceCocycles data .plane)
    (real : RealGL3) (vertices : Fin 3 → RealGL3) (argument : AdelicGL) :
    sourceValue data large holomorphic source (fun index => real * vertices index) argument =
      realCoefficientComponent degree data.chi real
        (sourceValue data large holomorphic source vertices (argument * atInfinity real)) := by
  unfold sourceValue
  rw [sourceSection_transformed, polynomialValue_coefficientMap, polynomialValue_right_real]

theorem sourceValue_closed {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (source : SourceSpace.sourceCocycles data .plane)
    (vertices : Fin 4 → RealGL3) (argument : AdelicGL) :
    sourceValue data large holomorphic source ![vertices 1, vertices 2, vertices 3] argument -
      sourceValue data large holomorphic source ![vertices 0, vertices 2, vertices 3] argument +
      sourceValue data large holomorphic source ![vertices 0, vertices 1, vertices 3] argument -
      sourceValue data large holomorphic source ![vertices 0, vertices 1, vertices 2] argument = 0 :=
  polynomialValue_source_closed data large holomorphic source vertices argument

def polynomialContinuation {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (sectionValue : polynomialSections data) :
    ℂ → AdelicGL → HomogeneousPoly degree :=
  fun parameter argument => FlatExtensions.assemblePolynomial degree (fun monomial =>
    StandardValue.chosenContinuation data (EndpointStandardValue.regularFamily data large
      (SectionSpace.linearFlatExtension data holomorphic (coefficientSection data monomial sectionValue)))
      parameter argument)

theorem polynomialContinuation_continues {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (sectionValue : polynomialSections data)
    (monomial : Fin 3 →₀ ℕ) :
    IsStandardContinuation
      (fun parameter argument => (PolynomialFamilies.polynomialFlatExtension data holomorphic sectionValue parameter argument).val.coeff monomial)
      (fun parameter argument => (polynomialContinuation data large holomorphic sectionValue parameter argument).val.coeff monomial) := by
  change IsStandardContinuation
    (fun parameter argument => (FlatExtensions.assemblePolynomial degree _).val.coeff monomial)
    (fun parameter argument => (FlatExtensions.assemblePolynomial degree _).val.coeff monomial)
  by_cases homogeneous : Finsupp.degree monomial = degree
  · simp only [FlatExtensions.assemblePolynomial_coeff, ite_eq_left homogeneous]
    exact (StandardValue.chosenContinuation_spec data (EndpointStandardValue.regularFamily data large
        (SectionSpace.linearFlatExtension data holomorphic (coefficientSection data monomial sectionValue)))).1
  · simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_right homogeneous] using
      FlatExtensions.standardContinuation_zero

theorem polynomialContinuation_regular {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (sectionValue : polynomialSections data)
    (argument : AdelicGL) (monomial : Fin 3 →₀ ℕ) :
    AnalyticAt ℂ (fun parameter => (polynomialContinuation data large holomorphic sectionValue parameter argument).val.coeff monomial) cohomologicalPoint := by
  change AnalyticAt ℂ (fun parameter => (FlatExtensions.assemblePolynomial degree _).val.coeff monomial) cohomologicalPoint
  by_cases homogeneous : Finsupp.degree monomial = degree
  · simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_left homogeneous] using
      (StandardValue.chosenContinuation_spec data (EndpointStandardValue.regularFamily data large
        (SectionSpace.linearFlatExtension data holomorphic (coefficientSection data monomial sectionValue)))).2 argument
  · simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_right homogeneous] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) cohomologicalPoint)

theorem polynomialContinuation_endpoint {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (sectionValue : polynomialSections data) :
    polynomialContinuation data large holomorphic sectionValue cohomologicalPoint =
      polynomialValue data large holomorphic sectionValue := rfl

def sourceContinuation {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (source : SourceSpace.sourceCocycles data .plane) :
    ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree :=
  fun parameter vertices => polynomialContinuation data large holomorphic
    (sourceSection data source vertices) parameter

theorem sourceContinuation_endpoint {degree : ℕ} (data : InducingData degree) (large : 4 ≤ degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (source : SourceSpace.sourceCocycles data .plane) :
    sourceContinuation data large holomorphic source cohomologicalPoint = sourceValue data large holomorphic source := rfl

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.EndpointPolynomialStandard
