module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PolynomialEisenstein

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialFamilies

def polynomialFlatExtension {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    PolynomialEisenstein.polynomialSections data →ₗ[ℂ]
      (ℂ → AdelicGL → HomogeneousPoly degree) where
  toFun sectionValue parameter argument := FlatExtensions.assemblePolynomial degree
    (fun monomial =>
      (SectionSpace.linearFlatExtension data holomorphic
        (PolynomialEisenstein.coefficientSection data monomial sectionValue)).val
          parameter argument)
  map_add' first second := by
    funext parameter argument
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    simp only [Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      FlatExtensions.assemblePolynomial_coeff, map_add, Submodule.coe_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' scalar sectionValue := by
    funext parameter argument
    apply Subtype.ext
    apply MvPolynomial.ext
    intro monomial
    simp only [Submodule.coe_smul, MvPolynomial.coeff_smul,
      FlatExtensions.assemblePolynomial_coeff, map_smul, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp

theorem polynomialFlatExtension_flat {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : PolynomialEisenstein.polynomialSections data)
    (monomial : Fin 3 →₀ ℕ) :
    IsFlatSection data (fun parameter argument => (polynomialFlatExtension data holomorphic sectionValue parameter argument).val.coeff monomial) := by
  change IsFlatSection data (fun parameter argument => (FlatExtensions.assemblePolynomial degree _).val.coeff monomial)
  by_cases homogeneous : Finsupp.degree monomial = degree
  · have flat : IsFlatSection data
        (SectionSpace.linearFlatExtension data holomorphic
          (PolynomialEisenstein.coefficientSection data monomial sectionValue)).val :=
      (SectionSpace.linearFlatExtension data holomorphic
        (PolynomialEisenstein.coefficientSection data monomial sectionValue)).property
    simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_left homogeneous] using flat
  · simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_right homogeneous] using
      FlatExtensions.flat_zero data

theorem polynomialFlatExtension_endpoint {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : PolynomialEisenstein.polynomialSections data) :
    polynomialFlatExtension data holomorphic sectionValue cohomologicalPoint =
      sectionValue.val := by
  funext argument
  change FlatExtensions.assemblePolynomial degree _ = sectionValue.val argument
  simpa only [SectionSpace.linearFlatExtension_endpoint,
    PolynomialEisenstein.coefficientSection, LinearMap.coe_mk, AddHom.coe_mk] using
    FlatExtensions.assemblePolynomial_original degree (sectionValue.val argument)

def polynomialContinuation {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : PolynomialEisenstein.polynomialSections data) :
    ℂ → AdelicGL → HomogeneousPoly degree :=
  fun parameter argument => FlatExtensions.assemblePolynomial degree
    (fun monomial => EisensteinValue.chosenContinuation data holomorphic
      (SectionSpace.linearFlatExtension data holomorphic
        (PolynomialEisenstein.coefficientSection data monomial sectionValue))
      parameter argument)

theorem polynomialContinuation_continues {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : PolynomialEisenstein.polynomialSections data)
    (monomial : Fin 3 →₀ ℕ) :
    IsEisensteinContinuation
      (fun parameter argument => (polynomialFlatExtension data holomorphic sectionValue parameter argument).val.coeff monomial)
      (fun parameter argument => (polynomialContinuation data holomorphic sectionValue parameter argument).val.coeff monomial) := by
  change IsEisensteinContinuation
    (fun parameter argument => (FlatExtensions.assemblePolynomial degree _).val.coeff monomial)
    (fun parameter argument => (FlatExtensions.assemblePolynomial degree _).val.coeff monomial)
  by_cases homogeneous : Finsupp.degree monomial = degree
  · simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_left homogeneous] using
      (EisensteinValue.chosenContinuation_spec data holomorphic
        (SectionSpace.linearFlatExtension data holomorphic
          (PolynomialEisenstein.coefficientSection data monomial sectionValue))).1
  · simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_right homogeneous] using
      FlatExtensions.eisensteinContinuation_zero

theorem polynomialContinuation_regular {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : PolynomialEisenstein.polynomialSections data)
    (argument : AdelicGL) (monomial : Fin 3 →₀ ℕ) :
    AnalyticAt ℂ (fun parameter => (polynomialContinuation data holomorphic sectionValue parameter argument).val.coeff monomial)
      cohomologicalPoint := by
  change AnalyticAt ℂ (fun parameter => (FlatExtensions.assemblePolynomial degree _).val.coeff monomial) cohomologicalPoint
  by_cases homogeneous : Finsupp.degree monomial = degree
  · simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_left homogeneous] using
      (EisensteinValue.chosenContinuation_spec data holomorphic
        (SectionSpace.linearFlatExtension data holomorphic
          (PolynomialEisenstein.coefficientSection data monomial sectionValue))).2 argument
  · simpa only [FlatExtensions.assemblePolynomial_coeff, ite_eq_right homogeneous] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) cohomologicalPoint)

theorem polynomialContinuation_endpoint {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : PolynomialEisenstein.polynomialSections data) :
    polynomialContinuation data holomorphic sectionValue cohomologicalPoint =
      PolynomialEisenstein.polynomialValue data holomorphic sectionValue := rfl

def sourceFlatExtension {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (source : SourceSpace.sourceCocycles data .plane) :
    ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree :=
  fun parameter vertices => polynomialFlatExtension data holomorphic
    (PolynomialEisenstein.sourceSection data source vertices) parameter

theorem sourceFlatExtension_endpoint {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (source : SourceSpace.sourceCocycles data .plane) :
    sourceFlatExtension data holomorphic source cohomologicalPoint = source.val := by
  funext vertices
  exact polynomialFlatExtension_endpoint data holomorphic
    (PolynomialEisenstein.sourceSection data source vertices)

theorem sourceFlatExtension_closed {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (source : SourceSpace.sourceCocycles data .plane) (parameter : ℂ)
    (vertices : Fin 4 → RealGL3) (argument : AdelicGL) :
    sourceFlatExtension data holomorphic source parameter
        ![vertices 1, vertices 2, vertices 3] argument -
      sourceFlatExtension data holomorphic source parameter
        ![vertices 0, vertices 2, vertices 3] argument +
      sourceFlatExtension data holomorphic source parameter
        ![vertices 0, vertices 1, vertices 3] argument -
      sourceFlatExtension data holomorphic source parameter
        ![vertices 0, vertices 1, vertices 2] argument = 0 := by
  have closed := congrArg (polynomialFlatExtension data holomorphic)
    (PolynomialEisenstein.sourceSection_closed data source vertices)
  change polynomialFlatExtension data holomorphic
      (PolynomialEisenstein.sourceSection data source ![vertices 1, vertices 2, vertices 3] -
          PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 2, vertices 3] +
        PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 1, vertices 3] -
          PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 1, vertices 2]) =
      polynomialFlatExtension data holomorphic 0 at closed
  rw [LinearMap.map_sub (polynomialFlatExtension data holomorphic)
      (PolynomialEisenstein.sourceSection data source ![vertices 1, vertices 2, vertices 3] -
          PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 2, vertices 3] +
        PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 1, vertices 3])
      (PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 1, vertices 2]),
    LinearMap.map_add (polynomialFlatExtension data holomorphic)
      (PolynomialEisenstein.sourceSection data source ![vertices 1, vertices 2, vertices 3] -
        PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 2, vertices 3])
      (PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 1, vertices 3]),
    LinearMap.map_sub (polynomialFlatExtension data holomorphic)
      (PolynomialEisenstein.sourceSection data source ![vertices 1, vertices 2, vertices 3])
      (PolynomialEisenstein.sourceSection data source ![vertices 0, vertices 2, vertices 3]),
    LinearMap.map_zero (polynomialFlatExtension data holomorphic)] at closed
  simpa only [sourceFlatExtension, Pi.sub_apply, Pi.add_apply, Pi.zero_apply] using
    congrFun (congrFun closed parameter) argument

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialFamilies
