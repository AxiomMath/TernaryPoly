module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SectionSpace

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialEisenstein

def polynomialSections {degree : ℕ} (data : InducingData degree) :
    Submodule ℂ (AdelicGL → HomogeneousPoly degree) where
  carrier := {function | ∀ monomial,
    IsInduced data .plane cohomologicalPoint
      (fun argument => (function argument).val.coeff monomial)}
  zero_mem' := by
    intro monomial
    simpa only [Pi.zero_apply, Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] using
      FlatExtensions.induced_zero data .plane cohomologicalPoint
  add_mem' {first second} firstInduced secondInduced := by
    intro monomial
    simpa only [Pi.add_apply, Submodule.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using
      LinearFamilies.induced_add data .plane cohomologicalPoint _ _
        (firstInduced monomial) (secondInduced monomial)
  smul_mem' scalar function induced := by
    intro monomial
    simpa only [Pi.smul_apply, Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul] using
      LinearFamilies.induced_smul data .plane cohomologicalPoint scalar _ (induced monomial)

def coefficientSection {degree : ℕ} (data : InducingData degree)
    (monomial : Fin 3 →₀ ℕ) :
    polynomialSections data →ₗ[ℂ]
      SectionSpace.inducedSections data .plane cohomologicalPoint where
  toFun sectionValue := ⟨fun argument =>
    (sectionValue.val argument).val.coeff monomial,
    sectionValue.property monomial⟩
  map_add' first second := by
    apply Subtype.ext
    funext argument
    exact rfl
  map_smul' scalar sectionValue := by
    apply Subtype.ext
    funext argument
    exact MvPolynomial.coeff_smul monomial scalar _

def polynomialValue {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) :
    polynomialSections data →ₗ[ℂ] (AdelicGL → HomogeneousPoly degree) where
  toFun sectionValue argument := FlatExtensions.assemblePolynomial degree
    (fun monomial =>
      (SectionSpace.sectionEisensteinValue data holomorphic
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

theorem polynomialValue_rational {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (sectionValue : polynomialSections data)
    (element : RationalGL3) (argument : AdelicGL) :
    polynomialValue data holomorphic sectionValue (rationalGroup element * argument) =
      polynomialValue data holomorphic sectionValue argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  change (FlatExtensions.assemblePolynomial degree _).val.coeff monomial =
      (FlatExtensions.assemblePolynomial degree _).val.coeff monomial
  rw [FlatExtensions.assemblePolynomial_coeff, FlatExtensions.assemblePolynomial_coeff]
  split_ifs
  · exact (SectionSpace.sectionEisensteinValue data holomorphic
      (coefficientSection data monomial sectionValue)).property.1 element argument
  · rfl

theorem polynomialValue_finite {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (sectionValue : polynomialSections data)
    (levelElement : finiteLevel) (argument : AdelicGL) :
    polynomialValue data holomorphic sectionValue (argument * atFinite levelElement.val) =
      polynomialValue data holomorphic sectionValue argument := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  change (FlatExtensions.assemblePolynomial degree _).val.coeff monomial =
      (FlatExtensions.assemblePolynomial degree _).val.coeff monomial
  rw [FlatExtensions.assemblePolynomial_coeff, FlatExtensions.assemblePolynomial_coeff]
  split_ifs
  · exact (SectionSpace.sectionEisensteinValue data holomorphic
      (coefficientSection data monomial sectionValue)).property.2 levelElement argument
  · rfl

def sourceSection {degree : ℕ} (data : InducingData degree)
    (source : SourceSpace.sourceCocycles data .plane) (vertices : Fin 3 → RealGL3) :
    polynomialSections data :=
  ⟨source.val vertices, source.property.1 vertices⟩

theorem sourceSection_closed {degree : ℕ} (data : InducingData degree)
    (source : SourceSpace.sourceCocycles data .plane) (vertices : Fin 4 → RealGL3) :
    sourceSection data source ![vertices 1, vertices 2, vertices 3] -
        sourceSection data source ![vertices 0, vertices 2, vertices 3] +
      sourceSection data source ![vertices 0, vertices 1, vertices 3] -
        sourceSection data source ![vertices 0, vertices 1, vertices 2] = 0 := by
  apply Subtype.ext
  funext argument
  exact source.property.2.2.2 vertices argument

theorem polynomialValue_source_closed {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (source : SourceSpace.sourceCocycles data .plane)
    (vertices : Fin 4 → RealGL3) (argument : AdelicGL) :
    polynomialValue data holomorphic
        (sourceSection data source ![vertices 1, vertices 2, vertices 3]) argument -
      polynomialValue data holomorphic
        (sourceSection data source ![vertices 0, vertices 2, vertices 3]) argument +
      polynomialValue data holomorphic
        (sourceSection data source ![vertices 0, vertices 1, vertices 3]) argument -
      polynomialValue data holomorphic
        (sourceSection data source ![vertices 0, vertices 1, vertices 2]) argument = 0 := by
  have closed := congrArg (polynomialValue data holomorphic)
    (sourceSection_closed data source vertices)
  change polynomialValue data holomorphic
      (sourceSection data source ![vertices 1, vertices 2, vertices 3] -
          sourceSection data source ![vertices 0, vertices 2, vertices 3] +
        sourceSection data source ![vertices 0, vertices 1, vertices 3] -
          sourceSection data source ![vertices 0, vertices 1, vertices 2]) =
      polynomialValue data holomorphic 0 at closed
  rw [LinearMap.map_sub (polynomialValue data holomorphic)
      (sourceSection data source ![vertices 1, vertices 2, vertices 3] -
          sourceSection data source ![vertices 0, vertices 2, vertices 3] +
        sourceSection data source ![vertices 0, vertices 1, vertices 3])
      (sourceSection data source ![vertices 0, vertices 1, vertices 2]),
    LinearMap.map_add (polynomialValue data holomorphic)
      (sourceSection data source ![vertices 1, vertices 2, vertices 3] -
        sourceSection data source ![vertices 0, vertices 2, vertices 3])
      (sourceSection data source ![vertices 0, vertices 1, vertices 3]),
    LinearMap.map_sub (polynomialValue data holomorphic)
      (sourceSection data source ![vertices 1, vertices 2, vertices 3])
      (sourceSection data source ![vertices 0, vertices 2, vertices 3]),
    LinearMap.map_zero (polynomialValue data holomorphic)] at closed
  simpa only [map_sub, map_add, map_zero, Pi.sub_apply, Pi.add_apply, Pi.zero_apply] using
    congrFun closed argument

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialEisenstein
