module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PolynomialEisenstein
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Compact.Equivariance

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped BigOperators

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialNaturality

def basisVector (degree : ℕ) (monomial : Fin 3 →₀ ℕ) : HomogeneousPoly degree :=
  FlatExtensions.assemblePolynomial degree (fun index => if index = monomial then 1 else 0)

theorem sum_basis (degree : ℕ) (polynomial : HomogeneousPoly degree) :
    (∑ monomial ∈ FlatExtensions.degreeMonomials degree,
      polynomial.val.coeff monomial • basisVector degree monomial) = polynomial := by
  classical
  apply Subtype.ext
  apply MvPolynomial.ext
  intro index
  simp only [Submodule.coe_sum, MvPolynomial.coeff_sum, Submodule.coe_smul,
    MvPolynomial.coeff_smul, smul_eq_mul, basisVector, FlatExtensions.assemblePolynomial_coeff]
  by_cases homogeneous : Finsupp.degree index = degree
  · simp [homogeneous, FlatExtensions.mem_degreeMonomials]
  · simp [homogeneous, polynomial.property.coeff_eq_zero homogeneous]

def tensorSection {degree : ℕ} (data : InducingData degree) (polynomial : HomogeneousPoly degree)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint) :
    PolynomialEisenstein.polynomialSections data :=
  ⟨fun argument => sectionValue.val argument • polynomial, by
    intro monomial
    simpa only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul, mul_comm] using
      LinearFamilies.induced_smul data .plane cohomologicalPoint
        (polynomial.val.coeff monomial) sectionValue.val sectionValue.property⟩

theorem coefficient_tensor {degree : ℕ} (data : InducingData degree)
    (polynomial : HomogeneousPoly degree)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (monomial : Fin 3 →₀ ℕ) :
    PolynomialEisenstein.coefficientSection data monomial (tensorSection data polynomial sectionValue) =
      polynomial.val.coeff monomial • sectionValue := by
  apply Subtype.ext
  funext argument
  simp [PolynomialEisenstein.coefficientSection, tensorSection, mul_comm]

theorem polynomialValue_coeff {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : PolynomialEisenstein.polynomialSections data)
    (monomial : Fin 3 →₀ ℕ) (argument : AdelicGL) :
    (PolynomialEisenstein.polynomialValue data holomorphic sectionValue argument).val.coeff monomial =
      (SectionSpace.sectionEisensteinValue data holomorphic
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

theorem polynomialValue_tensor {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data) (polynomial : HomogeneousPoly degree)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    PolynomialEisenstein.polynomialValue data holomorphic (tensorSection data polynomial sectionValue)
      argument = (SectionSpace.sectionEisensteinValue data holomorphic sectionValue).val argument • polynomial := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  rw [polynomialValue_coeff, coefficient_tensor, map_smul]
  simp [mul_comm]

theorem section_sum_basis {degree : ℕ} (data : InducingData degree)
    (sectionValue : PolynomialEisenstein.polynomialSections data) :
    (∑ monomial ∈ FlatExtensions.degreeMonomials degree,
      tensorSection data (basisVector degree monomial)
        (PolynomialEisenstein.coefficientSection data monomial sectionValue)) = sectionValue := by
  apply Subtype.ext
  funext argument
  simp only [Submodule.coe_sum, Finset.sum_apply]
  exact sum_basis degree (sectionValue.val argument)

def coefficientMap {degree : ℕ} (data : InducingData degree)
    (operator : Module.End ℂ (HomogeneousPoly degree))
    (sectionValue : PolynomialEisenstein.polynomialSections data) :
    PolynomialEisenstein.polynomialSections data :=
  ∑ monomial ∈ FlatExtensions.degreeMonomials degree,
    tensorSection data (operator (basisVector degree monomial))
      (PolynomialEisenstein.coefficientSection data monomial sectionValue)

theorem coefficientMap_apply {degree : ℕ} (data : InducingData degree)
    (operator : Module.End ℂ (HomogeneousPoly degree))
    (sectionValue : PolynomialEisenstein.polynomialSections data) (argument : AdelicGL) :
    (coefficientMap data operator sectionValue).val argument = operator (sectionValue.val argument) := by
  have equality := congrArg operator (sum_basis degree (sectionValue.val argument))
  simpa only [map_sum, map_smul, coefficientMap, Submodule.coe_sum, Finset.sum_apply,
    tensorSection, PolynomialEisenstein.coefficientSection, LinearMap.coe_mk, AddHom.coe_mk]
    using equality

theorem polynomialValue_sum_basis {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : PolynomialEisenstein.polynomialSections data) (argument : AdelicGL) :
    (∑ monomial ∈ FlatExtensions.degreeMonomials degree,
      (SectionSpace.sectionEisensteinValue data holomorphic
        (PolynomialEisenstein.coefficientSection data monomial sectionValue)).val argument •
          basisVector degree monomial) =
        PolynomialEisenstein.polynomialValue data holomorphic sectionValue argument := by
  have equality := congrArg (fun value =>
    PolynomialEisenstein.polynomialValue data holomorphic value argument) (section_sum_basis data sectionValue)
  simpa only [map_sum, Finset.sum_apply, polynomialValue_tensor] using equality

theorem polynomialValue_coefficientMap {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (operator : Module.End ℂ (HomogeneousPoly degree))
    (sectionValue : PolynomialEisenstein.polynomialSections data) (argument : AdelicGL) :
    PolynomialEisenstein.polynomialValue data holomorphic (coefficientMap data operator sectionValue)
      argument = operator (PolynomialEisenstein.polynomialValue data holomorphic sectionValue argument) := by
  have equality := congrArg operator (polynomialValue_sum_basis data holomorphic sectionValue argument)
  simpa only [coefficientMap, map_sum, Finset.sum_apply, polynomialValue_tensor, map_smul] using equality

def rightReal {degree : ℕ} (data : InducingData degree) (real : RealGL3)
    (sectionValue : PolynomialEisenstein.polynomialSections data) :
    PolynomialEisenstein.polynomialSections data :=
  ⟨fun argument => sectionValue.val (argument * atInfinity real), fun monomial =>
    RealTranslations.induced_right_real data .plane cohomologicalPoint _
      (sectionValue.property monomial) real⟩

theorem coefficient_rightReal {degree : ℕ} (data : InducingData degree) (real : RealGL3)
    (sectionValue : PolynomialEisenstein.polynomialSections data) (monomial : Fin 3 →₀ ℕ) :
    PolynomialEisenstein.coefficientSection data monomial (rightReal data real sectionValue) =
      RealTranslations.sectionRightReal data .plane cohomologicalPoint real
        (PolynomialEisenstein.coefficientSection data monomial sectionValue) := rfl

theorem polynomialValue_compact {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (sectionValue : PolynomialEisenstein.polynomialSections data)
    (real : RealGL3) (orthogonal : real.val.transpose * real.val = 1) (argument : AdelicGL) :
    PolynomialEisenstein.polynomialValue data holomorphic (rightReal data real sectionValue) argument =
      PolynomialEisenstein.polynomialValue data holomorphic sectionValue (argument * atInfinity real) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  rw [polynomialValue_coeff, polynomialValue_coeff, coefficient_rightReal]
  exact CompactEquivariance.sectionEisensteinValue_compact data holomorphic _ real orthogonal argument

theorem sourceSection_transformed {degree : ℕ} (data : InducingData degree)
    (source : SourceSpace.sourceCocycles data .plane) (real : RealGL3)
    (vertices : Fin 3 → RealGL3) :
    PolynomialEisenstein.sourceSection data source (fun index => real * vertices index) =
      coefficientMap data (realCoefficientComponent degree data.chi real)
        (rightReal data real (PolynomialEisenstein.sourceSection data source vertices)) := by
  apply Subtype.ext
  funext argument
  rw [coefficientMap_apply]
  exact source.property.2.2.1 real vertices argument

theorem sourceEisenstein_compact {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinHolomorphic data)
    (source : SourceSpace.sourceCocycles data .plane)
    (real : RealGL3) (orthogonal : real.val.transpose * real.val = 1)
    (vertices : Fin 3 → RealGL3) (argument : AdelicGL) :
    PolynomialEisenstein.polynomialValue data holomorphic
      (PolynomialEisenstein.sourceSection data source (fun index => real * vertices index)) argument =
        realCoefficientComponent degree data.chi real
          (PolynomialEisenstein.polynomialValue data holomorphic
            (PolynomialEisenstein.sourceSection data source vertices) (argument * atInfinity real)) := by
  rw [sourceSection_transformed, polynomialValue_coefficientMap,
    polynomialValue_compact data holomorphic _ real orthogonal argument]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialNaturality
