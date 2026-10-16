module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.PolynomialEisenstein
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PolynomialNaturality

@[expose] public section


/-!
# Naturality of the polynomial-valued Eisenstein value (convergent)

Coefficients, tensor sections, coefficient maps and compact equivariance of the polynomial-valued Eisenstein value.

Re-port of `TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialNaturality` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
`PlaneEisensteinConvergent`; declarations that do not depend on the continuation hypothesis are
not copied (the original ones are used).  Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.PolynomialNaturality

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialNaturality


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped BigOperators
theorem polynomialValue_coeff {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
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
    (holomorphic : PlaneEisensteinConvergent data) (polynomial : HomogeneousPoly degree)
    (sectionValue : SectionSpace.inducedSections data .plane cohomologicalPoint)
    (argument : AdelicGL) :
    PolynomialEisenstein.polynomialValue data holomorphic (tensorSection data polynomial sectionValue)
      argument = (SectionSpace.sectionEisensteinValue data holomorphic sectionValue).val argument • polynomial := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  rw [polynomialValue_coeff, coefficient_tensor, map_smul]
  simp [mul_comm]

theorem polynomialValue_sum_basis {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
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
    (holomorphic : PlaneEisensteinConvergent data)
    (operator : Module.End ℂ (HomogeneousPoly degree))
    (sectionValue : PolynomialEisenstein.polynomialSections data) (argument : AdelicGL) :
    PolynomialEisenstein.polynomialValue data holomorphic (coefficientMap data operator sectionValue)
      argument = operator (PolynomialEisenstein.polynomialValue data holomorphic sectionValue argument) := by
  have equality := congrArg operator (polynomialValue_sum_basis data holomorphic sectionValue argument)
  simpa only [coefficientMap, map_sum, Finset.sum_apply, polynomialValue_tensor, map_smul] using equality

theorem polynomialValue_compact {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : PolynomialEisenstein.polynomialSections data)
    (real : RealGL3) (orthogonal : real.val.transpose * real.val = 1) (argument : AdelicGL) :
    PolynomialEisenstein.polynomialValue data holomorphic (rightReal data real sectionValue) argument =
      PolynomialEisenstein.polynomialValue data holomorphic sectionValue (argument * atInfinity real) := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  rw [polynomialValue_coeff, polynomialValue_coeff, coefficient_rightReal]
  exact CompactEquivariance.sectionEisensteinValue_compact data holomorphic _ real orthogonal argument

theorem sourceEisenstein_compact {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
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



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.PolynomialNaturality
