module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.SectionSpace
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PolynomialEisenstein

@[expose] public section


/-!
# Polynomial-valued Eisenstein values (convergent)

The polynomial-valued Eisenstein value of a polynomial-valued induced section, from the convergent scalar Eisenstein value.

Re-port of `TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialEisenstein` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
`PlaneEisensteinConvergent`; declarations that do not depend on the continuation hypothesis are
not copied (the original ones are used).  Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.PolynomialEisenstein

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialEisenstein


open GeneralEisenstein GeneralEisenstein.Adelic
def polynomialValue {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) :
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
    (holomorphic : PlaneEisensteinConvergent data) (sectionValue : polynomialSections data)
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
    (holomorphic : PlaneEisensteinConvergent data) (sectionValue : polynomialSections data)
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

theorem polynomialValue_source_closed {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
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



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.PolynomialEisenstein
