module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.PolynomialEisenstein
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.PolynomialFamilies

@[expose] public section


/-!
# Flat extensions of polynomial sections (convergent)

Flat extension families of polynomial-valued induced sections and of plane source cocycles, from the flat extensions of the scalar sections.

Re-port of `TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialFamilies` (from the Sol reference implementation, ported by AxiomCode) with `PlaneEisensteinHolomorphic` replaced by the continuation-free
`PlaneEisensteinConvergent`; declarations that do not depend on the continuation hypothesis are
not copied (the original ones are used).  Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.PolynomialFamilies

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.PolynomialFamilies


open GeneralEisenstein GeneralEisenstein.Adelic
def polynomialFlatExtension {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data) :
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
    (holomorphic : PlaneEisensteinConvergent data)
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
    (holomorphic : PlaneEisensteinConvergent data)
    (sectionValue : PolynomialEisenstein.polynomialSections data) :
    polynomialFlatExtension data holomorphic sectionValue cohomologicalPoint =
      sectionValue.val := by
  funext argument
  change FlatExtensions.assemblePolynomial degree _ = sectionValue.val argument
  simpa only [SectionSpace.linearFlatExtension_endpoint,
    PolynomialEisenstein.coefficientSection, LinearMap.coe_mk, AddHom.coe_mk] using
    FlatExtensions.assemblePolynomial_original degree (sectionValue.val argument)

def sourceFlatExtension {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane) :
    ℂ → (Fin 3 → RealGL3) → AdelicGL → HomogeneousPoly degree :=
  fun parameter vertices => polynomialFlatExtension data holomorphic
    (PolynomialEisenstein.sourceSection data source vertices) parameter

theorem sourceFlatExtension_endpoint {degree : ℕ} (data : InducingData degree)
    (holomorphic : PlaneEisensteinConvergent data)
    (source : SourceSpace.sourceCocycles data .plane) :
    sourceFlatExtension data holomorphic source cohomologicalPoint = source.val := by
  funext vertices
  exact polynomialFlatExtension_endpoint data holomorphic
    (PolynomialEisenstein.sourceSection data source vertices)



end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.PolynomialFamilies
