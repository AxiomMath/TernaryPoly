module

public import TernaryPeriodPolynomials.EisensteinSeries.Edge.Inputs
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.Standard
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardUniqueness
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Line.ConstantTerm

@[expose] public section


/-!
# The line source cocycle of a related pair is the line constant term of `E`

If a plane source cocycle `c` is related to a line source cocycle `line`
(`StandardRelation.Related`: `line` is the value at `s₀` of the standard continuation of the flat
family of `c`), then `line` is the vertexwise value at `s₀` of the holomorphic standard continuation,
`EdgeStandard.edgeSourceValue` (uniqueness of flat families and of continuation germs). Its
coefficients are the standard values `HolomorphicStandardValue.sectionStandard` of coefficient
sections, which are the constant terms along the line radical of the Eisenstein values in every
degree (Sol's `sectionStandard_constantTerm`). No standard operator and no degree bound is needed.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein

open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence

variable {n : ℕ}

/-- The line cocycle of a related pair is the holomorphic standard value of the plane cocycle. -/
theorem related_line_eq (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (plane : SourceSpace.sourceCocycles D .plane) (line : SourceSpace.sourceCocycles D .line)
    (related : StandardRelation.Related D plane line) :
    line.val = EdgeStandard.edgeSourceValue D hol plane := by
  obtain ⟨family, continuation, flat, endpoint, actual, analytic, value⟩ := related
  have ownFlat : ∀ vertices monomial, IsFlatSection D (fun parameter argument =>
      (PolynomialFamilies.sourceFlatExtension D hol plane parameter vertices argument).val.coeff monomial) :=
    fun vertices monomial => PolynomialFamilies.polynomialFlatExtension_flat D hol
      (PolynomialEisenstein.sourceSection D plane vertices) monomial
  have familyEq := StandardUniqueness.sourceFlatFamilies_eq_of_endpoint D family
    (PolynomialFamilies.sourceFlatExtension D hol plane) flat ownFlat
    (endpoint.trans (PolynomialFamilies.sourceFlatExtension_endpoint D hol plane).symm)
  rw [familyEq] at actual
  have continuationEq := StandardUniqueness.sourceStandardEndpoints_eq
    (PolynomialFamilies.sourceFlatExtension D hol plane) continuation
    (EdgeStandard.edgeSourceContinuation D hol plane) actual
    (fun vertices monomial => EdgeStandard.edgePolynomialContinuation_continues D hol
      (PolynomialEisenstein.sourceSection D plane vertices) monomial)
    analytic
    (fun vertices argument monomial => EdgeStandard.edgePolynomialContinuation_regular D hol
      (PolynomialEisenstein.sourceSection D plane vertices) argument monomial)
  exact value.symm.trans
    (continuationEq.trans (EdgeStandard.edgeSourceContinuation_endpoint D hol plane))

/-- **Line constant term** for every related pair, in every degree. -/
theorem lineConstantTerm_of_related (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (plane : SourceSpace.sourceCocycles D .plane) (line : SourceSpace.sourceCocycles D .line)
    (related : StandardRelation.Related D plane line) :
    LineConstantTermAtEdge D hol plane line := by
  intro vertices argument monomial
  rw [related_line_eq D hol plane line related]
  change (EdgeStandard.edgePolynomialValue D hol
    (PolynomialEisenstein.sourceSection D plane vertices) argument).val.coeff monomial = _
  rw [EdgeStandard.edgePolynomialValue_coeff, HolomorphicStandardValue.sectionStandard_constantTerm,
    LineConstantTerm.average_eq]
  refine integral_congr_ae (ae_of_all _ fun pair => ?_)
  exact (PolynomialNaturality.polynomialValue_coeff D hol
    (PolynomialEisenstein.sourceSection D plane vertices) monomial _).symm

end TernaryPeriodPolynomials.EdgeEisenstein
