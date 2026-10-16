module

public import TernaryPeriodPolynomials.EisensteinSeries.Edge.RestrictionFormula
public import TernaryPeriodPolynomials.EisensteinSeries.Edge.EisensteinRegularity
public import TernaryPeriodPolynomials.EisensteinSeries.Edge.LineConstant
public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Edge.StandardEisenstein
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.GraphReduction

@[expose] public section


/-!
# Global Eisenstein classes at the edge of absolute convergence

For every degree, and in particular for `n = 3` where the Eisenstein series does not converge at
`s₀ = -3/2`, the global Eisenstein classes `EdgeStandardEisenstein.edgeGlobalClass` project to
`([c], [line])` for every related pair `(c, line)`, for any projection that is the identity on the
associate pair. The only input beyond `PlaneEisensteinHolomorphic` is the right real equivariance of
the Eisenstein value at `s₀` (`EdgeStandardEisenstein.EdgeEisensteinOperator`), which makes the
vertex values a global cocycle. Continuity and the plane constant term of the Eisenstein value come
from `EisensteinRegularity`, the line constant term from `LineConstant`, and the cohomological
restriction formula from `RestrictionFormula`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.EdgeEisenstein

open TernaryPeriodPolynomials
open TernaryPeriodPolynomials.EisensteinGraph
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EdgeConvergence

variable {n : ℕ}

/-- **The restriction formula at the edge.** The maximal-stratum coordinates of the global
Eisenstein cocycle of `c` are `([c], [line])` for every line cocycle related to `c`. -/
theorem edge_restriction_formula (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (edge : EdgeStandardEisenstein.EdgeEisensteinOperator D hol)
    (plane : SourceSpace.sourceCocycles D .plane) (line : SourceSpace.sourceCocycles D .line)
    (related : StandardRelation.Related D plane line) :
    globalCoordinates n D.chi (EdgeStandardEisenstein.edgeGlobalCocycle D hol edge plane) =
      (SourceSpace.sourceClass D .plane plane, SourceSpace.sourceClass D .line line) :=
  restriction_formula D hol (EisensteinRegularity.eisensteinContinuous D hol)
    (EisensteinRegularity.planeConstantTerm D hol) plane
    (EdgeStandardEisenstein.sourceValue_real_covariant D hol edge plane) line
    (lineConstantTerm_of_related D hol plane line related)

/-- **Global Eisenstein classes**, in every degree, from the right real equivariance of the
Eisenstein value at `s₀`. -/
theorem hasEisensteinClasses_of_edge (D : InducingData n) (hol : PlaneEisensteinHolomorphic D)
    (edge : EdgeStandardEisenstein.EdgeEisensteinOperator D hol)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (identity : ∀ x ∈ associatePair D, projection x = x) :
    GraphReduction.HasEisensteinClasses D projection := by
  refine ⟨EdgeStandardEisenstein.edgeGlobalClass D hol edge, ?_⟩
  intro plane line related
  have coordinates := GraphPieces.Helpers.canonicalCoordinates_restriction n D.chi
    (EdgeStandardEisenstein.edgeGlobalCocycle D hol edge plane)
  have formula := edge_restriction_formula D hol edge plane line related
  unfold globalCoordinates at formula
  change projection ((GraphPieces.Helpers.canonicalCoordinates n D.chi).comp
      (GraphPieces.Helpers.canonicalRestriction n D.chi)
        (classOf rationalLevel (rationalCoefficientComponent n D.chi)
          (EdgeStandardEisenstein.edgeGlobalCocycle D hol edge plane))) = _
  rw [coordinates, formula]
  apply identity
  constructor
  · rw [← SourceSpace.sourceClass_range D .plane]
    exact ⟨plane, rfl⟩
  · rw [← SourceSpace.sourceClass_range D .line]
    exact ⟨line, rfl⟩

/-- **Global Eisenstein classes in degree three**, the `n = 3` conjunct of the general Eisenstein
graph. The residual input is the right real equivariance `EdgeEisensteinOperator` of the
Eisenstein value at the edge `s₀ = -n/2` of absolute convergence. -/
theorem hasEisensteinClasses_three (hn : n = 3) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (identity : ∀ x ∈ associatePair D, projection x = x)
    (edge : EdgeStandardEisenstein.EdgeEisensteinOperator D hol) :
    GraphReduction.HasEisensteinClasses D projection := by
  subst hn
  exact hasEisensteinClasses_of_edge D hol edge projection identity

/-- Sanity check: for `4 ≤ n` the input holds (absolutely convergent series), so the edge theorem
recovers `ConstantTerm.hasEisensteinClasses_of_large`. -/
theorem hasEisensteinClasses_of_large' (large : 4 ≤ n) (D : InducingData n)
    (hol : PlaneEisensteinHolomorphic D)
    (projection : Module.End ℂ (BoundaryCoordinates n D.chi))
    (identity : ∀ x ∈ associatePair D, projection x = x) :
    GraphReduction.HasEisensteinClasses D projection :=
  hasEisensteinClasses_of_edge D hol
    (EdgeStandardEisenstein.edgeEisensteinOperator_of_large D hol large) projection identity

end TernaryPeriodPolynomials.EdgeEisenstein
