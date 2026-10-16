module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.s.GlobalRealizationConv
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Graph

@[expose] public section


/-!
# The linearly selected constant-term map `T` is the standard (convergent) operator

`FacePairingFull.Graph.exists_constant_term_map` chooses the constant-term map `T` linearly from the existential
`constant_terms`. The paper's `T` is the operator that takes plane cusp data to the line constant term of the
convergent cusp-form sum (`thm:J-vanishes`, `ar:prop:graph`): for a plane source cocycle `c` of a cohomological cuspidal
datum `D` it is the class of the *standard line cocycle* `sourceStandard D c` (the absolutely convergent standard integral
`(Tφ)(g) = ∫ φ(w₀⁻¹ u(s,t) g) ds dt`, `ar:eq:intertwiner`).

* `standardLine_eq_of_graph`: let `T` be any linear map on plane stratum cohomology with the graph property of
  `ar:prop:graph` (a global class with zero flag restrictions has line restriction `T` of its plane restriction; such a
  `T` exists, `Graph.graph_containment`). Then for every plane source cocycle of every `CohomologicalCuspData`,
  `T [c] = [sourceStandard c]`. Proof: the explicit convergent global cocycle has coordinates
  `([c], [sourceStandard c])` (`ConstantTerm.restrictionFormula`) and zero flag restrictions (its line coordinate is inner);
  graph containment then forces `[sourceStandard c] = T [c]`.
* `standardLine_eq_T`: the same for the `T` of `exists_constant_term_map`; in particular `T` does not depend on the
  linear selection on the automorphic plane span (`standardLine_eq_of_graph` applied to two such maps).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.CuspidalSpan
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.FacePairingFull

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- **The standard operator is the graph map.** -/
theorem standardLine_eq_of_graph {n : ℕ} (hn : 4 ≤ n)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      EdgeExactGlobal c →
        (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1)
    (Dm : CohomologicalCuspData n)
    (plane : SourceSpace.sourceCocycles Dm.inducingData .plane) :
    SourceSpace.sourceClass Dm.inducingData .line
        (EndpointSourceStandard.sourceStandard Dm.inducingData hn
          (planeEisensteinConvergent hn Dm.inducingData) plane) =
      T (SourceSpace.sourceClass Dm.inducingData .plane plane) := by
  have hcoord := ConstantTerm.restrictionFormula hn Dm.inducingData
    (planeEisensteinConvergent hn Dm.inducingData) plane
  have hline : InnerBoundary n trivialCharacter .line
      (globalCoordinates n trivialCharacter
        (EndpointEisensteinCocycle.globalCocycle Dm.inducingData
          (planeEisensteinConvergent hn Dm.inducingData) hn plane)).2 := by
    rw [congrArg Prod.snd hcoord]
    exact sourceClass_line_subset_innerBoundary Dm.inducingData
      (EndpointSourceStandard.sourceStandard Dm.inducingData hn
        (planeEisensteinConvergent hn Dm.inducingData) plane)
  have hedge := exists_edgePrimitive_of_line_inner
    (EndpointEisensteinCocycle.globalCocycle Dm.inducingData
      (planeEisensteinConvergent hn Dm.inducingData) hn plane) hline
  have h := hT _ hedge
  rw [congrArg Prod.snd hcoord, congrArg Prod.fst hcoord] at h
  exact h

/-- **The linearly selected `T` is the standard operator.** -/
theorem standardLine_eq_T {n : ℕ} (hn : 4 ≤ n) :
    ∃ T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line,
      (∀ Dm : CohomologicalCuspData n, ∀ plane : SourceSpace.sourceCocycles Dm.inducingData .plane,
        SourceSpace.sourceClass Dm.inducingData .line
            (EndpointSourceStandard.sourceStandard Dm.inducingData hn
              (planeEisensteinConvergent hn Dm.inducingData) plane) =
          T (SourceSpace.sourceClass Dm.inducingData .plane plane)) ∧
      ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
        EdgeExactGlobal c →
          (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1 := by
  have hg := graph_containment (n := n) hn
  rcases hg with ⟨T, -, hT⟩
  exact ⟨T, fun Dm plane => standardLine_eq_of_graph hn T hT Dm plane, hT⟩

end TernaryPeriodPolynomials.Argument.FacePairingFull
