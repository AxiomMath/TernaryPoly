module

public import TernaryPeriodPolynomials.BoundaryComparison.CuspidalSpan.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.GraphPieces.EndpointReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagExactness.LineTranslateInvariance
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.SourceSpace

@[expose] public section


/-!
# Every realized line source class is `InnerBoundary`

Line-side mirror of `PlaneInner.lean`. There, a plane boundary-summand class was shown
`InnerBoundary` via the pre-packaged `BoundaryDuality.TracePairing.flat_of_mem`. No such
package exists for the line side, so this file reproduces its underlying argument directly, with
`FlagExactness.line_flagExact` (unconditional on *every* line source cocycle, unlike the
conditional, Hecke-eigenvalue-indexed facts elsewhere in the project) replacing `plane_flagExact`,
following exactly the pattern of the `BoundaryDuality.TraceRepresentatives.planeEdgeExact_of_mem`:
`GraphPieces.EndpointReduction.boundarySummand_le_ker` reduces summand membership to vanishing of
`GraphPieces.BoundaryExactness.endpointPullH2`, whose realizing representative
(`endpointPullH2_realizes`) is then unpacked as a coboundary witness — exactly `InnerBoundary`'s
own existential, since `EdgeCochains n χ 1` is definitionally the codomain of that witness.

We state it directly for `SourceSpace.sourceClass`, since every explicit realization used in
`constant_terms`'s proof produces its line coordinate as a `sourceClass`-image (via
`EndpointSourceStandard.sourceStandard`), and `SourceSpace.evaluatedSource` is a canonical
representative cocycle for it, avoiding a separate representative-existence lemma.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section


namespace TernaryPeriodPolynomials.Argument.CuspidalSpan

open TernaryPeriodPolynomials.GraphPieces.EndpointReduction
open TernaryPeriodPolynomials.GraphPieces.BoundaryExactness
open TernaryPeriodPolynomials.FlagExactness
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

/-- Every class realized by `SourceSpace.sourceClass` on the line side is `InnerBoundary`. -/
theorem sourceClass_line_subset_innerBoundary {n : ℕ} (D : InducingData n)
    (source : SourceSpace.sourceCocycles D .line) :
    InnerBoundary n D.chi .line (SourceSpace.sourceClass D .line source) := by
  set y := SourceSpace.evaluatedSource D .line source with hy_def
  have hclassy : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .line) y =
      SourceSpace.sourceClass D .line source := rfl
  have hmem : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .line) y ∈
      boundarySummand D .line := by
    rw [hclassy, ← SourceSpace.sourceClass_range D .line]
    exact ⟨source, rfl⟩
  have hker := boundarySummand_le_ker D .line
    (fun src isSrc flag => line_flagExact D src isSrc flag) hmem
  rw [LinearMap.mem_ker, endpointPullH2_realizes] at hker
  obtain ⟨s, hs⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp hker)
  exact ⟨y, hclassy, s, fun x e =>
    (congrFun (congrFun (congrArg Subtype.val (congrArg Subtype.val hs)) x) e).symm⟩

end TernaryPeriodPolynomials.Argument.CuspidalSpan
