module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.StandardConv.Unique
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.StandardOperator

@[expose] public section


/-!
# The linear standard operator of `RealizesStandardConv` is the graph map `T`

the `StandardConv.realizesStandardConv_apply_eq_sourceStandard` (identity theorem on the half plane `-d/2 < Re s`: the line cocycle of
`RelatedConv` is the convergent `sourceStandard`) says that any linear map `standard` on the boundary summand with
`RealizesStandardConv` takes the class of a plane source `c` to the class of `sourceStandard c`. Together with
`StandardOperator.standardLine_eq_of_graph` (every `T` with the graph property of `ar:prop:graph` does the same) this gives
`standard = T` on the whole plane boundary summand: the abstract operator characterized by the continuation of the standard family,
the convergent standard integral, and the constant-term map selected from the global classes of `ar:prop:graph` coincide.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- **`standard = T` on the plane boundary summand.** -/
theorem standard_eq_T {n : ℕ} (hn : 4 ≤ n)
    (T : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line)
    (hT : ∀ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
      EdgeExactGlobal c →
        (globalCoordinates n trivialCharacter c).2 = T (globalCoordinates n trivialCharacter c).1)
    (Dm : CohomologicalCuspData n)
    (standard : boundarySummand Dm.inducingData .plane →ₗ[ℂ] boundarySummand Dm.inducingData .line)
    (hstd : RealizesStandardConv Dm.inducingData standard)
    (x : boundarySummand Dm.inducingData .plane) :
    (standard x).val = T x.val := by
  have hr := SourceSpace.sourceClass_range Dm.inducingData .plane
  have hx : x.val ∈ LinearMap.range (SourceSpace.sourceClass Dm.inducingData .plane) := by
    rw [hr]
    exact x.property
  rcases hx with ⟨plane, hplane⟩
  have hx' : x = SourceQuotient.sourceToSummand Dm.inducingData .plane plane :=
    Subtype.ext hplane.symm
  rw [hx', StandardConv.realizesStandardConv_apply_eq_sourceStandard Dm.inducingData hn
    (planeEisensteinConvergent hn Dm.inducingData) standard hstd plane]
  exact standardLine_eq_of_graph hn T hT Dm plane

end TernaryPeriodPolynomials.Argument.FacePairingFull
