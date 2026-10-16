module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.ChainLift

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open EquivariantSingularSmall SingularBoundaryRestriction SymmetricSpaceBoundaryIncidenceHomology
open OrdinaryTopBoundaryComparison

variable (W : Rep.{0} ℚ principalSix)

/-- Literal evaluation of the descended lifted differential equals evaluation of the
original boundary cochain on the actual lifted boundary. -/
theorem connecting_representative_evaluation (x : (homCochains boundaryChains W).cycles 1) :
    upstairsRelativeChains.iCycles 2 ≫ relativeConnectingCochain W x =
      relativeCycleBoundaryLift ≫ cocycleValue boundaryChains W 1 x := by
  rw [← relativeCycleAmbientLift_projection, Category.assoc, relativeConnectingCochain_projection,
    ← Category.assoc, ← relativeCycleBoundaryLift_inclusion, Category.assoc,
    boundaryCocycleExtension_restriction]

/-- Canonical evaluation intertwines the actual cohomology and homology connecting maps,
with sign +1, on every actual boundary cocycle. -/
theorem relativeConnectingCocycle_evaluation (x : (homCochains boundaryChains W).cycles 1) :
    cocycleEvaluation upstairsRelativeChains W 2 (relativeConnectingCocycle W x) =
      upstairsRelativeSequence_shortExact.δ 2 1 rfl ≫ cocycleEvaluation boundaryChains W 1 x := by
  apply (cancel_epi (upstairsRelativeChains.homologyπ 2)).mp
  have hright : upstairsRelativeChains.homologyπ 2 ≫
      upstairsRelativeSequence_shortExact.δ 2 1 rfl ≫ cocycleEvaluation boundaryChains W 1 x =
      relativeCycleBoundaryLift ≫ cocycleValue boundaryChains W 1 x := by
    erw [← Category.assoc (upstairsRelativeChains.homologyπ 2),
      relativeCycleBoundaryCycles_connecting, Category.assoc, cocycleEvaluation_projection]
    change (boundaryChains.liftCycles relativeCycleBoundaryLift 0 (by simp)
      relativeCycleBoundaryLift_cycle) ≫ boundaryChains.iCycles 1 ≫
        cocycleValue boundaryChains W 1 x = _
    erw [liftCycles_i_assoc]
  calc
    upstairsRelativeChains.homologyπ 2 ≫
        cocycleEvaluation upstairsRelativeChains W 2 (relativeConnectingCocycle W x) =
      upstairsRelativeChains.iCycles 2 ≫ cocycleValue upstairsRelativeChains W 2
        (relativeConnectingCocycle W x) := cocycleEvaluation_projection _ _ _ _
    _ = upstairsRelativeChains.iCycles 2 ≫ relativeConnectingCochain W x := by
      rw [relativeConnectingCocycle_value]
    _ = relativeCycleBoundaryLift ≫ cocycleValue boundaryChains W 1 x :=
      connecting_representative_evaluation W x
    _ = upstairsRelativeChains.homologyπ 2 ≫ upstairsRelativeSequence_shortExact.δ 2 1 rfl ≫
        cocycleEvaluation boundaryChains W 1 x := hright.symm

end TernaryPoly.OrdinaryBoundaryActualEvaluation
