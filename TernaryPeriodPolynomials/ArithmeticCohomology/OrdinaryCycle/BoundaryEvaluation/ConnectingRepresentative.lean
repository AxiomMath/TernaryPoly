module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.ConnectingClasses

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open EquivariantSingularSmall SingularBoundaryRestriction SymmetricSpaceBoundaryIncidenceHomology
open OrdinaryTopBoundaryComparison

variable (W : Rep.{0} ℚ principalSix)

/-- The constructed positive lifted-differential cocycle represents the actual boundary
cohomology connecting class under the literal Hom-cokernel/kernel isomorphism. -/
theorem relativeConnectingCocycle_class (x : (homCochains boundaryChains W).cycles 1) :
    boundaryConnecting W 1 ((homCochains boundaryChains W).homologyπ 1 x) =
      homologyMap (relativeHomKernelIso W).hom 2
        ((homCochains upstairsRelativeChains W).homologyπ 2 (relativeConnectingCocycle W x)) := by
  let y := cyclesMap (relativeHomKernelIso W).hom 2 (relativeConnectingCocycle W x)
  have hy : (relativeCochains W).iCycles 2 y =
      (relativeHomKernelIso W).hom.f 2 (relativeConnectingCochain W x) := by
    have h := congrArg (fun f => f (relativeConnectingCocycle W x))
      (cyclesMap_i (relativeHomKernelIso W).hom 2)
    change (relativeCochains W).iCycles 2 y =
      (relativeHomKernelIso W).hom.f 2 (cocycleValue upstairsRelativeChains W 2
        (relativeConnectingCocycle W x)) at h
    rw [relativeConnectingCocycle_value] at h
    exact h
  have hinc := congrArg (fun f => f (relativeConnectingCochain W x))
    (HomologicalComplex.congr_hom (relativeHomKernelIso_inclusion W) 2)
  have h₁ : (relativeInclusion W).f 2 ((relativeCochains W).iCycles 2 y) =
      (absoluteCochains W).d 1 2 (boundaryCocycleExtension W x) := by
    rw [hy]
    exact hinc.trans (relativeConnectingCochain_projection W x)
  have hδ := connecting_abstract_cycles (RelativeCochainSequence.sequence (boundaryRestriction W))
    (boundary_shortExact W) 1 2 rfl x (boundaryCocycleExtension W x) y
    (boundaryCocycleExtension_restriction W x) h₁
  have hnat := congrArg (fun f => f (relativeConnectingCocycle W x))
    (homologyπ_naturality (relativeHomKernelIso W).hom 2)
  exact hδ.trans hnat.symm

end TernaryPoly.OrdinaryBoundaryActualEvaluation
