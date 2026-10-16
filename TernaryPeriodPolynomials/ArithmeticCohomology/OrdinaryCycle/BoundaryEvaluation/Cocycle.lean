module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonCap

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open EquivariantSingularSmall EquivariantSingularResolution SingularBoundaryRestriction
open SymmetricSpaceBoundaryIncidenceHomology SymmetricSpaceRationalGluing
open OrdinaryTopBoundaryComparison

variable (W : Rep.{0} ℚ principalSix)

/-- The actual quotient-Hom/kernel comparison retains literal ambient cochain inclusion. -/
theorem relativeHomKernelIso_inclusion :
    (relativeHomKernelIso W).hom ≫ relativeInclusion W =
      homPullback (cokernel.π upstairsBoundaryChainMap) W := by
  dsimp only [relativeHomKernelIso, Iso.trans_hom]
  rw [Category.assoc, kernelIsoOfEq_hom_comp_ι, HomCokernelKernel.cochainIso_hom_inclusion]

/-- Extend an actual boundary cocycle by zero on the actual ambient singular simplex complement. -/
def boundaryCocycleExtension (x : (homCochains boundaryChains W).cycles 1) :
    (equivariantChains principalSix (TopCat.of Glued)).X 1 ⟶ W :=
  cochainExtension boundaryInclusion boundaryInclusion_equivariant boundaryInclusion_injective W 1
    (cocycleValue boundaryChains W 1 x)

/-- Actual restriction of this extension recovers the original boundary cocycle. -/
theorem boundaryCocycleExtension_restriction (x : (homCochains boundaryChains W).cycles 1) :
    upstairsBoundaryChainMap.f 1 ≫ boundaryCocycleExtension W x = cocycleValue boundaryChains W 1 x :=
  cochainPullback_extension boundaryInclusion boundaryInclusion_equivariant
    boundaryInclusion_injective W 1 (cocycleValue boundaryChains W 1 x)

/-- The differential of the lifted cochain annihilates actual boundary two-chains. -/
theorem boundaryCocycleExtension_differential (x : (homCochains boundaryChains W).cycles 1) :
    upstairsBoundaryChainMap.f 2 ≫
      ((equivariantChains principalSix (TopCat.of Glued)).d 2 1 ≫ boundaryCocycleExtension W x) = 0 := by
  rw [← Category.assoc, upstairsBoundaryChainMap.comm 2 1, Category.assoc,
    boundaryCocycleExtension_restriction]
  exact cocycleValue_boundary boundaryChains W 1 x

/-- The literal differential of the extension descends to the actual relative chain cokernel. -/
def relativeConnectingCochain (x : (homCochains boundaryChains W).cycles 1) :
    upstairsRelativeChains.X 2 ⟶ W :=
  RelativeChainHomotopy.degreeDesc upstairsBoundaryChainMap 2
    ((equivariantChains principalSix (TopCat.of Glued)).d 2 1 ≫ boundaryCocycleExtension W x)
    (boundaryCocycleExtension_differential W x)

/-- The descended cochain retains the actual lifted differential, with positive sign. -/
theorem relativeConnectingCochain_projection (x : (homCochains boundaryChains W).cycles 1) :
    (cokernel.π upstairsBoundaryChainMap).f 2 ≫ relativeConnectingCochain W x =
      (equivariantChains principalSix (TopCat.of Glued)).d 2 1 ≫ boundaryCocycleExtension W x :=
  RelativeChainHomotopy.projection_degreeDesc _ _ _ _

/-- The descended differential is an actual relative cocycle. -/
theorem relativeConnectingCochain_boundary (x : (homCochains boundaryChains W).cycles 1) :
    upstairsRelativeChains.d 3 2 ≫ relativeConnectingCochain W x = 0 := by
  apply (cancel_epi ((cokernel.π upstairsBoundaryChainMap).f 3)).mp
  rw [← Category.assoc, (cokernel.π upstairsBoundaryChainMap).comm 3 2, Category.assoc,
    relativeConnectingCochain_projection, ← Category.assoc, d_comp_d, zero_comp, comp_zero]

/-- An actual cocycle representative for the boundary-cohomology connecting class. -/
def relativeConnectingCocycle (x : (homCochains boundaryChains W).cycles 1) :
    (homCochains upstairsRelativeChains W).cycles 2 :=
  degreeTwoCocycle upstairsRelativeChains W (relativeConnectingCochain W x)
    (relativeConnectingCochain_boundary W x)

/-- The representative has exactly the descended cochain, without a scalar or sign change. -/
theorem relativeConnectingCocycle_value (x : (homCochains boundaryChains W).cycles 1) :
    cocycleValue upstairsRelativeChains W 2 (relativeConnectingCocycle W x) =
      relativeConnectingCochain W x := degreeTwoCocycle_value _ _ _ _

end TernaryPoly.OrdinaryBoundaryActualEvaluation
