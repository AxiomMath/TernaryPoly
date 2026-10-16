module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.FiniteCycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.Apartment

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence EquivariantSingularSmall
open SymmetricSpaceBoundaryFull SymmetricSpaceBoundaryFullTransfer SymmetricSpaceBoundaryIncidenceHomology
open SymmetricSpaceBoundaryManifold SymmetricSpaceBoundaryDuality SymmetricSpaceBoundaryOrientation OrdinaryTopBoundaryComparison

variable (W : Rep.{0} ℚ principalSix)

/-- The actual finite boundary cycle retains the literal canonical inverse on its underlying chain. -/
theorem finiteApartmentBoundaryCycle_value :
    boundaryChains.iCycles 1 finiteApartmentBoundaryCycle =
      (canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain := by
  have h := congrArg (fun f => f.hom finiteApartmentCycle)
    (cyclesMap_i (coverRestrictionFunctor.map canonicalBoundaryEquiv.inv) 1)
  change boundaryChains.iCycles 1 finiteApartmentBoundaryCycle =
    (canonicalBoundaryEquiv.inv.f 1).hom
      ((restrictedComplex principalSix canonicalFaceCone).iCycles 1 finiteApartmentCycle) at h
  rw [finiteApartmentCycle_value] at h
  exact h

/-- Genuine capped boundary evaluation is the explicit finite canonical-cone evaluation. -/
theorem cappedBoundary_finite_evaluation (x : (homCochains boundaryChains W).cycles 1) :
    groupApartmentEvaluation W (boundaryToGroup W 3
      ((boundaryH1CapIso W boundaryOrientation).hom ((boundaryCohomologyIso W).hom
        ((homCochains boundaryChains W).homologyπ 1 x)))) =
      (cocycleValue boundaryChains W 1 x).hom
        ((canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain) := by
  rw [cappedBoundary_cocycle_evaluation W x finiteApartmentBoundaryCycle finiteApartmentBoundaryCycle_class,
    finiteApartmentBoundaryCycle_value]

/-- The same exact evaluation for any cochain with a proved incoming-boundary vanishing identity. -/
theorem cappedBoundary_cochain_finite_evaluation (b : boundaryChains.X 1 ⟶ W)
    (hb : boundaryChains.d 2 1 ≫ b = 0) :
    groupApartmentEvaluation W (boundaryToGroup W 3
      ((boundaryH1CapIso W boundaryOrientation).hom ((boundaryCohomologyIso W).hom
        ((homCochains boundaryChains W).homologyπ 1 (cocycleOfBoundary boundaryChains W 1 b hb))))) =
      b.hom ((canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain) := by
  rw [cappedBoundary_finite_evaluation, cocycleOfBoundary_value]

end TernaryPoly.OrdinaryBoundaryActualEvaluation
