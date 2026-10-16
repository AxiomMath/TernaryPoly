module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.TranslatedApartment

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence ModThreeGoodAction
open SymmetricSpaceBoundaryFull SymmetricSpaceBoundaryFullTransfer EquivariantSingularSmall
open SymmetricSpaceBoundaryIncidenceHomology OrdinaryTopBoundaryComparison OrdinaryApartmentPresentation OrdinaryBoundaryCone

/-- Every translated representative is literally the full integral action on the fixed boundary chain. -/
theorem translatedFiniteApartmentBoundaryCycle_value (g : IntegralGL) :
    boundaryChains.iCycles 1 (translatedFiniteApartmentBoundaryCycle g) =
      (fullBoundaryChains.X 1).ρ g ((canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain) := by
  have h := congrArg (fun f => f.hom (translatedFiniteApartmentCycle g))
    (cyclesMap_i (coverRestrictionFunctor.map canonicalBoundaryEquiv.inv) 1)
  change boundaryChains.iCycles 1 (translatedFiniteApartmentBoundaryCycle g) =
    (canonicalBoundaryEquiv.inv.f 1).hom
      ((restrictedComplex principalSix canonicalFaceCone).iCycles 1 (translatedFiniteApartmentCycle g)) at h
  rw [translatedFiniteApartmentCycle_value, Rep.hom_comm_apply] at h
  exact h

/-- The canonical ordinary functional evaluates on each frame by the literal translated boundary cycle. -/
theorem boundaryOrdinaryEvaluation_frame (W : Rep.{0} ℚ principalSix)
    (x : (homCochains boundaryChains W).cycles 1) (g : IntegralGL) :
    (boundaryOrdinaryEvaluation W ((homCochains boundaryChains W).homologyπ 1 x)).hom (frameCycle g) =
      (cocycleValue boundaryChains W 1 x).hom
        ((fullBoundaryChains.X 1).ρ g ((canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain)) := by
  rw [boundaryOrdinaryEvaluation_cycle]
  have hc : boundaryH1OrdinaryCyclesIso.inv (frameCycle g) =
      boundaryChains.homologyπ 1 (translatedFiniteApartmentBoundaryCycle g) := by
    have h := congrArg (fun c => boundaryH1OrdinaryCyclesIso.inv c)
      (translatedFiniteApartmentBoundaryCycle_class g)
    have hi := congrArg (fun f => f.hom (boundaryChains.homologyπ 1
      (translatedFiniteApartmentBoundaryCycle g))) boundaryH1OrdinaryCyclesIso.hom_inv_id
    change boundaryH1OrdinaryCyclesIso.inv (boundaryH1OrdinaryCyclesIso.hom
      (boundaryChains.homologyπ 1 (translatedFiniteApartmentBoundaryCycle g))) =
      boundaryChains.homologyπ 1 (translatedFiniteApartmentBoundaryCycle g) at hi
    exact h.symm.trans hi
  change (cocycleEvaluation boundaryChains W 1 x).hom (boundaryH1OrdinaryCyclesIso.inv (frameCycle g)) = _
  rw [hc]
  have he := congrArg (fun f => f.hom (translatedFiniteApartmentBoundaryCycle g))
    (cocycleEvaluation_projection boundaryChains W 1 x)
  change (cocycleEvaluation boundaryChains W 1 x).hom
      (boundaryChains.homologyπ 1 (translatedFiniteApartmentBoundaryCycle g)) =
    (cocycleValue boundaryChains W 1 x).hom
      (boundaryChains.iCycles 1 (translatedFiniteApartmentBoundaryCycle g)) at he
  rw [translatedFiniteApartmentBoundaryCycle_value] at he
  exact he

/-- Actual full-equivariance is imposed on the whole ordinary cycle functional. -/
def ordinaryFunctionalFullEquivariant (n : ℕ) (e : ℤ)
    (φ : ordinaryFunctionals (restrictedCoefficients n e)) : Prop :=
  ∀ (g : IntegralGL) (c : OrdinaryIncidenceChains.Cycles),
    φ.hom (OrdinaryFullAction.cycleAction (OrdinaryFullAction.integral g) c) =
      (actualCoefficients n e).ρ g (φ.hom c)

/-- Full-equivariant ordinary functionals have literal representation-orbit values on every frame. -/
theorem fullEquivariant_frame (n : ℕ) (e : ℤ)
    (φ : ordinaryFunctionals (restrictedCoefficients n e))
    (hφ : ordinaryFunctionalFullEquivariant n e φ) (g : IntegralGL) :
    φ.hom (frameCycle g) = (actualCoefficients n e).ρ g (φ.hom identityApartment) := by
  have h := hφ g identityApartment
  change φ.hom (OrdinaryFullAction.cycleAction (OrdinaryFullAction.integral g) (frameCycle 1)) = _ at h
  rw [OrdinaryFullAction.frameCycle_equivariant, mul_one] at h
  exact h

end TernaryPoly.OrdinaryBoundaryActualEvaluation
