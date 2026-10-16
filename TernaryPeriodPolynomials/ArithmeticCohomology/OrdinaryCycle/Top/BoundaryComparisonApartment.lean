module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonCap
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Apartment.Presentation

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryTopBoundaryComparison
open CategoryTheory HomologicalComplex IntegralGL3Congruence
open EquivariantSingularSmall SingularLocalHomology OrdinaryApartmentPresentation
open SymmetricSpaceBoundaryIncidenceHomology

/-- The identity-frame apartment, as an actual ordinary incidence homology cycle. -/
abbrev identityApartment : ordinaryCyclesRep := frameCycle 1

/-- The actual upstairs boundary homology class represented by the identity apartment. -/
def identityApartmentBoundaryClass : boundaryChains.homology 1 :=
  boundaryH1OrdinaryCyclesIso.inv identityApartment

/-- The actual relative class lifting the identity apartment through the literal connecting map. -/
def identityApartmentRelativeClass : upstairsRelativeChains.homology 2 :=
  upstairsRelativeH2OrdinaryIso.inv identityApartment

/-- This relative class maps to the actual identity-apartment boundary homology class. -/
theorem identityApartmentRelativeClass_connecting :
    upstairsRelativeSequence_shortExact.δ 2 1 rfl identityApartmentRelativeClass =
      identityApartmentBoundaryClass := by
  change upstairsRelativeH2BoundaryIso.hom
    (upstairsRelativeH2BoundaryIso.inv (boundaryH1OrdinaryCyclesIso.inv identityApartment)) = _
  exact congrArg (fun f => f.hom (boundaryH1OrdinaryCyclesIso.inv identityApartment))
    upstairsRelativeH2BoundaryIso.inv_hom_id

/-- The distinguished ordinary coefficient evaluates the literal identity apartment. -/
def identityApartmentEvaluation (W : Rep.{0} ℚ principalSix) : ordinaryFunctionals W ⟶ ModuleCat.of ℚ W :=
  ModuleCat.ofHom {
    toFun := fun φ => φ.hom identityApartment
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The actual arithmetic top evaluator, using actual cap, relative descent, and the identity apartment. -/
def groupApartmentEvaluation (W : Rep.{0} ℚ principalSix) : groupHomology W 3 ⟶ ModuleCat.of ℚ W :=
  (groupOrdinaryIso W).hom ≫ identityApartmentEvaluation W

/-- On an actual capped cohomology class, top evaluation is canonical evaluation on the actual
relative identity-apartment class. -/
theorem cappedClass_apartmentEvaluation (W : Rep.{0} ℚ principalSix)
    (x : (homCochains upstairsRelativeChains W).homology 2) :
    groupApartmentEvaluation W ((bordifiedGroupLocalHomologyIso W 3).inv
      ((relativeHomCapIso W).hom x)) =
    (homologyEvaluation upstairsRelativeChains W 2 x).hom identityApartmentRelativeClass := by
  have h := congrArg (fun f => f x) (cappedClass_groupOrdinary W)
  change identityApartmentEvaluation W
    ((groupOrdinaryIso W).hom ((bordifiedGroupLocalHomologyIso W 3).inv
      ((relativeHomCapIso W).hom x))) = _
  change (groupOrdinaryIso W).hom ((bordifiedGroupLocalHomologyIso W 3).inv
    ((relativeHomCapIso W).hom x)) = (relativeOrdinaryCohomologyIso W).hom x at h
  rw [h, relativeOrdinaryCohomologyIso_apply]
  rfl

end TernaryPoly.OrdinaryTopBoundaryComparison
