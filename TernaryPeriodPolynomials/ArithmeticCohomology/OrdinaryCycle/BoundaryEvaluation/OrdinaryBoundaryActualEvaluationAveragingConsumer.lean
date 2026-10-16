module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.OrdinaryBoundaryActualEvaluationAveraging

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence ModThreeGoodAction
open SymmetricSpaceBoundaryFull SymmetricSpaceBoundaryFullTransfer EquivariantSingularSmall
open SymmetricSpaceBoundaryIncidenceHomology OrdinaryTopBoundaryComparison OrdinaryApartmentPresentation
open OrdinaryBoundaryCone SymmetricSpaceBoundaryManifold SymmetricSpaceBoundaryOrientation
open SymmetricSpaceBoundaryDuality SingularLocalHomology

/-- Literal actual cap and inclusion recover the whole canonical boundary ordinary functional. -/
theorem cappedBoundary_ordinary_apply (W : Rep.{0} ℚ principalSix)
    (x : (homCochains boundaryChains W).homology 1) :
    (groupOrdinaryIso W).hom (boundaryToGroup W 3
      ((boundaryH1CapIso W boundaryOrientation).hom ((boundaryCohomologyIso W).hom x))) =
    boundaryOrdinaryEvaluation W x := by
  have h := congrArg (fun f => f x) (cappedBoundary_ordinary W)
  exact h

/-- Actual normalized boundary descent corresponds to the actual averaged ordinary functional. -/
theorem normalizedBoundaryClassToGroup_ordinary (n : ℕ) (e : ℤ)
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).homology 1) :
    (groupOrdinaryIso (restrictedCoefficients n e)).hom (normalizedBoundaryClassToGroup n e x) =
    boundaryOrdinaryEvaluation (restrictedCoefficients n e)
      (homologyMap (descentProjector principalSix fullBoundaryChains (actualCoefficients n e)) 1 x) := by
  unfold normalizedBoundaryClassToGroup fullBoundaryClassToGroup boundaryRestriction descentProjector
  rw [homologyMap_comp, homologyMap_comp]
  exact cappedBoundary_ordinary_apply (restrictedCoefficients n e) _

/-- Averaging an arbitrary actual boundary preimage preserves its genuine arithmetic image
when the resulting ordinary functional is full-equivariant. -/
theorem normalizedBoundaryClassToGroup_eq_of_fullEquivariant (n : ℕ) (e : ℤ)
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).homology 1)
    (hx : ordinaryFunctionalFullEquivariant n e (boundaryOrdinaryEvaluation (restrictedCoefficients n e) x)) :
    normalizedBoundaryClassToGroup n e x = boundaryToGroup (restrictedCoefficients n e) 3
      ((boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).hom
        ((boundaryCohomologyIso (restrictedCoefficients n e)).hom x)) := by
  apply (ConcreteCategory.bijective_of_isIso (groupOrdinaryIso (restrictedCoefficients n e)).hom).injective
  rw [normalizedBoundaryClassToGroup_ordinary, averagedBoundaryClass_ordinary n e x hx,
    cappedBoundary_ordinary_apply]

/-- Any full-equivariant ordinary functional represented by actual boundary cohomology has Pairwise support. -/
theorem fullEquivariant_boundaryOrdinary_pairwise (n : ℕ) (e : ℤ)
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).homology 1)
    (hx : ordinaryFunctionalFullEquivariant n e (boundaryOrdinaryEvaluation (restrictedCoefficients n e) x)) :
    coefficientPairwise n ((boundaryOrdinaryEvaluation (restrictedCoefficients n e) x).hom identityApartment) := by
  have hp := normalizedBoundaryClassToGroup_pairwise n e x
  change coefficientPairwise n
    (((groupOrdinaryIso (restrictedCoefficients n e)).hom (normalizedBoundaryClassToGroup n e x)).hom
      identityApartment) at hp
  rw [normalizedBoundaryClassToGroup_ordinary, averagedBoundaryClass_ordinary n e x hx] at hp
  exact hp

/-- An arbitrary genuine boundary class has a literal boundary cohomology preimage under fixed cap. -/
def actualBoundaryCohomologyPreimage (n : ℕ) (e : ℤ)
    (b : (boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    (homCochains boundaryChains (restrictedCoefficients n e)).homology 1 :=
  (boundaryCohomologyIso (restrictedCoefficients n e)).inv
    ((boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).inv b)

/-- The preimage's ordinary functional is precisely the actual boundary image's ordinary functional. -/
theorem actualBoundaryCohomologyPreimage_ordinary (n : ℕ) (e : ℤ)
    (b : (boundaryLocalChains (restrictedCoefficients n e)).homology 3) :
    boundaryOrdinaryEvaluation (restrictedCoefficients n e) (actualBoundaryCohomologyPreimage n e b) =
    (groupOrdinaryIso (restrictedCoefficients n e)).hom (boundaryToGroup (restrictedCoefficients n e) 3 b) := by
  rw [← cappedBoundary_ordinary_apply]
  unfold actualBoundaryCohomologyPreimage
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]

/-- Full equivariance of the actual ordinary functional suffices for every genuine boundary H3 image.
The chosen boundary class itself need not belong to the full-level component. -/
theorem boundary_image_fullEquivariant_pairwise (n : ℕ) (e : ℤ)
    (b : (boundaryLocalChains (restrictedCoefficients n e)).homology 3)
    (hb : ordinaryFunctionalFullEquivariant n e
      ((groupOrdinaryIso (restrictedCoefficients n e)).hom (boundaryToGroup (restrictedCoefficients n e) 3 b))) :
    coefficientPairwise n (groupApartmentEvaluation (restrictedCoefficients n e)
      (boundaryToGroup (restrictedCoefficients n e) 3 b)) := by
  have hx : ordinaryFunctionalFullEquivariant n e (boundaryOrdinaryEvaluation (restrictedCoefficients n e)
      (actualBoundaryCohomologyPreimage n e b)) := by
    rw [actualBoundaryCohomologyPreimage_ordinary]
    exact hb
  have hp := fullEquivariant_boundaryOrdinary_pairwise n e (actualBoundaryCohomologyPreimage n e b) hx
  rw [actualBoundaryCohomologyPreimage_ordinary] at hp
  exact hp

/-- The actual entire-boundary-image hypothesis and full ordinary equivariance imply Pairwise support. -/
theorem actual_boundary_image_fullEquivariant_pairwise (n : ℕ) (e : ℤ)
    (x : groupHomology (restrictedCoefficients n e) 3)
    (hboundary : ∃ b : (boundaryLocalChains (restrictedCoefficients n e)).homology 3,
      boundaryToGroup (restrictedCoefficients n e) 3 b = x)
    (hfull : ordinaryFunctionalFullEquivariant n e ((groupOrdinaryIso (restrictedCoefficients n e)).hom x)) :
    coefficientPairwise n (groupApartmentEvaluation (restrictedCoefficients n e) x) := by
  obtain ⟨b, rfl⟩ := hboundary
  exact boundary_image_fullEquivariant_pairwise n e b hfull

end TernaryPoly.OrdinaryBoundaryActualEvaluation
