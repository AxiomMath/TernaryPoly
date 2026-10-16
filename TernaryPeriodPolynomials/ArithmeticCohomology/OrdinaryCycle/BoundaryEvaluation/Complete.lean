module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.OrdinaryBoundaryActualEvaluationAveragingConsumer

@[expose] public section

noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open SymmetricSpaceBoundaryFull SymmetricSpaceBoundaryFullTransfer EquivariantSingularSmall
open SymmetricSpaceBoundaryIncidenceHomology OrdinaryTopBoundaryComparison OrdinaryBoundaryCone
open SymmetricSpaceBoundaryManifold SymmetricSpaceBoundaryOrientation SymmetricSpaceBoundaryDuality
open SingularLocalHomology

/-- Averaging places every genuine boundary image with full-equivariant ordinary functional
in the actual full-integral restriction image, without altering that arithmetic class. -/
theorem fullEquivariant_boundary_image_mem (n : ℕ) (e : ℤ)
    (b : (boundaryLocalChains (restrictedCoefficients n e)).homology 3)
    (hb : ordinaryFunctionalFullEquivariant n e
      ((groupOrdinaryIso (restrictedCoefficients n e)).hom (boundaryToGroup (restrictedCoefficients n e) 3 b))) :
    boundaryToGroup (restrictedCoefficients n e) 3 b ∈ actualFullBoundaryImage n e := by
  let x := actualBoundaryCohomologyPreimage n e b
  have hx : ordinaryFunctionalFullEquivariant n e (boundaryOrdinaryEvaluation (restrictedCoefficients n e) x) := by
    change ordinaryFunctionalFullEquivariant n e
      (boundaryOrdinaryEvaluation (restrictedCoefficients n e) (actualBoundaryCohomologyPreimage n e b))
    rw [actualBoundaryCohomologyPreimage_ordinary]
    exact hb
  refine ⟨homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1 x, ?_⟩
  change normalizedBoundaryClassToGroup n e x = boundaryToGroup (restrictedCoefficients n e) 3 b
  apply (ConcreteCategory.bijective_of_isIso (groupOrdinaryIso (restrictedCoefficients n e)).hom).injective
  rw [normalizedBoundaryClassToGroup_ordinary, averagedBoundaryClass_ordinary n e x hx]
  exact actualBoundaryCohomologyPreimage_ordinary n e b

/-- On actual full-equivariant ordinary classes, the entire boundary image equals the
full-integral restriction image. This is an equality of actual images in principal-six H3. -/
theorem actualFullBoundaryImage_iff_boundary_of_fullEquivariant (n : ℕ) (e : ℤ)
    (x : groupHomology (restrictedCoefficients n e) 3)
    (hx : ordinaryFunctionalFullEquivariant n e ((groupOrdinaryIso (restrictedCoefficients n e)).hom x)) :
    x ∈ actualFullBoundaryImage n e ↔
      ∃ b : (boundaryLocalChains (restrictedCoefficients n e)).homology 3,
        boundaryToGroup (restrictedCoefficients n e) 3 b = x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).hom
      (homologyMap (boundaryRestriction n e) 1 y), rfl⟩
  · rintro ⟨b, rfl⟩
    exact fullEquivariant_boundary_image_mem n e b hx

/-- The ordinary-boundary support endpoint: a full-integral equivariant ordinary functional
has Pairwise reference coefficient whenever its actual arithmetic H3 class comes from the entire boundary.
No assertion that every ordinary class is boundary is included. -/
theorem ordinary_functional_boundary_pairwise (n : ℕ) (e : ℤ)
    (φ : ordinaryFunctionals (restrictedCoefficients n e))
    (hfull : ordinaryFunctionalFullEquivariant n e φ)
    (hboundary : ∃ b : (boundaryLocalChains (restrictedCoefficients n e)).homology 3,
      boundaryToGroup (restrictedCoefficients n e) 3 b = (groupOrdinaryIso (restrictedCoefficients n e)).inv φ) :
    coefficientPairwise n (φ.hom identityApartment) := by
  have hf : ordinaryFunctionalFullEquivariant n e
      ((groupOrdinaryIso (restrictedCoefficients n e)).hom ((groupOrdinaryIso (restrictedCoefficients n e)).inv φ)) := by
    rw [Iso.inv_hom_id_apply]
    exact hfull
  have h := actual_boundary_image_fullEquivariant_pairwise n e
    ((groupOrdinaryIso (restrictedCoefficients n e)).inv φ) hboundary hf
  change coefficientPairwise n
    (((groupOrdinaryIso (restrictedCoefficients n e)).hom
      ((groupOrdinaryIso (restrictedCoefficients n e)).inv φ)).hom identityApartment) at h
  rw [Iso.inv_hom_id_apply] at h
  exact h

end TernaryPoly.OrdinaryBoundaryActualEvaluation
