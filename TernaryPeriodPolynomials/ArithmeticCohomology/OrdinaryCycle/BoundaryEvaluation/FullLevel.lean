module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.FiniteCap
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.NormalizedFinite

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence EquivariantSingularSmall SingularLocalHomology
open SymmetricSpaceBoundaryFull SymmetricSpaceBoundaryFullTransfer SymmetricSpaceBoundaryIncidenceHomology
open SymmetricSpaceBoundaryDuality SymmetricSpaceBoundaryManifold SymmetricSpaceBoundaryOrientation OrdinaryTopBoundaryComparison OrdinaryBoundaryCone

/-- The actual full-level boundary image in genuine arithmetic H3, through restriction and genuine boundary cap. -/
def fullBoundaryClassToGroup (n : ℕ) (e : ℤ) :
    (fullBoundaryCochains n e).homology 1 ⟶ groupHomology (restrictedCoefficients n e) 3 :=
  homologyMap (boundaryRestriction n e) 1 ≫
    (boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).hom ≫
      boundaryToGroup (restrictedCoefficients n e) 3

/-- Full-level restriction preserves the literal boundary cocycle, including all residue coordinates. -/
theorem restriction_boundary_cocycle_value (n : ℕ) (e : ℤ)
    (x : (fullBoundaryCochains n e).cycles 1) :
    cocycleValue boundaryChains (restrictedCoefficients n e) 1
      (cyclesMap (restriction principalSix fullBoundaryChains (actualCoefficients n e)) 1 x) =
        (Rep.resFunctor principalSix.subtype).map
          (cocycleValue fullBoundaryChains (actualCoefficients n e) 1 x) := by
  have h := congrArg (fun f => f x)
    (cyclesMap_i (restriction principalSix fullBoundaryChains (actualCoefficients n e)) 1)
  exact h

/-- A genuine full-boundary cocycle has exactly its finite geometric apartment evaluation in arithmetic H3. -/
theorem fullBoundaryClassToGroup_cocycle_evaluation (n : ℕ) (e : ℤ)
    (x : (fullBoundaryCochains n e).cycles 1) :
    groupApartmentEvaluation (restrictedCoefficients n e)
      (fullBoundaryClassToGroup n e ((fullBoundaryCochains n e).homologyπ 1 x)) =
      (cocycleValue fullBoundaryChains (actualCoefficients n e) 1 x).hom
        ((canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain) := by
  let r := restriction principalSix fullBoundaryChains (actualCoefficients n e)
  have hn := congrArg (fun f => f x) (homologyπ_naturality r 1)
  have hmap : homologyMap (boundaryRestriction n e) 1 ((fullBoundaryCochains n e).homologyπ 1 x) =
      (boundaryCohomologyIso (restrictedCoefficients n e)).hom
        ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 (cyclesMap r 1 x)) := by
    rw [boundaryRestriction, homologyMap_comp]
    exact congrArg (fun y => (boundaryCohomologyIso (restrictedCoefficients n e)).hom y) hn
  change groupApartmentEvaluation (restrictedCoefficients n e)
    (boundaryToGroup (restrictedCoefficients n e) 3
      ((boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).hom
        (homologyMap (boundaryRestriction n e) 1 ((fullBoundaryCochains n e).homologyπ 1 x)))) = _
  erw [hmap, cappedBoundary_finite_evaluation, restriction_boundary_cocycle_value]
  rfl

/-- The distinguished coefficient of every actual full-level whole-boundary H3 image has pairwise support. -/
theorem fullBoundaryClassToGroup_pairwise (n : ℕ) (e : ℤ)
    (x : (fullBoundaryCochains n e).homology 1) :
    coefficientPairwise n (groupApartmentEvaluation (restrictedCoefficients n e) (fullBoundaryClassToGroup n e x)) := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((fullBoundaryCochains n e).homologyπ 1)).mp inferInstance x
  rw [fullBoundaryClassToGroup_cocycle_evaluation]
  exact fullBoundaryCocycle_finite_pairwise n e _
    (cocycleValue_boundary fullBoundaryChains (actualCoefficients n e) 1 z)

/-- Every true full-level boundary class, characterized by the actual projector, has pairwise top evaluation. -/
theorem fullLevelBoundary_pairwise (n : ℕ) (e : ℤ)
    (x : fullLevelComponent n e 1) :
    coefficientPairwise n (groupApartmentEvaluation (restrictedCoefficients n e)
      (boundaryToGroup (restrictedCoefficients n e) 3
        ((boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).hom x.val))) := by
  obtain ⟨y, hy⟩ := (fullLevelComponent_iff_image n e 1 x.val).mp x.property
  rw [← hy]
  exact fullBoundaryClassToGroup_pairwise n e y

end TernaryPoly.OrdinaryBoundaryActualEvaluation
