module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.FullLevel

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence EquivariantSingularSmall SingularLocalHomology
open SymmetricSpaceBoundaryFull SymmetricSpaceBoundaryFullTransfer SymmetricSpaceBoundaryIncidenceHomology
open SymmetricSpaceBoundaryManifold SymmetricSpaceBoundaryOrientation OrdinaryTopBoundaryComparison OrdinaryBoundaryCone
open SymmetricSpaceBoundaryDuality RationalCohomologyDescent

/-- Normalized full-level descent of an actual entire-boundary cover cohomology class into genuine arithmetic H3. -/
def normalizedBoundaryClassToGroup (n : ℕ) (e : ℤ) :
    (homCochains boundaryChains (restrictedCoefficients n e)).homology 1 ⟶
      groupHomology (restrictedCoefficients n e) 3 :=
  homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1 ≫ fullBoundaryClassToGroup n e

/-- Actual transfer of a cocycle retains its literal normalized equivariant averaging map. -/
theorem transfer_boundary_cocycle_value (n : ℕ) (e : ℤ)
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1) :
    cocycleValue fullBoundaryChains (actualCoefficients n e) 1
      (cyclesMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1 x) =
        transferHom principalSix (fullBoundaryChains.X 1) (actualCoefficients n e)
          (cocycleValue boundaryChains (restrictedCoefficients n e) 1 x) := by
  have h := congrArg (fun f => f x)
    (cyclesMap_i (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1)
  exact h

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- Exact arithmetic apartment evaluation after normalized transfer: no index, coefficient action,
or input-chain action is omitted. -/
theorem normalizedBoundaryClassToGroup_evaluation (n : ℕ) (e : ℤ)
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).cycles 1) :
    groupApartmentEvaluation (restrictedCoefficients n e)
      (normalizedBoundaryClassToGroup n e
        ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x)) =
      (Nat.card (RightCosets principalSix) : ℚ)⁻¹ •
        ∑ q : RightCosets principalSix, (actualCoefficients n e).ρ q.out⁻¹
          ((cocycleValue boundaryChains (restrictedCoefficients n e) 1 x).hom
            ((fullBoundaryChains.X 1).ρ q.out
              ((canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain))) := by
  have hn := congrArg (fun f => f x)
    (homologyπ_naturality (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1)
  change groupApartmentEvaluation (restrictedCoefficients n e)
    (fullBoundaryClassToGroup n e
      (homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1
        ((homCochains boundaryChains (restrictedCoefficients n e)).homologyπ 1 x))) = _
  erw [hn, fullBoundaryClassToGroup_cocycle_evaluation, transfer_boundary_cocycle_value, transferHom_apply]
  rfl

/-- The normalized full-level image of every actual cover-boundary class has pairwise distinguished support. -/
theorem normalizedBoundaryClassToGroup_pairwise (n : ℕ) (e : ℤ)
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).homology 1) :
    coefficientPairwise n (groupApartmentEvaluation (restrictedCoefficients n e)
      (normalizedBoundaryClassToGroup n e x)) :=
  fullBoundaryClassToGroup_pairwise n e
    (homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1 x)

/-- This normalized arithmetic image is exactly the genuine local boundary projector followed by cap and inclusion. -/
theorem normalizedBoundaryClassToGroup_projector (n : ℕ) (e : ℤ) :
    normalizedBoundaryClassToGroup n e =
      (boundaryCohomologyIso (restrictedCoefficients n e)).hom ≫
        homologyMap (boundaryProjector n e) 1 ≫
          (boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).hom ≫
            boundaryToGroup (restrictedCoefficients n e) 3 := by
  unfold normalizedBoundaryClassToGroup fullBoundaryClassToGroup boundaryProjector boundaryTransfer
  rw [homologyMap_comp, homologyMap_comp]
  have h {A B C D E : ModuleCat ℚ} (i : A ≅ B)
      (t : A ⟶ C) (r : C ⟶ D) (s : D ⟶ E) :
      t ≫ r ≫ s = i.hom ≫ ((i.inv ≫ t) ≫ r) ≫ s := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact h (boundaryCohomologyIso (restrictedCoefficients n e))
    (homologyMap (transfer principalSix fullBoundaryChains (actualCoefficients n e)) 1)
    (homologyMap (boundaryRestriction n e) 1) _

/-- On a genuinely full-level boundary class, normalized transfer preserves the actual unprojected boundary image. -/
theorem normalizedBoundaryClassToGroup_fixed (n : ℕ) (e : ℤ)
    (x : (homCochains boundaryChains (restrictedCoefficients n e)).homology 1)
    (hx : (boundaryCohomologyIso (restrictedCoefficients n e)).hom x ∈ fullLevelComponent n e 1) :
    normalizedBoundaryClassToGroup n e x = boundaryToGroup (restrictedCoefficients n e) 3
      ((boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).hom
        ((boundaryCohomologyIso (restrictedCoefficients n e)).hom x)) := by
  rw [normalizedBoundaryClassToGroup_projector]
  have hf := (mem_fullLevelComponent n e 1 _).mp hx
  change boundaryToGroup (restrictedCoefficients n e) 3
    ((boundaryH1CapIso (restrictedCoefficients n e) boundaryOrientation).hom
      (homologyMap (boundaryProjector n e) 1 ((boundaryCohomologyIso (restrictedCoefficients n e)).hom x))) = _
  rw [hf]

end TernaryPoly.OrdinaryBoundaryActualEvaluation
