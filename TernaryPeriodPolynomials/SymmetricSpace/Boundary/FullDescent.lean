module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullTransferEvaluation
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullAction
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullCoefficients
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.GeometricConeComplete

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex IntegralGL3Congruence OrdinaryBoundaryCone
open EquivariantSingularSmall SingularLocalCoefficient SingularBoundaryRestriction
open SymmetricSpaceBoundaryFullTransfer

abbrev fullBoundaryCochains (n : ℕ) (e : ℤ) := homCochains fullBoundaryChains (actualCoefficients n e)
abbrev coverBoundaryCochains (n : ℕ) (e : ℤ) :=
  SymmetricSpaceBoundaryGeometricCone.localBoundaryCochains (restrictedCoefficients n e)

/-- The restricted full boundary cochain complex is the genuine local-system model. -/
def restrictedLocalIso (n : ℕ) (e : ℤ) :
    homCochains (restrictedComplex principalSix fullBoundaryChains) (restrictedCoefficients n e) ≅
      coverBoundaryCochains n e :=
  cochainIso boundaryProjection boundaryQuotientCovering (restrictedCoefficients n e)

/-- Actual full integral cochains restrict to the entire finite-cover boundary. -/
def boundaryRestriction (n : ℕ) (e : ℤ) : fullBoundaryCochains n e ⟶ coverBoundaryCochains n e :=
  restriction principalSix fullBoundaryChains (actualCoefficients n e) ≫ (restrictedLocalIso n e).hom

/-- Normalized finite-cover transfer on the genuine entire boundary. -/
def boundaryTransfer (n : ℕ) (e : ℤ) : coverBoundaryCochains n e ⟶ fullBoundaryCochains n e :=
  (restrictedLocalIso n e).inv ≫ transfer principalSix fullBoundaryChains (actualCoefficients n e)

/-- Full-level restriction has a left inverse on actual geometric local cochains. -/
theorem boundaryRestriction_transfer (n : ℕ) (e : ℤ) :
    boundaryRestriction n e ≫ boundaryTransfer n e = 𝟙 _ := by
  unfold boundaryRestriction boundaryTransfer
  rw [Category.assoc,Iso.hom_inv_id_assoc,restriction_transfer]

/-- Actual cohomology on the full-level boundary injects into finite-cover local cohomology. -/
theorem boundaryRestriction_injective (n : ℕ) (e : ℤ) (j : ℕ) :
    Function.Injective (homologyMap (boundaryRestriction n e) j) := by
  have hs : homologyMap (boundaryRestriction n e) j ≫ homologyMap (boundaryTransfer n e) j = 𝟙 _ := by
    rw [← homologyMap_comp,boundaryRestriction_transfer,homologyMap_id]
  intro x y h
  have he := congrArg (fun z => homologyMap (boundaryTransfer n e) j z) h
  exact (congrArg (fun u => u x) hs).symm.trans (he.trans (congrArg (fun u => u y) hs))

/-- The required full-level component is the image of this explicit geometric projector. -/
def boundaryProjector (n : ℕ) (e : ℤ) : coverBoundaryCochains n e ⟶ coverBoundaryCochains n e :=
  boundaryTransfer n e ≫ boundaryRestriction n e

theorem boundaryProjector_idempotent (n : ℕ) (e : ℤ) :
    boundaryProjector n e ≫ boundaryProjector n e = boundaryProjector n e := by
  unfold boundaryProjector
  rw [Category.assoc,← Category.assoc (boundaryRestriction n e),boundaryRestriction_transfer,
    Category.id_comp]

/-- The full-family stabilizer model receives the actual full-level geometric classes. -/
def fullBoundaryToStabilizerTotal (n : ℕ) (e : ℤ) : fullBoundaryCochains n e ⟶
    SymmetricSpaceBoundaryGeometricCone.stabilizerTotalCochains (restrictedCoefficients n e) :=
  boundaryRestriction n e ≫
    SymmetricSpaceBoundaryGeometricCone.localBoundaryToStabilizerTotal (restrictedCoefficients n e)

end TernaryPoly.SymmetricSpaceBoundaryFull
