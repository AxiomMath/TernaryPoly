module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonApartment
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.Duality

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory HomologicalComplex IntegralGL3Congruence
open SingularBoundaryRestriction SingularLocalHomology SymmetricSpaceBoundaryDuality
open SymmetricSpaceBoundaryManifold SymmetricSpaceBoundaryOrientation SymmetricSpaceRelativeCapConnecting
open OrdinaryTopBoundaryComparison

variable (W : Rep.{0} ℚ principalSix)

/-- The actual boundary cohomology class enters the canonical ordinary-functional space via
the genuine connecting morphism and the literal relative Hom comparison. -/
def boundaryCohomologyOrdinary :
    (SingularLocalCoefficient.localCochains boundaryProjection boundaryQuotientCovering W).homology 1 ⟶
      ordinaryFunctionals W :=
  geometricBoundaryConnecting W 1 ≫ homologyMap (relativeHomGeometricIso W).inv 2 ≫
    (relativeOrdinaryCohomologyIso W).hom

/-- Under actual relative fundamental cap, ordinary evaluation retains the inverse
geometric-to-Hom cochain comparison. -/
theorem relativeCap_groupOrdinary :
    relativeFundamentalCap W ≫ (bordifiedGroupLocalHomologyIso W 3).inv ≫
      (groupOrdinaryIso W).hom =
    homologyMap (relativeHomGeometricIso W).inv 2 ≫ (relativeOrdinaryCohomologyIso W).hom := by
  have h := cappedClass_groupOrdinary W
  rw [relativeHomCapIso_hom] at h
  apply (cancel_epi (homologyMap (relativeHomGeometricIso W).hom 2)).mp
  erw [← Category.assoc, ← Category.assoc, h, ← Category.assoc, ← homologyMap_comp,
    Iso.hom_inv_id, homologyMap_id, Category.id_comp]

/-- The entire actual boundary H3 image maps to exactly the actual boundary connecting class.
The positive sign is the sign proved in the geometric fundamental cap square. -/
theorem boundary_groupOrdinary_square :
    (boundaryH1CapIso W boundaryOrientation).hom ≫ boundaryToGroup W 3 ≫
      (groupOrdinaryIso W).hom = boundaryCohomologyOrdinary W := by
  change (boundaryH1CapIso W boundaryOrientation).hom ≫
    (homologyMap (boundaryInclusionMap W) 3 ≫ (bordifiedGroupLocalHomologyIso W 3).inv) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, ordinary_cap_connecting,
    Category.assoc, Category.assoc, relativeCap_groupOrdinary]
  rfl

/-- An arbitrary genuine whole-boundary homology class has the specified actual
ordinary-functional image, without asserting that every top class is boundary. -/
theorem boundaryToGroup_ordinary :
    boundaryToGroup W 3 ≫ (groupOrdinaryIso W).hom =
      (boundaryH1CapIso W boundaryOrientation).inv ≫ boundaryCohomologyOrdinary W := by
  rw [← boundary_groupOrdinary_square, Iso.inv_hom_id_assoc]

/-- Literal identity-apartment evaluation of the entire genuine boundary image. -/
theorem boundaryToGroup_apartment :
    boundaryToGroup W 3 ≫ groupApartmentEvaluation W =
      (boundaryH1CapIso W boundaryOrientation).inv ≫ boundaryCohomologyOrdinary W ≫
        identityApartmentEvaluation W := by
  rw [groupApartmentEvaluation, ← Category.assoc, boundaryToGroup_ordinary, Category.assoc]

end TernaryPoly.OrdinaryBoundaryActualEvaluation
