module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.Geometric

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open EquivariantSingularSmall SingularBoundaryRestriction SingularLocalCoefficient SingularLocalHomology
open SymmetricSpaceBoundaryManifold SymmetricSpaceBoundaryOrientation SymmetricSpaceBoundaryDuality
open SymmetricSpaceBoundaryIncidenceHomology OrdinaryTopBoundaryComparison

variable (W : Rep.{0} ℚ principalSix)

/-- Actual equivariant and geometric boundary H1 are identified by the literal covering cochain iso. -/
def boundaryCohomologyIso : (homCochains boundaryChains W).homology 1 ≅
    (localCochains boundaryProjection boundaryQuotientCovering W).homology 1 :=
  (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) 1).mapIso
    (cochainIso boundaryProjection boundaryQuotientCovering W)

/-- The whole-boundary image's ordinary functional is the direct actual boundary evaluator
applied to the inverse genuine cap and covering comparisons. -/
theorem boundaryToGroup_direct :
    boundaryToGroup W 3 ≫ (groupOrdinaryIso W).hom =
      (boundaryH1CapIso W boundaryOrientation).inv ≫ (boundaryCohomologyIso W).inv ≫
        boundaryOrdinaryEvaluation W := by
  have h : boundaryCohomologyOrdinary W =
      (boundaryCohomologyIso W).inv ≫ boundaryOrdinaryEvaluation W := by
    apply (cancel_epi (boundaryCohomologyIso W).hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact boundaryCohomologyOrdinary_equivariant W
  rw [boundaryToGroup_ordinary, h]

/-- Literal identity-apartment evaluation of every genuine boundary H3 image, with no
assumption that all arithmetic top classes come from the boundary. -/
theorem boundary_image_apartment (b : (boundaryLocalChains W).homology 3) :
    groupApartmentEvaluation W (boundaryToGroup W 3 b) =
      (homologyEvaluation boundaryChains W 1
        ((boundaryCohomologyIso W).inv ((boundaryH1CapIso W boundaryOrientation).inv b))).hom
          identityApartmentBoundaryClass := by
  have h := congrArg (fun f => f b) (boundaryToGroup_direct W)
  change (groupOrdinaryIso W).hom (boundaryToGroup W 3 b) =
    boundaryOrdinaryEvaluation W
      ((boundaryCohomologyIso W).inv ((boundaryH1CapIso W boundaryOrientation).inv b)) at h
  change identityApartmentEvaluation W ((groupOrdinaryIso W).hom (boundaryToGroup W 3 b)) = _
  rw [h]
  rfl

/-- For any actual representative of the identity-apartment boundary class, the capped
boundary evaluator is literally the original cocycle applied to that representative. -/
theorem cappedBoundary_cocycle_evaluation (x : (homCochains boundaryChains W).cycles 1)
    (z : boundaryChains.cycles 1) (hz : boundaryChains.homologyπ 1 z = identityApartmentBoundaryClass) :
    groupApartmentEvaluation W (boundaryToGroup W 3
      ((boundaryH1CapIso W boundaryOrientation).hom ((boundaryCohomologyIso W).hom
        ((homCochains boundaryChains W).homologyπ 1 x)))) =
      (cocycleValue boundaryChains W 1 x).hom (boundaryChains.iCycles 1 z) := by
  rw [boundary_image_apartment]
  have hb := congrArg (fun f => f ((boundaryCohomologyIso W).hom
    ((homCochains boundaryChains W).homologyπ 1 x)))
    (boundaryH1CapIso W boundaryOrientation).hom_inv_id
  have hc := congrArg (fun f => f ((homCochains boundaryChains W).homologyπ 1 x))
    (boundaryCohomologyIso W).hom_inv_id
  change (boundaryH1CapIso W boundaryOrientation).inv
    ((boundaryH1CapIso W boundaryOrientation).hom ((boundaryCohomologyIso W).hom
      ((homCochains boundaryChains W).homologyπ 1 x))) = _ at hb
  change (boundaryCohomologyIso W).inv ((boundaryCohomologyIso W).hom
    ((homCochains boundaryChains W).homologyπ 1 x)) = _ at hc
  simp only [ModuleCat.id_apply] at hb hc
  rw [hb, hc, ← hz]
  exact homologyEvaluation_apply boundaryChains W 1 x z

end TernaryPoly.OrdinaryBoundaryActualEvaluation
