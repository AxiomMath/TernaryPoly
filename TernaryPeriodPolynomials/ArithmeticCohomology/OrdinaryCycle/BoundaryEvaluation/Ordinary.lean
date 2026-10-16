module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.ConnectingPairing

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open EquivariantSingularSmall SingularBoundaryRestriction SymmetricSpaceBoundaryIncidenceHomology
open OrdinaryTopBoundaryComparison

variable (W : Rep.{0} ℚ principalSix)

/-- Boundary H1 cohomology evaluates on actual ordinary cycles through the literal boundary
MV isomorphism. No exactness assertion for all boundary Hom degrees is used. -/
def boundaryOrdinaryEvaluation : (homCochains boundaryChains W).homology 1 ⟶ ordinaryFunctionals W :=
  homologyEvaluation boundaryChains W 1 ≫ ModuleCat.ofHom {
    toFun := fun φ => boundaryH1OrdinaryCyclesIso.inv ≫ φ
    map_add' := fun _ _ => by simp only [Preadditive.comp_add]
    map_smul' := fun _ _ => by simp only [Linear.comp_smul, RingHom.id_apply] }

/-- Literal evaluation of a represented boundary cocycle on ordinary cycles. -/
theorem boundaryOrdinaryEvaluation_cycle (x : (homCochains boundaryChains W).cycles 1) :
    boundaryOrdinaryEvaluation W ((homCochains boundaryChains W).homologyπ 1 x) =
      boundaryH1OrdinaryCyclesIso.inv ≫ cocycleEvaluation boundaryChains W 1 x := by
  have h := congrArg (fun f => f x) (homologyEvaluation_projection boundaryChains W 1)
  change homologyEvaluation boundaryChains W 1 ((homCochains boundaryChains W).homologyπ 1 x) =
    cocycleEvaluation boundaryChains W 1 x at h
  change boundaryH1OrdinaryCyclesIso.inv ≫
    homologyEvaluation boundaryChains W 1 ((homCochains boundaryChains W).homologyπ 1 x) = _
  rw [h]

/-- The relative connecting cocycle has exactly the boundary ordinary functional. -/
theorem connectingCocycle_ordinary (x : (homCochains boundaryChains W).cycles 1) :
    (relativeOrdinaryCohomologyIso W).hom
      ((homCochains upstairsRelativeChains W).homologyπ 2 (relativeConnectingCocycle W x)) =
        boundaryOrdinaryEvaluation W ((homCochains boundaryChains W).homologyπ 1 x) := by
  rw [relativeOrdinaryCohomologyIso_apply, boundaryOrdinaryEvaluation_cycle]
  have he := congrArg (fun f => f (relativeConnectingCocycle W x))
    (homologyEvaluation_projection upstairsRelativeChains W 2)
  change homologyEvaluation upstairsRelativeChains W 2
      ((homCochains upstairsRelativeChains W).homologyπ 2 (relativeConnectingCocycle W x)) =
    cocycleEvaluation upstairsRelativeChains W 2 (relativeConnectingCocycle W x) at he
  rw [he, relativeConnectingCocycle_evaluation]
  change (boundaryH1OrdinaryCyclesIso.inv ≫ upstairsRelativeH2BoundaryIso.inv) ≫
    (upstairsRelativeH2BoundaryIso.hom ≫ cocycleEvaluation boundaryChains W 1 x) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]

/-- Canonical relative ordinary evaluation intertwines the actual equivariant boundary
cohomology connecting map with direct evaluation of boundary H1 cohomology. -/
theorem boundaryConnecting_ordinary :
    boundaryConnecting W 1 ≫ homologyMap (relativeHomKernelIso W).inv 2 ≫
      (relativeOrdinaryCohomologyIso W).hom = boundaryOrdinaryEvaluation W := by
  apply (cancel_epi ((homCochains boundaryChains W).homologyπ 1)).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (relativeOrdinaryCohomologyIso W).hom (homologyMap (relativeHomKernelIso W).inv 2
      (boundaryConnecting W 1 ((homCochains boundaryChains W).homologyπ 1 x))) = _
  rw [relativeConnectingCocycle_class]
  have h : homologyMap (relativeHomKernelIso W).hom 2 ≫
      homologyMap (relativeHomKernelIso W).inv 2 = 𝟙 _ := by
    rw [← homologyMap_comp, Iso.hom_inv_id, homologyMap_id]
  have hc := congrArg (fun f => f
    ((homCochains upstairsRelativeChains W).homologyπ 2 (relativeConnectingCocycle W x))) h
  change homologyMap (relativeHomKernelIso W).inv 2
      (homologyMap (relativeHomKernelIso W).hom 2
        ((homCochains upstairsRelativeChains W).homologyπ 2 (relativeConnectingCocycle W x))) =
      (homCochains upstairsRelativeChains W).homologyπ 2 (relativeConnectingCocycle W x) at hc
  rw [hc]
  exact connectingCocycle_ordinary W x

end TernaryPoly.OrdinaryBoundaryActualEvaluation
