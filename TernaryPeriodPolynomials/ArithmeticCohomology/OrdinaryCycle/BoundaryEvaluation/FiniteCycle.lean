module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.FiniteCorner
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.CanonicalEdge

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex Preadditive BoundaryFaceResolutionComparison
open SymmetricSpaceBoundaryFull SymmetricSpaceBoundaryFullTransfer OrdinaryParabolicGroups
open IntegralGL3Congruence SymmetricSpaceBoundaryIncidenceHomology OrdinaryTopBoundaryComparison

local instance : HasForget₂ (Rep.{0} ℚ principalSix) Ab :=
  HasForget₂.trans (Rep ℚ principalSix) (ModuleCat ℚ) Ab

local instance : (forget₂ (Rep.{0} ℚ principalSix) Ab).Additive :=
  inferInstanceAs ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).Additive)

local instance : (forget₂ (Rep.{0} ℚ principalSix) Ab).PreservesHomology :=
  inferInstanceAs ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).PreservesHomology)

/-- The actual finite chain has precisely the negative of the six-flag corner coordinate. -/
theorem finiteApartmentChain_corner :
    (CofiberSequence.first canonicalFaceArrow 0).hom finiteApartmentChain = -finiteApartmentCorner := by
  have hc : signedCornerInclusion canonicalLineArrow canonicalPlaneArrow 0 ≫
      CofiberSequence.first canonicalFaceArrow 0 = 𝟙 _ :=
    homotopyCofiber.inlX_fstX canonicalFaceArrow 0 1 rfl
  have hl : signedLineInclusion canonicalLineArrow canonicalPlaneArrow 1 ≫
      CofiberSequence.first canonicalFaceArrow 0 = 0 := by
    unfold signedLineInclusion CofiberSequence.first
    erw [Category.assoc, homotopyCofiber.inrX_fstX, comp_zero]
  have hp : signedPlaneInclusion canonicalLineArrow canonicalPlaneArrow 1 ≫
      CofiberSequence.first canonicalFaceArrow 0 = 0 := by
    unfold signedPlaneInclusion CofiberSequence.first
    erw [Category.assoc, homotopyCofiber.inrX_fstX, comp_zero]
  have hca := congrArg (fun f => f.hom finiteApartmentCorner) hc
  have hla := congrArg (fun f => f.hom finiteApartmentLine) hl
  have hpa := congrArg (fun f => f.hom finiteApartmentPlane) hp
  change (CofiberSequence.first canonicalFaceArrow 0).hom
    ((signedCornerInclusion _ _ 0).hom finiteApartmentCorner) = finiteApartmentCorner at hca
  change (CofiberSequence.first canonicalFaceArrow 0).hom
    ((signedLineInclusion _ _ 1).hom finiteApartmentLine) = 0 at hla
  change (CofiberSequence.first canonicalFaceArrow 0).hom
    ((signedPlaneInclusion _ _ 1).hom finiteApartmentPlane) = 0 at hpa
  erw [finiteApartmentChain, map_neg, map_sub, map_add, hca, hla, hpa, add_zero, sub_zero]

/-- The finite chain's corner cochain is the negative literal identity-apartment coefficient. -/
theorem finiteApartmentChain_augmentation :
    (coneCornerCochain canonicalFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0)).hom
      finiteApartmentChain = -ordinaryCycleInclusion.hom identityApartment := by
  change (flagParabolicResolution.π.f 0).hom
    ((CofiberSequence.first canonicalFaceArrow 0).hom finiteApartmentChain) = _
  erw [finiteApartmentChain_corner, map_neg, finiteApartmentCorner_augmentation]
  rfl

/-- The explicit finite chain bundled as a cycle of the genuine principal-six restriction. -/
def finiteApartmentCycle : (restrictedComplex principalSix canonicalFaceCone).cycles 1 :=
  ((restrictedComplex principalSix canonicalFaceCone).sc 1).cyclesMk finiteApartmentChain (by
    change canonicalFaceCone.d 1 ((ComplexShape.down ℕ).next 1) finiteApartmentChain = 0
    rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
    exact finiteApartmentChain_boundary)

theorem finiteApartmentCycle_value :
    (restrictedComplex principalSix canonicalFaceCone).iCycles 1 finiteApartmentCycle = finiteApartmentChain :=
  ((restrictedComplex principalSix canonicalFaceCone).sc 1).i_cyclesMk _ _

/-- Its actual restricted corner homology value is minus the identity apartment. -/
theorem finiteApartmentCycle_corner :
    restrictedCanonicalCorner ((restrictedComplex principalSix canonicalFaceCone).homologyπ 1 finiteApartmentCycle) =
      -ordinaryCycleInclusion.hom identityApartment := by
  have h := congrArg (fun f => f.hom finiteApartmentCycle)
    (restrictedEvaluation_projection principalSix canonicalFaceCone fullFlagLabels 1
      (coneCornerCochain canonicalFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0))
      (coneCornerCochain_boundary canonicalFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0)
        flagParabolicResolution.complex_d_comp_π_f_zero))
  change restrictedCanonicalCorner ((restrictedComplex principalSix canonicalFaceCone).homologyπ 1 finiteApartmentCycle) =
    (coneCornerCochain canonicalFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0)).hom
      ((restrictedComplex principalSix canonicalFaceCone).iCycles 1 finiteApartmentCycle) at h
  rw [finiteApartmentCycle_value, finiteApartmentChain_augmentation] at h
  exact h

/-- The actual boundary cycle obtained by the canonical geometric inverse. -/
def finiteApartmentBoundaryCycle : boundaryChains.cycles 1 :=
  cyclesMap (coverRestrictionFunctor.map canonicalBoundaryEquiv.inv) 1 finiteApartmentCycle

/-- The identity-apartment boundary class has its literal ordinary edge coefficients. -/
theorem identityApartmentBoundaryClass_edge :
    boundaryEdgeMap identityApartmentBoundaryClass = ordinaryCycleInclusion.hom identityApartment := by
  have h := congrArg (fun f => f.hom identityApartment)
    (Iso.inv_hom_id_assoc boundaryH1OrdinaryCyclesIso ordinaryCycleInclusion)
  rw [boundaryH1OrdinaryCyclesIso_edge] at h
  exact h

/-- The finite twelve-term canonical cone cycle represents precisely the actual identity apartment. -/
theorem finiteApartmentBoundaryCycle_class :
    boundaryChains.homologyπ 1 finiteApartmentBoundaryCycle = identityApartmentBoundaryClass := by
  have hm : Mono boundaryEdgeMap := by
    rw [← boundaryH1OrdinaryCyclesIso_edge]
    infer_instance
  apply (Rep.mono_iff_injective boundaryEdgeMap).mp hm
  have he := congrArg (fun f => f.hom
    ((restrictedComplex principalSix canonicalFaceCone).homologyπ 1 finiteApartmentCycle))
      restrictedCanonicalBoundary_inverse_edge
  change boundaryEdgeMap (homologyMap (coverRestrictionFunctor.map canonicalBoundaryEquiv.inv) 1
    ((restrictedComplex principalSix canonicalFaceCone).homologyπ 1 finiteApartmentCycle)) =
      -restrictedCanonicalCorner ((restrictedComplex principalSix canonicalFaceCone).homologyπ 1 finiteApartmentCycle) at he
  rw [finiteApartmentCycle_corner, neg_neg] at he
  have hn := congrArg (fun f => f.hom finiteApartmentCycle)
    (homologyπ_naturality (coverRestrictionFunctor.map canonicalBoundaryEquiv.inv) 1)
  change homologyMap (coverRestrictionFunctor.map canonicalBoundaryEquiv.inv) 1
    ((restrictedComplex principalSix canonicalFaceCone).homologyπ 1 finiteApartmentCycle) =
      boundaryChains.homologyπ 1 finiteApartmentBoundaryCycle at hn
  rw [hn, ← identityApartmentBoundaryClass_edge] at he
  exact he

end TernaryPoly.OrdinaryBoundaryActualEvaluation
