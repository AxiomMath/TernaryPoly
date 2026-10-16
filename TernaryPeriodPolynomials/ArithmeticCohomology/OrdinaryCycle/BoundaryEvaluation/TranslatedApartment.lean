module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.BoundaryImage
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.ActionFrames

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence ModThreeGoodAction
open SymmetricSpaceBoundaryFull SymmetricSpaceBoundaryFullTransfer SymmetricSpaceBoundaryMV
open SymmetricSpaceBoundaryIncidenceHomology OrdinaryTopBoundaryComparison OrdinaryApartmentPresentation
open scoped MonoidAlgebra

local instance : HasForget₂ (Rep.{0} ℚ principalSix) Ab :=
  HasForget₂.trans (Rep ℚ principalSix) (ModuleCat ℚ) Ab
local instance : (forget₂ (Rep.{0} ℚ principalSix) Ab).Additive :=
  inferInstanceAs ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).Additive)
local instance : (forget₂ (Rep.{0} ℚ principalSix) Ab).PreservesHomology :=
  inferInstanceAs ((forget₂ (Rep ℚ principalSix) (ModuleCat ℚ) ⋙ forget₂ (ModuleCat ℚ) Ab).PreservesHomology)

/-- Every integral flag action is the literal unrestricted ordinary edge action. -/
theorem integral_flag_action_ordinary (g : IntegralGL) (F : Flag) :
    g • F = OrdinaryFullAction.edgeAction (OrdinaryFullAction.integral g) F := rfl

/-- Full integral transport preserves the literal flag coefficients. -/
theorem integral_edgeCoefficients_action (g : IntegralGL) (c : ℚ[Flag]) :
    edgeCoefficients (fullFlagLabels.ρ g c) =
      OrdinaryFullAction.edgeRepresentation (OrdinaryFullAction.integral g) (edgeCoefficients c) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single F r =>
    change edgeCoefficients (Representation.ofMulAction ℚ IntegralGL Flag g (MonoidAlgebra.single F r)) = _
    rw [Representation.ofMulAction_single, edgeCoefficients_single, edgeCoefficients_single]
    erw [OrdinaryFullAction.edgeRepresentation_single]
    exact congrArg (fun e => Finsupp.single e r) (integral_flag_action_ordinary g F)

/-- The ordinary cycle inclusion respects the actual full integral action, including all flags. -/
theorem integral_ordinaryCycleInclusion_action (g : IntegralGL) (c : OrdinaryIncidenceChains.Cycles) :
    ordinaryCycleInclusion.hom (OrdinaryFullAction.cycleAction (OrdinaryFullAction.integral g) c) =
      fullFlagLabels.ρ g (ordinaryCycleInclusion.hom c) := by
  apply edgeCoefficients.injective
  change edgeCoefficients (edgeCoefficients.symm
      (OrdinaryFullAction.cycleAction (OrdinaryFullAction.integral g) c).val) =
    edgeCoefficients (fullFlagLabels.ρ g (edgeCoefficients.symm c.val))
  rw [edgeCoefficients.apply_symm_apply, integral_edgeCoefficients_action, edgeCoefficients.apply_symm_apply]
  rfl

/-- Every integral translate of the finite apartment is an actual cycle. -/
theorem translatedFiniteApartment_boundary (g : IntegralGL) :
    canonicalFaceCone.d 1 0 ((canonicalFaceCone.X 1).ρ g finiteApartmentChain) = 0 := by
  rw [Rep.hom_comm_apply, finiteApartmentChain_boundary, map_zero]

/-- Integral translates are bundled in the same genuine principal-six cycle object. -/
def translatedFiniteApartmentCycle (g : IntegralGL) :
    (restrictedComplex principalSix canonicalFaceCone).cycles 1 :=
  ((restrictedComplex principalSix canonicalFaceCone).sc 1).cyclesMk
    ((canonicalFaceCone.X 1).ρ g finiteApartmentChain) (by
      change canonicalFaceCone.d 1 ((ComplexShape.down ℕ).next 1) _ = 0
      rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
      exact translatedFiniteApartment_boundary g)

theorem translatedFiniteApartmentCycle_value (g : IntegralGL) :
    (restrictedComplex principalSix canonicalFaceCone).iCycles 1 (translatedFiniteApartmentCycle g) =
      (canonicalFaceCone.X 1).ρ g finiteApartmentChain :=
  ((restrictedComplex principalSix canonicalFaceCone).sc 1).i_cyclesMk _ _

/-- Its corner is the negative literal translated ordinary apartment. -/
theorem translatedFiniteApartmentCycle_corner (g : IntegralGL) :
    restrictedCanonicalCorner ((restrictedComplex principalSix canonicalFaceCone).homologyπ 1
      (translatedFiniteApartmentCycle g)) = -ordinaryCycleInclusion.hom (frameCycle g) := by
  have h := congrArg (fun f => f.hom (translatedFiniteApartmentCycle g))
    (restrictedEvaluation_projection principalSix canonicalFaceCone fullFlagLabels 1
      (coneCornerCochain canonicalFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0))
      (coneCornerCochain_boundary canonicalFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0)
        flagParabolicResolution.complex_d_comp_π_f_zero))
  change restrictedCanonicalCorner ((restrictedComplex principalSix canonicalFaceCone).homologyπ 1
      (translatedFiniteApartmentCycle g)) =
    (coneCornerCochain canonicalFaceArrow fullFlagLabels (flagParabolicResolution.π.f 0)).hom
      ((restrictedComplex principalSix canonicalFaceCone).iCycles 1 (translatedFiniteApartmentCycle g)) at h
  rw [translatedFiniteApartmentCycle_value, Rep.hom_comm_apply,
    finiteApartmentChain_augmentation, map_neg, ← integral_ordinaryCycleInclusion_action] at h
  have hg : OrdinaryFullAction.cycleAction (OrdinaryFullAction.integral g) identityApartment = frameCycle g := by
    change OrdinaryFullAction.cycleAction (OrdinaryFullAction.integral g) (frameCycle 1) = _
    rw [OrdinaryFullAction.frameCycle_equivariant, mul_one]
  rw [hg] at h
  exact h

/-- The actual boundary representative of each translated finite apartment. -/
def translatedFiniteApartmentBoundaryCycle (g : IntegralGL) : boundaryChains.cycles 1 :=
  cyclesMap (coverRestrictionFunctor.map canonicalBoundaryEquiv.inv) 1 (translatedFiniteApartmentCycle g)

/-- Its genuine boundary homology class maps to the exact integral frame apartment. -/
theorem translatedFiniteApartmentBoundaryCycle_class (g : IntegralGL) :
    boundaryH1OrdinaryCyclesIso.hom (boundaryChains.homologyπ 1
      (translatedFiniteApartmentBoundaryCycle g)) = frameCycle g := by
  apply (Rep.mono_iff_injective ordinaryCycleInclusion).mp inferInstance
  have he := congrArg (fun f => f.hom
    ((restrictedComplex principalSix canonicalFaceCone).homologyπ 1 (translatedFiniteApartmentCycle g)))
      restrictedCanonicalBoundary_inverse_edge
  change boundaryEdgeMap (homologyMap (coverRestrictionFunctor.map canonicalBoundaryEquiv.inv) 1
    ((restrictedComplex principalSix canonicalFaceCone).homologyπ 1 (translatedFiniteApartmentCycle g))) =
      -restrictedCanonicalCorner ((restrictedComplex principalSix canonicalFaceCone).homologyπ 1
        (translatedFiniteApartmentCycle g)) at he
  rw [translatedFiniteApartmentCycle_corner, neg_neg] at he
  have hn := congrArg (fun f => f.hom (translatedFiniteApartmentCycle g))
    (homologyπ_naturality (coverRestrictionFunctor.map canonicalBoundaryEquiv.inv) 1)
  change homologyMap (coverRestrictionFunctor.map canonicalBoundaryEquiv.inv) 1
    ((restrictedComplex principalSix canonicalFaceCone).homologyπ 1 (translatedFiniteApartmentCycle g)) =
      boundaryChains.homologyπ 1 (translatedFiniteApartmentBoundaryCycle g) at hn
  rw [hn] at he
  have hi := congrArg (fun f => f.hom (boundaryChains.homologyπ 1
    (translatedFiniteApartmentBoundaryCycle g))) boundaryH1OrdinaryCyclesIso_edge
  exact hi.trans he

end TernaryPoly.OrdinaryBoundaryActualEvaluation
