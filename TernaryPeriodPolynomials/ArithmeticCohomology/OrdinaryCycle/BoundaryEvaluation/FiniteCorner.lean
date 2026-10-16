module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.FiniteCone
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.ReferenceApartment

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory HomologicalComplex Representation SymmetricSpaceBoundaryFull OrdinaryParabolicGroups
open ReferenceCoefficientMatrices SymmetricSpaceBoundaryIncidenceHomology OrdinaryTopBoundaryComparison
open ModThreeGoodAction

/-- The canonical scalar zero-bar retains its precise induced flag label. -/
theorem inducedZero_flag_augmentation (g : ModThreeGoodAction.IntegralGL) :
    (flagParabolicResolution.π.f 0).hom (inducedZero B g) =
      MonoidAlgebra.single (g⁻¹ • standardFlag) (1 : ℚ) := by
  rw [inducedZero, fullParabolicAt_augmentation]
  exact congrArg (fun r : ℚ => MonoidAlgebra.single (g⁻¹ • standardFlag) r)
    (SingularCoverRestriction.barAugmentation_generator default)

/-- For a K induction coordinate the augmented flag is the exact inverse edge translate. -/
theorem inducedZero_flag_edge (g : K) :
    edgeCoefficients ((flagParabolicResolution.π.f 0).hom (inducedZero B g.val)) =
      OrdinaryIncidenceChains.edgeRepresentation g⁻¹ OrdinaryCoordinateFlag.flagChain := by
  rw [inducedZero_flag_augmentation]
  exact fullFlag_single_edge g⁻¹

theorem sK_inv_eq_self : sK⁻¹ = sK := Subtype.ext s_inv_eq_self

theorem cK_inv_eq_sq : cK⁻¹ = cK*cK := Subtype.ext (c_inv_eq_sq.trans (pow_two _))

theorem cK_cube_eq_one : cK*cK*cK = 1 := by
  apply Subtype.ext
  change c*c*c = 1
  simpa only [pow_succ, pow_zero, one_mul] using c_cube

/-- The actual cyclic edge action has order three on all chains. -/
theorem cyclicEdge_triple (x : OrdinaryIncidenceChains.EdgeChains) :
    OrdinaryIncidenceChains.edgeRepresentation cK (OrdinaryIncidenceChains.edgeRepresentation cK
      (OrdinaryIncidenceChains.edgeRepresentation cK x)) = x := by
  change (OrdinaryIncidenceChains.edgeRepresentation cK * OrdinaryIncidenceChains.edgeRepresentation cK *
    OrdinaryIncidenceChains.edgeRepresentation cK) x = x
  rw [← map_mul, ← map_mul, cK_cube_eq_one, map_one, Module.End.one_apply]

/-- The six scalar canonical corners augment to the literal identity-apartment edge chain. -/
theorem finiteApartmentCorner_augmentation :
    (flagParabolicResolution.π.f 0).hom finiteApartmentCorner = ordinaryCycleInclusion.hom identityApartment := by
  apply edgeCoefficients.injective
  change edgeCoefficients ((flagParabolicResolution.π.f 0).hom finiteApartmentCorner) = identityApartment.val
  rw [identityApartment_hexagon]
  unfold finiteApartmentCorner
  repeat' first | erw [map_add] | erw [map_sub]
  change
    (edgeCoefficients ((flagParabolicResolution.π.f 0).hom (inducedZero B (1 : K).val)) -
      edgeCoefficients ((flagParabolicResolution.π.f 0).hom (inducedZero B sK.val))) +
    (edgeCoefficients ((flagParabolicResolution.π.f 0).hom (inducedZero B (cK⁻¹).val)) -
      edgeCoefficients ((flagParabolicResolution.π.f 0).hom (inducedZero B (sK*cK⁻¹).val))) +
    (edgeCoefficients ((flagParabolicResolution.π.f 0).hom (inducedZero B cK.val)) -
      edgeCoefficients ((flagParabolicResolution.π.f 0).hom (inducedZero B (sK*cK).val))) = _
  rw [inducedZero_flag_edge, inducedZero_flag_edge, inducedZero_flag_edge,
    inducedZero_flag_edge, inducedZero_flag_edge, inducedZero_flag_edge]
  simp only [inv_one, mul_inv_rev, sK_inv_eq_self, cK_inv_eq_sq,
    map_one, Module.End.one_apply, map_mul, Module.End.mul_apply, OrdinaryCoordinateApartment.segment]
  rw [cyclicEdge_triple, cyclicEdge_triple]

end TernaryPoly.OrdinaryBoundaryActualEvaluation
