module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.BoundaryEvaluation.FinitePairwise

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryBoundaryActualEvaluation
open CategoryTheory Limits HomologicalComplex SymmetricSpaceBoundaryFull OrdinaryParabolicGroups OrdinaryBoundaryCone

variable (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL)

/-- An ordinary gauge is the literal canonical cone coboundary under the actual coordinate isomorphism. -/
theorem canonicalGauge_cochain (b : canonicalFaceCone.X 1 ⟶ W) (v : C0 W) :
    (ordinaryCoordinates1 W).symm (ordinaryCoordinates1 W b - d0 W P Q v) =
      b - canonicalFaceCone.d 1 0 ≫ (ordinaryCoordinates0 W).symm v := by
  apply (ordinaryCoordinates1 W).injective
  rw [LinearEquiv.apply_symm_apply, map_sub, ordinaryCoordinates_d0, LinearEquiv.apply_symm_apply]

/-- The finite scalar cone cycle annihilates every actual ordinary gauge term. -/
theorem canonicalGauge_finite_evaluation (b : canonicalFaceCone.X 1 ⟶ W) (v : C0 W) :
    ((ordinaryCoordinates1 W).symm (ordinaryCoordinates1 W b - d0 W P Q v)).hom finiteApartmentChain =
      b.hom finiteApartmentChain := by
  rw [canonicalGauge_cochain]
  change b.hom finiteApartmentChain -
    ((ordinaryCoordinates0 W).symm v).hom (canonicalFaceCone.d 1 0 finiteApartmentChain) = _
  rw [finiteApartmentChain_boundary, map_zero, sub_zero]

/-- The actual full coefficient normal form controls evaluation on the explicit finite apartment cycle. -/
theorem canonicalCocycle_finite_pairwise (n : ℕ) (e : ℤ)
    (b : canonicalFaceCone.X 1 ⟶ actualCoefficients n e)
    (hb : canonicalFaceCone.d 2 1 ≫ b = 0) :
    coefficientPairwise n (b.hom finiteApartmentChain) := by
  let z : actualCycles n e := ⟨ordinaryCoordinates1 (actualCoefficients n e) b, by
    change d1 (actualCoefficients n e) P Q (ordinaryCoordinates1 (actualCoefficients n e) b) = 0
    rw [← ordinaryCoordinates_d1, hb, map_zero]⟩
  obtain ⟨z', hz', hp, hq, hc⟩ := actual_class_pairwise_representative n e
    (classOf (actualCoefficients n e) P Q z)
  obtain ⟨v, hv⟩ := (classOf_eq_iff (actualCoefficients n e) P Q z' z).mp hz'
  have hv' : z'.val = ordinaryCoordinates1 (actualCoefficients n e) b -
      d0 (actualCoefficients n e) P Q v := congrArg Subtype.val hv
  let b' := (ordinaryCoordinates1 (actualCoefficients n e)).symm z'.val
  have hcoord : ordinaryCoordinates1 (actualCoefficients n e) b' = z'.val :=
    (ordinaryCoordinates1 (actualCoefficients n e)).apply_symm_apply _
  have heval : b'.hom finiteApartmentChain = b.hom finiteApartmentChain := by
    dsimp [b']
    rw [hv', canonicalGauge_finite_evaluation]
  rw [← heval]
  apply finiteApartmentChain_pairwise n e b'
  · rw [hcoord]
    exact hp
  · rw [hcoord]
    exact hq
  · rw [hcoord]
    exact hc

/-- Every actual full-boundary cocycle evaluates the finite identity apartment with pairwise distinguished support. -/
theorem fullBoundaryCocycle_finite_pairwise (n : ℕ) (e : ℤ)
    (b : fullBoundaryChains.X 1 ⟶ actualCoefficients n e)
    (hb : fullBoundaryChains.d 2 1 ≫ b = 0) :
    coefficientPairwise n (b.hom ((canonicalBoundaryEquiv.inv.f 1).hom finiteApartmentChain)) := by
  apply canonicalCocycle_finite_pairwise n e (canonicalBoundaryEquiv.inv.f 1 ≫ b)
  rw [← Category.assoc, ← canonicalBoundaryEquiv.inv.comm 2 1, Category.assoc, hb, comp_zero]

end TernaryPoly.OrdinaryBoundaryActualEvaluation
