module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneMixedCocycles
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Cohomology

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realUpperCuspidalBinaryCoordinate_boundary (degree : ℕ) (cusp : CuspidalRepresentation)
    (potential : realUpperCuspidalRep degree cusp) :
    realUpperCuspidalBinaryCoordinate degree cusp (oneBoundaryCycle (realUpperCuspidalRep degree cusp) potential) = 0 := by
  apply Subtype.ext
  funext argument
  apply Subtype.ext
  rw [realUpperCuspidalBinaryCoordinate_value]
  have projected (coordinate : Fin 2) :
      binaryPolynomialRestrict
        ((oneBoundaryCycle (realUpperCuspidalRep degree cusp) potential (realRadicalAxis coordinate 1)).val argument).val = 0 := by
    have equality := binaryHomogeneousRestrict_realUpper degree (realRadicalAxis coordinate 1) (potential.val argument)
    have difference := (binaryHomogeneousRestrict degree).map_sub
      ((realUpperRadicalRep degree).ρ (realRadicalAxis coordinate 1) (potential.val argument)) (potential.val argument)
    rw [equality, sub_self] at difference
    exact congrArg Subtype.val difference
  rw [projected, projected, mul_zero, mul_zero, add_zero, smul_zero]
  rfl

def realPlaneBinaryCochain (degree : ℕ) (cusp : CuspidalRepresentation)
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (matrix : BinaryRealGL) : cuspidalTensorValues cusp (Binary.HomogeneousPoly (degree + 1)) :=
  realUpperCuspidalBinaryCoordinate degree cusp (realPlaneMixedCocycle degree cusp matrix cycle)

theorem realPlaneBinaryCochain_cocycle {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (regular : ∀ matrix coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
        (realPlaneMixedCocycle degree cusp matrix cycle (realRadicalAxis coordinate parameter))) 0)
    (first second : BinaryRealGL) (argument : BinaryAdelicGL) :
    (realPlaneBinaryCochain degree cusp cycle (first * second)).val argument =
      (realPlaneBinaryCochain degree cusp cycle first).val argument +
        binaryCohomologicalAction degree first (realPlaneBinaryCochain degree cusp cycle second).val argument := by
  unfold realPlaneBinaryCochain
  rw [realPlaneMixedCocycle_mul, map_add, map_add,
    realUpperCuspidalBinaryCoordinate_boundary degree cusp
      (cycle.val (SemidirectProduct.inr first, SemidirectProduct.inr second)), add_zero]
  change (realUpperCuspidalBinaryCoordinate degree cusp
      (realUpperCuspidalCocycleLevi degree cusp first (realPlaneMixedCocycle degree cusp second cycle))).val argument +
      (realUpperCuspidalBinaryCoordinate degree cusp (realPlaneMixedCocycle degree cusp first cycle)).val argument = _
  rw [realUpperCuspidalBinaryCoordinate_equivariant degree cusp basis first
    (realPlaneMixedCocycle degree cusp second cycle) (regular second)]
  exact add_comm _ _

def realPlaneBinaryCocycle {index : Type} [Fintype index]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneCuspidalRep degree cusp trivialCharacter))
    (regular : ∀ matrix coordinate, DifferentiableAt ℝ
      (fun parameter => cuspidalTensorHilbertEmbedding cusp basis
        (realPlaneMixedCocycle degree cusp matrix cycle (realRadicalAxis coordinate parameter))) 0) :
    groupCohomology.cocycles₁ (binaryCuspidalRep cusp degree) :=
  binaryCocycleToGroupCocycle cusp (fun matrix => (realPlaneBinaryCochain degree cusp cycle matrix).val)
    (fun matrix => (cuspidalTensorValues_binary_iff cusp degree _).mp
      (realPlaneBinaryCochain degree cusp cycle matrix).property)
    (realPlaneBinaryCochain_cocycle degree cusp basis cycle regular)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
