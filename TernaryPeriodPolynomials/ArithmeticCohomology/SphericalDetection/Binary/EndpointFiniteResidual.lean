module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.FiniteDetection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.BoundaryLift

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspIntegralWeightValues_spherical (cusp : CuspidalRepresentation) (weight : ℤ)
    (vector : cuspAffineSmoothValues cusp)
    (member : vector ∈ cuspFiniteWeightValues cusp (finiteIntegralGLLevel 2) weight) :
    vector.val ∈ cuspSphericalValues cusp := by
  intro compact
  exact member.1 ⟨GeneralLinearGroup.map integralEmbedding compact, ⟨compact, rfl⟩⟩

theorem cuspIntegralExtremal_exists_classical (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cuspAffineSmoothValues cusp)
    (member : vector ∈ cuspFiniteWeightValues cusp (finiteIntegralGLLevel 2) (2 * halfWeight))
    (killed : cuspRaisingOperator cusp (2 * halfWeight) vector = 0) :
    ∃ classicalVector : cuspClassicalVectors cusp halfWeight, classicalVector.val.val = vector.val := by
  have fixed := cuspIntegralWeightValues_spherical cusp (2 * halfWeight) vector member
  have regular := vector.property.differentiableOn (by simp)
  have raising_zero : cuspRaisingVector cusp (2 * halfWeight) vector.val = 0 := congrArg Subtype.val killed
  have smooth := cuspSphericalWeight_smooth_of_raising_zero cusp spherical central_positive vector.val
    halfWeight member.2 fixed regular raising_zero
  let smoothVector : cusp.smooth := ⟨vector.val, smooth⟩
  have holomorphic := cuspWeightedAffineOrbit_holomorphic cusp halfWeight vector.val regular raising_zero
  refine ⟨⟨smoothVector, cuspClassicalVectors_mem_of_holomorphic cusp halfWeight smoothVector fixed member.2 ?_⟩, rfl⟩
  exact cuspScalarWeightedRealization_holomorphic cusp halfWeight smoothVector fixed member.2 holomorphic 1

theorem binaryNormalForm_lower_residual_classical (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (degree : ℕ) (halfWeight : ℤ) (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (lower upper : binarySmoothValues cusp (Fin (degree + 2)))
    (lower_mem : ∀ position, lower position ∈
      cuspFiniteWeightValues cusp (finiteIntegralGLLevel 2) (binaryUnitaryWeight degree (-2) position))
    (closed : binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) (-2) lower =
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 2 upper)
    (support : ∀ position : Fin (degree + 1), lower position.succ = 0)
    (boundary : cuspFiniteWeightValues cusp (finiteIntegralGLLevel 2) (degree + 1 : ℕ))
    (upper_lift : cuspRaisingOperator cusp (degree + 1 : ℕ) boundary.val = upper (Fin.last (degree + 1))) :
    ∃ vector : cuspClassicalVectors cusp halfWeight,
      vector.val.val = (lower 0 - binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0
        (binaryRelativeBoundaryLift cusp degree (finiteIntegralGLLevel 2) boundary) 0).val := by
  let primitive := binaryRelativeBoundaryLift cusp degree (finiteIntegralGLLevel 2) boundary
  obtain ⟨last, primitive_mem, primitive_support⟩ := binaryRelativeBoundaryLift_spec cusp degree (finiteIntegralGLLevel 2) boundary
  change primitive (Fin.last (degree + 1)) = boundary.val at last
  let new_lower := lower - binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0 primitive
  let new_upper := upper - binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) 0 primitive
  have new_closed := binaryRelativeLadder_shift cusp (binaryWeightBasis (degree + 1)) lower upper primitive closed
  have new_support (position : Fin (degree + 1)) : new_lower position.succ = 0 := by
    change lower position.succ - binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0 primitive position.succ = 0
    rw [support, primitive_support, sub_self]
  have endpoint_zero : new_upper (Fin.last (degree + 1)) = 0 := by
    change upper (Fin.last (degree + 1)) - binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) 0
      primitive (Fin.last (degree + 1)) = 0
    rw [binaryRelativeRaising_last, zero_add, last, upper_lift, sub_self]
  have upper_zero := binaryRelative_normal_form_upper_zero cusp degree new_lower new_upper new_closed new_support endpoint_zero
  have weight_zero : binaryUnitaryWeight degree (-2) 0 = 2 * halfWeight := by
    simp only [binaryUnitaryWeight, Fin.val_zero, Nat.cast_zero, mul_zero, add_zero]
    omega
  have member : new_lower 0 ∈ cuspFiniteWeightValues cusp (finiteIntegralGLLevel 2) (2 * halfWeight) := by
    rw [← weight_zero]
    exact Submodule.sub_mem _ (lower_mem 0)
      (binaryRelativeLowering_mem cusp degree (finiteIntegralGLLevel 2) 0 primitive primitive_mem 0)
  have killed : cuspRaisingOperator cusp (2 * halfWeight) (new_lower 0) = 0 := by
    have equation := (binaryRelative_normal_form_equations cusp degree new_lower new_upper new_closed new_support).1
    have target_weight : -2 - ((degree + 1 : ℕ) : ℤ) = 2 * halfWeight := by omega
    rw [upper_zero, Pi.zero_apply, map_zero, target_weight] at equation
    exact equation
  exact cuspIntegralExtremal_exists_classical cusp spherical central_positive halfWeight (new_lower 0) member killed

theorem binaryNormalForm_lower_endpoint_iff_finite_residual (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (large : 3 < degree)
    (cohomological : Cohomological cusp degree) (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (lower : binarySmoothValues cusp (Fin (degree + 2)))
    (boundary : cuspFiniteWeightValues cusp (finiteIntegralGLLevel 2) (degree + 1 : ℕ))
    (vector : cuspClassicalVectors cusp halfWeight)
    (residual : vector.val.val = (lower 0 - binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0
      (binaryRelativeBoundaryLift cusp degree (finiteIntegralGLLevel 2) boundary) 0).val) :
    binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0
      (binaryRelativeBoundaryLift cusp degree (finiteIntegralGLLevel 2) boundary) 0 = lower 0 ↔
      ∀ real : BinaryRealGL, goodLineFiniteVectorIntegral degree cusp cohomologicalPoint
        (cuspSmoothAction cusp (atInfinity real) vector.val) = 0 := by
  have endpoint_iff : binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 0
      (binaryRelativeBoundaryLift cusp degree (finiteIntegralGLLevel 2) boundary) 0 = lower 0 ↔ vector.val = 0 := by
    constructor
    · intro equal
      apply Subtype.ext
      rw [residual, equal, sub_self]
      rfl
    · intro zero
      have value_zero := (congrArg Subtype.val zero).symm.trans residual
      exact (sub_eq_zero.mp (Subtype.ext value_zero.symm)).symm
  rw [endpoint_iff]
  constructor
  · intro zero real
    rw [zero, map_zero]
    unfold goodLineFiniteVectorIntegral
    simp
  · exact goodLineFiniteVectorIntegral_classical_detects cusp
      (cohomological_centralCharacter_positive cusp cohomological) spherical large cohomological
      halfWeight weight vector.val vector.property

end TernaryPeriodPolynomials.SphericalDetection.Helpers
