module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.MonomialLadder

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspPolynomialLift TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientCoordinates TernaryPeriodPolynomials.PlaneEisensteinContinuation.CoefficientTensor
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialCoordinates TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialWeights

def weight (degree : ℕ) (target : ℤ) (position : ℕ) : ℤ := target + position - (degree + 1 - position : ℕ)

theorem weight_succ (degree position : ℕ) (bound : position + 1 ≤ degree + 1) :
    weight degree 0 (position + 1) = weight degree 0 position + 2 := by
  unfold weight
  omega

theorem weight_target (degree position : ℕ) (target : ℤ) :
    weight degree target position = weight degree 0 position + target := by
  unfold weight
  omega

theorem weight_last (degree : ℕ) (target : ℤ) : weight degree target (degree + 1) = target + degree + 1 := by
  simp [weight]
  omega

theorem component_eigen (data : CuspidalRepresentation) (degree position : ℕ) (target : ℤ)
    (bound : position ≤ degree + 1) (vectors : Vectors data degree)
    (eigen : CoefficientRotation.shifted data degree target vectors = 0) :
    rotationOperator data (component data degree position vectors) =
      (Complex.I * weight degree target position) • component data degree position vectors := by
  have fullEigen : CoefficientInfinitesimal.operator data degree rotationMatrix vectors = (Complex.I * target) • vectors :=
    sub_eq_zero.mp eigen
  have equality := congrArg (fun tuple : Vectors data degree => fromMonomials data degree tuple (indexOf degree position bound)) fullEigen
  rw [fromMonomials_rotation, map_smul, Pi.smul_apply] at equality
  dsimp only at equality
  rw [indexOf_zero, indexOf_one] at equality
  rw [component_apply data degree position bound]
  calc
    _ = (Complex.I * target) • fromMonomials data degree vectors (indexOf degree position bound) -
        (Complex.I * (((degree + 1 - position : ℕ) : ℂ) - position)) •
          fromMonomials data degree vectors (indexOf degree position bound) := eq_sub_of_add_eq equality
    _ = _ := by
      simp only [weight, Int.cast_sub, Int.cast_add, Int.cast_natCast]
      module

theorem assemble_eigen (data : CuspidalRepresentation) (degree : ℕ) (target : ℤ) (family : ℕ → data.smooth)
    (eigen : ∀ position, position ≤ degree + 1 → rotationOperator data (family position) =
      (Complex.I * weight degree target position) • family position) :
    CoefficientRotation.shifted data degree target (assemble data degree family) = 0 := by
  change CoefficientRotation.shifted data degree target (toMonomials data degree (fun index => family (index.val 0))) = 0
  rw [CoefficientRotation.shifted_toMonomials]
  have coordinates : (fun index : Index (degree + 1) => rotationOperator data (family (index.val 0)) -
      (Complex.I * CoefficientRotation.weight degree target index) • family (index.val 0)) = 0 := by
    funext index
    have other : degree + 1 - index.val 0 = index.val 1 := by have := index_degree (degree + 1) index; omega
    have sameWeight : weight degree target (index.val 0) = CoefficientRotation.weight degree target index := by
      simp only [weight, other, CoefficientRotation.weight]
    rw [eigen (index.val 0) (position_bound degree index), sameWeight, sub_self]
    rfl
  rw [coordinates, map_zero]

theorem basis_eigen (data : CuspidalRepresentation) (degree position : ℕ) (target : ℤ)
    (bound : position ≤ degree + 1) (vector : data.smooth)
    (eigen : rotationOperator data vector = (Complex.I * weight degree target position) • vector) :
    CoefficientRotation.shifted data degree target (basisVector data degree position vector) = 0 := by
  change CoefficientInfinitesimal.operator data degree rotationMatrix (tensor data degree _ vector) -
    (Complex.I * target) • tensor data degree _ vector = 0
  rw [rotation_tensor data degree position (degree + 1 - position) (by omega), eigen, tensor_vector_smul]
  simp only [weight, Int.cast_sub, Int.cast_add, Int.cast_natCast]
  module

theorem basis_fixed (data : CuspidalRepresentation) (degree position : ℕ) (vector : data.smooth)
    (level : Subgroup BinaryFiniteGL) (fixed : vector.val ∈ BinaryLevel.fixedSubspace data level)
    (index : Index (degree + 1)) : (basisVector data degree position vector index).val ∈ BinaryLevel.fixedSubspace data level :=
  (BinaryLevel.fixedSubspace data level).smul_mem _ fixed

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.MonomialWeights
