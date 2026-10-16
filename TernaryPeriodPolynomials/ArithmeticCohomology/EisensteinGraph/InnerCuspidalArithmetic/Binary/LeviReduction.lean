module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ExplicitBinaryAction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

theorem binaryLeviCrossed_scalar_zero (degree : ℕ)
    (cochain : crossedCocycles (binaryLeviRepresentation degree)) (scalar : ℤˣ) :
    cochain.val (scalar, 1) = 0 := by
  have identity := cochain.property (scalar, 1) (scalar, 1)
  change cochain.val (scalar * scalar, 1 * 1) = cochain.val (scalar, 1) +
    binaryArithmeticRepresentation degree 1 (cochain.val (scalar, 1)) at identity
  rw [Int.units_mul_self, one_mul, map_one, Module.End.one_apply] at identity
  have oneZero : cochain.val (1, 1) = 0 := crossedCocycle_one _ cochain
  rw [oneZero] at identity
  have twice : (2 : ℂ) • cochain.val (scalar, 1) = 0 := by
    rw [two_smul]
    exact identity.symm
  exact (smul_eq_zero.mp twice).resolve_left (by norm_num)

theorem binaryLeviCrossed_factor (degree : ℕ)
    (cochain : crossedCocycles (binaryLeviRepresentation degree))
    (element : ℤˣ × binaryArithmeticLevel) : cochain.val element = cochain.val (1, element.2) := by
  have identity := cochain.property (element.1, 1) (1, element.2)
  change cochain.val (element.1 * 1, 1 * element.2) = cochain.val (element.1, 1) +
    binaryArithmeticRepresentation degree 1 (cochain.val (1, element.2)) at identity
  simpa only [mul_one, one_mul, binaryLeviCrossed_scalar_zero, map_one,
    Module.End.one_apply, zero_add] using identity

def binaryLeviCrossedEquiv (degree : ℕ) :
    crossedCocycles (binaryLeviRepresentation degree) ≃ₗ[ℂ]
      crossedCocycles (binaryArithmeticRepresentation degree) where
  toFun cochain := ⟨fun element => cochain.val (1, element), by
    intro first second
    have identity := cochain.property (1, first) (1, second)
    change cochain.val (1 * 1, first * second) = cochain.val (1, first) +
      binaryArithmeticRepresentation degree first (cochain.val (1, second)) at identity
    simpa only [one_mul] using identity⟩
  invFun cochain := ⟨fun element => cochain.val element.2, by
    intro first second
    exact cochain.property first.2 second.2⟩
  left_inv cochain := by
    apply Subtype.ext
    funext element
    exact (binaryLeviCrossed_factor degree cochain element).symm
  right_inv cochain := Subtype.ext rfl
  map_add' first second := rfl
  map_smul' scalar cochain := rfl

theorem binaryLeviCrossedEquiv_boundary (degree : ℕ) (polynomial : Binary.HomogeneousPoly (degree + 1)) :
    binaryLeviCrossedEquiv degree (crossedBoundary (binaryLeviRepresentation degree) polynomial) =
      crossedBoundary (binaryArithmeticRepresentation degree) polynomial := by
  apply Subtype.ext
  rfl

theorem binaryLeviCrossedEquiv_boundaries (degree : ℕ) :
    (crossedBoundaries (binaryLeviRepresentation degree)).map
      (binaryLeviCrossedEquiv degree).toLinearMap =
      crossedBoundaries (binaryArithmeticRepresentation degree) := by
  apply le_antisymm
  · rintro cochain ⟨previous, ⟨polynomial, rfl⟩, rfl⟩
    exact ⟨polynomial, (binaryLeviCrossedEquiv_boundary degree polynomial).symm⟩
  · rintro cochain ⟨polynomial, rfl⟩
    exact ⟨crossedBoundary (binaryLeviRepresentation degree) polynomial, ⟨polynomial, rfl⟩,
      binaryLeviCrossedEquiv_boundary degree polynomial⟩

def binaryLeviH1Equiv (degree : ℕ) :
    CrossedH1 (binaryLeviRepresentation degree) ≃ₗ[ℂ]
      CrossedH1 (binaryArithmeticRepresentation degree) :=
  Submodule.Quotient.equiv _ _ (binaryLeviCrossedEquiv degree)
    (binaryLeviCrossedEquiv_boundaries degree)

def innerBadLineArithmeticBinaryMap (degree : ℕ) (positive : 0 < degree) :
    innerBadLineClasses degree →ₗ[ℂ] CrossedH1 (binaryArithmeticRepresentation degree) :=
  (binaryLeviH1Equiv degree).toLinearMap.comp (innerBadLineExplicitBinaryMap degree positive)

theorem innerBadLineArithmeticBinaryMap_injective (degree : ℕ) (positive : 0 < degree) :
    Function.Injective (innerBadLineArithmeticBinaryMap degree positive) :=
  (binaryLeviH1Equiv degree).injective.comp (innerBadLineExplicitBinaryMap_injective degree positive)

theorem innerBadLineArithmeticBinaryMap_zero_iff (degree : ℕ) (positive : 0 < degree)
    (coordinate : innerBadLineClasses degree) :
    innerBadLineArithmeticBinaryMap degree positive coordinate = 0 ↔ coordinate = 0 := by
  constructor
  · intro zero
    apply innerBadLineArithmeticBinaryMap_injective degree positive
    exact zero.trans (map_zero _).symm
  · rintro rfl
    exact map_zero _

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
