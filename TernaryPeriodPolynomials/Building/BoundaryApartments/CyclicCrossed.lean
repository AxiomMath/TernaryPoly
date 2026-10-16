module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Radical.Exactness
public import Mathlib.GroupTheory.SemidirectProduct

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

def representationMultiplicativeAut {GroupType Vector : Type*}
    [Group GroupType] [AddCommGroup Vector] [Module ℂ Vector]
    (representation : Representation ℂ GroupType Vector) :
    GroupType →* MulAut (Multiplicative Vector) where
  toFun matrix :=
    { toFun := fun value => Multiplicative.ofAdd (representation matrix value.toAdd)
      invFun := fun value => Multiplicative.ofAdd (representation matrix⁻¹ value.toAdd)
      left_inv := by
        intro value
        change representation matrix⁻¹ (representation matrix value.toAdd) = value.toAdd
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      right_inv := by
        intro value
        change representation matrix (representation matrix⁻¹ value.toAdd) = value.toAdd
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      map_mul' := by
        intro first second
        change representation matrix (first.toAdd + second.toAdd) =
          representation matrix first.toAdd + representation matrix second.toAdd
        exact map_add _ _ _ }
  map_one' := by
    apply MulEquiv.ext
    intro value
    change representation 1 value.toAdd = value.toAdd
    rw [map_one, Module.End.one_apply]
  map_mul' first second := by
    apply MulEquiv.ext
    intro value
    change representation (first * second) value.toAdd =
      representation first (representation second value.toAdd)
    rw [map_mul, Module.End.mul_apply]

theorem cyclicCrossed_exists {GroupType Vector : Type*}
    [Group GroupType] [AddCommGroup Vector] [Module ℂ Vector]
    (representation : Representation ℂ GroupType Vector)
    (generator : GroupType) (value : Vector) :
    ∃ crossed : ℤ → Vector, crossed 1 = value ∧
      ∀ first second : ℤ, crossed (first + second) =
        representation (generator ^ first) (crossed second) + crossed first := by
  let action := representationMultiplicativeAut representation
  let lift : Multiplicative Vector ⋊[action] GroupType :=
    ⟨Multiplicative.ofAdd value, generator⟩
  let crossed (integer : ℤ) : Vector := (lift ^ integer).left.toAdd
  have right (integer : ℤ) : (lift ^ integer).right = generator ^ integer := by
    have mapped := map_zpow (SemidirectProduct.rightHom
      (φ := action)) lift integer
    exact mapped
  refine ⟨crossed, ?_, ?_⟩
  · change (lift ^ (1 : ℤ)).left.toAdd = value
    rw [zpow_one]
    rfl
  · intro first second
    change (lift ^ (first + second)).left.toAdd = _
    rw [zpow_add, SemidirectProduct.mul_left]
    change crossed first + representation (lift ^ first).right (crossed second) = _
    rw [right, add_comm]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
