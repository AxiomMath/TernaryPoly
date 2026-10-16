module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InnerMixed

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

section Coefficients

variable {GroupType Source Target : Type} [Group GroupType]
  [AddCommGroup Source] [AddCommGroup Target] [Module ℂ Source] [Module ℂ Target]
  (representation : Representation ℂ GroupType Source) (equivalence : Source ≃ₗ[ℂ] Target)

def coefficientTransportRepresentation : Representation ℂ GroupType Target :=
  equivalence.conjRingEquiv.toMonoidHom.comp representation

theorem coefficientTransportRepresentation_apply (element : GroupType) (value : Target) :
    coefficientTransportRepresentation representation equivalence element value =
      equivalence (representation element (equivalence.symm value)) := rfl

def crossedCoefficientEquiv :
    crossedCocycles representation ≃ₗ[ℂ]
      crossedCocycles (coefficientTransportRepresentation representation equivalence) where
  toFun cochain := ⟨fun element => equivalence (cochain.val element), by
    intro first second
    change equivalence (cochain.val (first * second)) =
      equivalence (cochain.val first) +
        coefficientTransportRepresentation representation equivalence first
          (equivalence (cochain.val second))
    rw [cochain.property, map_add]
    change _ = _ + equivalence (representation first (equivalence.symm (equivalence (cochain.val second))))
    rw [LinearEquiv.symm_apply_apply]⟩
  invFun cochain := ⟨fun element => equivalence.symm (cochain.val element), by
    intro first second
    change equivalence.symm (cochain.val (first * second)) =
      equivalence.symm (cochain.val first) + representation first (equivalence.symm (cochain.val second))
    rw [cochain.property, map_add]
    rw [coefficientTransportRepresentation_apply, LinearEquiv.symm_apply_apply]⟩
  left_inv cochain := by
    apply Subtype.ext
    funext element
    exact equivalence.symm_apply_apply _
  right_inv cochain := by
    apply Subtype.ext
    funext element
    exact equivalence.apply_symm_apply _
  map_add' first second := by
    apply Subtype.ext
    funext element
    exact map_add _ _ _
  map_smul' scalar cochain := by
    apply Subtype.ext
    funext element
    exact map_smul _ _ _

theorem crossedCoefficientEquiv_boundary (value : Source) :
    crossedCoefficientEquiv representation equivalence (crossedBoundary representation value) =
      crossedBoundary (coefficientTransportRepresentation representation equivalence)
        (equivalence value) := by
  apply Subtype.ext
  funext element
  change equivalence (representation element value - value) =
    coefficientTransportRepresentation representation equivalence element (equivalence value) -
      equivalence value
  rw [map_sub, coefficientTransportRepresentation_apply, LinearEquiv.symm_apply_apply]

theorem crossedCoefficientEquiv_boundaries :
    (crossedBoundaries representation).map (crossedCoefficientEquiv representation equivalence).toLinearMap =
      crossedBoundaries (coefficientTransportRepresentation representation equivalence) := by
  apply le_antisymm
  · rintro cochain ⟨previous, ⟨value, rfl⟩, rfl⟩
    exact ⟨equivalence value, (crossedCoefficientEquiv_boundary representation equivalence value).symm⟩
  · rintro cochain ⟨value, rfl⟩
    refine ⟨crossedBoundary representation (equivalence.symm value), ⟨_, rfl⟩, ?_⟩
    change crossedCoefficientEquiv representation equivalence _ = _
    rw [crossedCoefficientEquiv_boundary, LinearEquiv.apply_symm_apply]

def crossedH1CoefficientEquiv :
    CrossedH1 representation ≃ₗ[ℂ]
      CrossedH1 (coefficientTransportRepresentation representation equivalence) :=
  Submodule.Quotient.equiv _ _ (crossedCoefficientEquiv representation equivalence)
    (crossedCoefficientEquiv_boundaries representation equivalence)

end Coefficients

def standardBadLineRadicalBinaryEquiv (degree : ℕ) (positive : 0 < degree) :
    CrossedH1 ((standardBadLineRepresentation degree).comp SemidirectProduct.inl) ≃ₗ[ℂ]
      Binary.HomogeneousPoly (degree + 1) := by
  rw [standardBadLineRepresentation_radical]
  exact radicalCrossedBinaryEquiv degree positive

/-- The binary action transported from the actual stabilizer action on radical cohomology. -/
def standardBadLineBinaryRepresentation (degree : ℕ) (positive : 0 < degree) :
    Representation ℂ (ℤˣ × binaryArithmeticLevel) (Binary.HomogeneousPoly (degree + 1)) :=
  coefficientTransportRepresentation
    (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree))
    (standardBadLineRadicalBinaryEquiv degree positive)

def standardBadLineBinaryH1Equiv (degree : ℕ) (positive : 0 < degree) :
    CrossedH1 (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree)) ≃ₗ[ℂ]
        CrossedH1 (standardBadLineBinaryRepresentation degree positive) := by
  unfold standardBadLineBinaryRepresentation
  exact crossedH1CoefficientEquiv
    (leviCrossedH1Representation integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree))
    (standardBadLineRadicalBinaryEquiv degree positive)

def innerBadLineBinaryMixedMap (degree : ℕ) (positive : 0 < degree) :
    innerBadLineClasses degree →ₗ[ℂ]
      CrossedH1 (standardBadLineBinaryRepresentation degree positive) :=
  (standardBadLineBinaryH1Equiv degree positive).toLinearMap.comp (innerBadLineMixedMap degree)

theorem innerBadLineBinaryMixedMap_injective (degree : ℕ) (positive : 0 < degree) :
    Function.Injective (innerBadLineBinaryMixedMap degree positive) :=
  (standardBadLineBinaryH1Equiv degree positive).injective.comp
    (innerBadLineMixedMap_injective degree)

theorem innerBadLineBinaryMixedMap_zero_iff (degree : ℕ) (positive : 0 < degree)
    (coordinate : innerBadLineClasses degree) :
    innerBadLineBinaryMixedMap degree positive coordinate = 0 ↔ coordinate = 0 := by
  constructor
  · intro zero
    apply innerBadLineBinaryMixedMap_injective degree positive
    exact zero.trans (map_zero _).symm
  · rintro rfl
    exact map_zero _

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
