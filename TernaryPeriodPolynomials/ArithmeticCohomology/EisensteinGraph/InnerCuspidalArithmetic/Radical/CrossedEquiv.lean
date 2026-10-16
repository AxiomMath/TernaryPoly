module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.CrossedRadical

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

variable {GroupType Value : Type} [Group GroupType] [AddCommGroup Value] [Module ℂ Value]

def representationAddEquiv (representation : Representation ℂ GroupType Value)
    (element : GroupType) : Value ≃+ Value where
  toFun := representation element
  invFun := representation element⁻¹
  left_inv value := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv value := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  map_add' := (representation element).map_add

def representationMultiplicativeAction (representation : Representation ℂ GroupType Value) :
    GroupType →* MulAut (Multiplicative Value) where
  toFun element := AddEquiv.toMultiplicative (representationAddEquiv representation element)
  map_one' := by
    ext value
    change representation 1 value.toAdd = value.toAdd
    rw [map_one, Module.End.one_apply]
  map_mul' first second := by
    ext value
    change representation (first * second) value.toAdd =
      representation first (representation second value.toAdd)
    rw [map_mul, Module.End.mul_apply]

variable {Target : Type} [Group Target]

def integerPairLift (first second : Target) (commuting : Commute first second) :
    Multiplicative (ℤ × ℤ) →* Target where
  toFun coordinates := first ^ coordinates.toAdd.1 * second ^ coordinates.toAdd.2
  map_one' := by simp
  map_mul' coordinatesOne coordinatesTwo := by
    change first ^ (coordinatesOne.toAdd.1 + coordinatesTwo.toAdd.1) *
      second ^ (coordinatesOne.toAdd.2 + coordinatesTwo.toAdd.2) = _
    rw [zpow_add, zpow_add]
    calc
      first ^ coordinatesOne.toAdd.1 * first ^ coordinatesTwo.toAdd.1 *
          (second ^ coordinatesOne.toAdd.2 * second ^ coordinatesTwo.toAdd.2) =
        first ^ coordinatesOne.toAdd.1 *
          (first ^ coordinatesTwo.toAdd.1 * second ^ coordinatesOne.toAdd.2) *
            second ^ coordinatesTwo.toAdd.2 := by simp only [mul_assoc]
      _ = first ^ coordinatesOne.toAdd.1 *
          (second ^ coordinatesOne.toAdd.2 * first ^ coordinatesTwo.toAdd.1) *
            second ^ coordinatesTwo.toAdd.2 := by
        rw [(commuting.zpow_zpow coordinatesTwo.toAdd.1 coordinatesOne.toAdd.2).eq]
      _ = _ := by simp only [mul_assoc]

def radicalAffineGenerator (degree : ℕ)
    (pair : discreteRadicalCycles degree) (index : Fin 2) :
    SemidirectProduct (Multiplicative (HomogeneousPoly degree)) (Multiplicative (ℤ × ℤ))
      (representationMultiplicativeAction (radicalRepresentation degree)) :=
  ⟨Multiplicative.ofAdd (if index = 0 then pair.val.1 else pair.val.2),
    integralRadicalGenerator index⟩

theorem radicalAffineGenerator_commute (degree : ℕ) (pair : discreteRadicalCycles degree) :
    Commute (radicalAffineGenerator degree pair 0) (radicalAffineGenerator degree pair 1) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change pair.val.1 + radicalRepresentation degree (integralRadicalGenerator 0) pair.val.2 =
      pair.val.2 + radicalRepresentation degree (integralRadicalGenerator 1) pair.val.1
    rw [radicalRepresentation_generator, radicalRepresentation_generator]
    have relation := pair.property
    change (radicalDifference degree 0 pair.val.2 - radicalDifference degree 1 pair.val.1) = 0
      at relation
    have equality := sub_eq_zero.mp relation
    simp only [radicalDifference, LinearMap.sub_apply, Module.End.one_apply] at equality
    simpa only [add_comm] using sub_eq_sub_iff_add_eq_add.mp equality
  · exact mul_comm _ _

def radicalAffineLift (degree : ℕ) (pair : discreteRadicalCycles degree) :
    Multiplicative (ℤ × ℤ) →*
      SemidirectProduct (Multiplicative (HomogeneousPoly degree)) (Multiplicative (ℤ × ℤ))
        (representationMultiplicativeAction (radicalRepresentation degree)) :=
  integerPairLift (radicalAffineGenerator degree pair 0) (radicalAffineGenerator degree pair 1)
    (radicalAffineGenerator_commute degree pair)

theorem radicalAffineLift_right (degree : ℕ) (pair : discreteRadicalCycles degree)
    (coordinates : Multiplicative (ℤ × ℤ)) :
    (radicalAffineLift degree pair coordinates).right = coordinates := by
  change SemidirectProduct.rightHom
    (radicalAffineGenerator degree pair 0 ^ coordinates.toAdd.1 *
      radicalAffineGenerator degree pair 1 ^ coordinates.toAdd.2) = coordinates
  rw [map_mul, map_zpow, map_zpow]
  exact integralRadicalGenerator_factor coordinates

def radicalCrossedFromPair (degree : ℕ) (pair : discreteRadicalCycles degree) :
    crossedCocycles (radicalRepresentation degree) :=
  ⟨fun coordinates => (radicalAffineLift degree pair coordinates).left.toAdd, by
    intro first second
    change (radicalAffineLift degree pair (first * second)).left.toAdd =
      (radicalAffineLift degree pair first).left.toAdd +
        radicalRepresentation degree first (radicalAffineLift degree pair second).left.toAdd
    rw [map_mul, SemidirectProduct.mul_left, toAdd_mul, radicalAffineLift_right]
    rfl⟩

theorem radicalCrossedFromPair_generator (degree : ℕ) (pair : discreteRadicalCycles degree)
    (index : Fin 2) :
    (radicalCrossedFromPair degree pair).val (integralRadicalGenerator index) =
      if index = 0 then pair.val.1 else pair.val.2 := by
  change (radicalAffineGenerator degree pair 0 ^ (integralRadicalGenerator index).toAdd.1 *
    radicalAffineGenerator degree pair 1 ^ (integralRadicalGenerator index).toAdd.2).left.toAdd = _
  fin_cases index <;> simp [integralRadicalGenerator, radicalAffineGenerator]

theorem radicalCrossedEvaluation_surjective (degree : ℕ) :
    Function.Surjective (radicalCrossedEvaluation degree) := by
  intro pair
  refine ⟨radicalCrossedFromPair degree pair, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact radicalCrossedFromPair_generator degree pair 0
  · change (radicalCrossedFromPair degree pair).val (integralRadicalGenerator 1) = pair.val.2
    simpa using radicalCrossedFromPair_generator degree pair 1

def radicalCrossedEvaluationEquiv (degree : ℕ) :
    crossedCocycles (radicalRepresentation degree) ≃ₗ[ℂ] discreteRadicalCycles degree :=
  LinearEquiv.ofBijective (radicalCrossedEvaluation degree)
    ⟨radicalCrossedEvaluation_injective degree, radicalCrossedEvaluation_surjective degree⟩

def radicalCrossedBoundaries (degree : ℕ) :
    Submodule ℂ (crossedCocycles (radicalRepresentation degree)) :=
  (crossedBoundary (radicalRepresentation degree)).range

abbrev RadicalCrossedH1 (degree : ℕ) :=
  @HasQuotient.Quotient (crossedCocycles (radicalRepresentation degree))
    (Submodule ℂ (crossedCocycles (radicalRepresentation degree)))
    (@Submodule.hasQuotient ℂ (crossedCocycles (radicalRepresentation degree))
      inferInstance inferInstance inferInstance)
    (radicalCrossedBoundaries degree)

theorem radicalCrossedEvaluationEquiv_boundaries (degree : ℕ) (positive : 0 < degree) :
    (radicalCrossedBoundaries degree).map (radicalCrossedEvaluationEquiv degree).toLinearMap =
      discreteRadicalBoundaries degree positive := by
  apply le_antisymm
  · rintro cycle ⟨previous, ⟨polynomial, rfl⟩, rfl⟩
    exact ⟨polynomial, (radicalCrossedEvaluation_boundary degree positive polynomial).symm⟩
  · rintro cycle ⟨polynomial, rfl⟩
    exact ⟨crossedBoundary (radicalRepresentation degree) polynomial, ⟨polynomial, rfl⟩,
      radicalCrossedEvaluation_boundary degree positive polynomial⟩

def radicalCrossedDiscreteEquiv (degree : ℕ) (positive : 0 < degree) :
    RadicalCrossedH1 degree ≃ₗ[ℂ] DiscreteRadicalH1 degree positive :=
  Submodule.Quotient.equiv _ _ (radicalCrossedEvaluationEquiv degree)
    (radicalCrossedEvaluationEquiv_boundaries degree positive)

def radicalCrossedBinaryEquiv (degree : ℕ) (positive : 0 < degree) :
    RadicalCrossedH1 degree ≃ₗ[ℂ] Binary.HomogeneousPoly (degree + 1) :=
  (radicalCrossedDiscreteEquiv degree positive).trans (discreteRadicalBinaryEquiv degree positive)

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
