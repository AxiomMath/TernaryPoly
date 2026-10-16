module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Two.CocycleUnits

@[expose] public section


noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {G : Type} [Group G]

@[ext]
structure TwoCocycleExtension (representation : Rep ℂ G) (cycle : groupCohomology.cocycles₂ representation)
    (unit_zero : cycle (1, 1) = 0) where
  coefficient : representation
  element : G

instance twoCocycleExtensionGroup (representation : Rep ℂ G) (cycle : groupCohomology.cocycles₂ representation)
    (unit_zero : cycle (1, 1) = 0) : Group (TwoCocycleExtension representation cycle unit_zero) where
  mul first second := ⟨first.coefficient + representation.ρ first.element second.coefficient +
    cycle (first.element, second.element), first.element * second.element⟩
  one := ⟨0, 1⟩
  inv value := ⟨-representation.ρ value.element⁻¹ value.coefficient - cycle (value.element⁻¹, value.element), value.element⁻¹⟩
  mul_assoc first second third := by
    apply TwoCocycleExtension.ext
    · change (first.coefficient + representation.ρ first.element second.coefficient + cycle (first.element, second.element)) +
        representation.ρ (first.element * second.element) third.coefficient + cycle (first.element * second.element, third.element) =
        first.coefficient + representation.ρ first.element
          (second.coefficient + representation.ρ second.element third.coefficient + cycle (second.element, third.element)) +
            cycle (first.element, second.element * third.element)
      rw [map_add, map_add, map_mul, Module.End.mul_apply]
      linear_combination (norm := abel) twoCocycle_relation representation cycle first.element second.element third.element
    · exact mul_assoc _ _ _
  one_mul value := by
    apply TwoCocycleExtension.ext
    · change 0 + representation.ρ 1 value.coefficient + cycle (1, value.element) = value.coefficient
      rw [map_one, Module.End.one_apply, zero_add, twoCocycle_one_left, unit_zero, add_zero]
    · exact one_mul _
  mul_one value := by
    apply TwoCocycleExtension.ext
    · change value.coefficient + representation.ρ value.element 0 + cycle (value.element, 1) = value.coefficient
      rw [map_zero, add_zero, twoCocycle_one_right, unit_zero, map_zero, add_zero]
    · exact mul_one _
  inv_mul_cancel value := by
    apply TwoCocycleExtension.ext
    · change (-representation.ρ value.element⁻¹ value.coefficient - cycle (value.element⁻¹, value.element)) +
        representation.ρ value.element⁻¹ value.coefficient + cycle (value.element⁻¹, value.element) = 0
      abel
    · exact inv_mul_cancel _

def twoCocycleExtensionProjection (representation : Rep ℂ G) (cycle : groupCohomology.cocycles₂ representation)
    (unit_zero : cycle (1, 1) = 0) : TwoCocycleExtension representation cycle unit_zero →* G where
  toFun := TwoCocycleExtension.element
  map_one' := rfl
  map_mul' _ _ := rfl

def twoCocycleExtensionInclusion (representation : Rep ℂ G) (cycle : groupCohomology.cocycles₂ representation)
    (unit_zero : cycle (1, 1) = 0) : Multiplicative representation →* TwoCocycleExtension representation cycle unit_zero where
  toFun vector := ⟨vector.toAdd, 1⟩
  map_one' := rfl
  map_mul' first second := by
    apply TwoCocycleExtension.ext
    · change first.toAdd + second.toAdd = first.toAdd + representation.ρ 1 second.toAdd + cycle (1, 1)
      rw [map_one, Module.End.one_apply, unit_zero, add_zero]
    · exact (one_mul 1).symm

theorem twoCocycleExtensionInclusion_coefficient (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0) (vector : representation) :
    (twoCocycleExtensionInclusion representation cycle unit_zero (Multiplicative.ofAdd vector)).coefficient = vector := rfl

theorem twoCocycleExtensionInclusion_projection (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0) (vector : Multiplicative representation) :
    twoCocycleExtensionProjection representation cycle unit_zero
      (twoCocycleExtensionInclusion representation cycle unit_zero vector) = 1 := rfl

theorem twoCocycleExtension_kernel (representation : Rep ℂ G) (cycle : groupCohomology.cocycles₂ representation)
    (unit_zero : cycle (1, 1) = 0) (value : TwoCocycleExtension representation cycle unit_zero)
    (kernel : twoCocycleExtensionProjection representation cycle unit_zero value = 1) :
    value = twoCocycleExtensionInclusion representation cycle unit_zero (Multiplicative.ofAdd value.coefficient) := by
  apply TwoCocycleExtension.ext
  · rfl
  · exact kernel

theorem twoCocycleExtensionInclusion_power (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0)
    (vector : representation) (power : ℕ) :
    twoCocycleExtensionInclusion representation cycle unit_zero (Multiplicative.ofAdd vector) ^ power =
      twoCocycleExtensionInclusion representation cycle unit_zero (Multiplicative.ofAdd ((power : ℂ) • vector)) := by
  rw [← map_pow]
  congr 1
  apply Multiplicative.toAdd.injective
  change power • vector = (power : ℂ) • vector
  exact (Nat.cast_smul_eq_nsmul ℂ power vector).symm

theorem twoCocycleExtensionInclusion_commutes (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0)
    (trivial : ∀ element vector, representation.ρ element vector = vector)
    (vector : representation) (value : TwoCocycleExtension representation cycle unit_zero) :
    Commute (twoCocycleExtensionInclusion representation cycle unit_zero (Multiplicative.ofAdd vector)) value := by
  apply TwoCocycleExtension.ext
  · change vector + representation.ρ 1 value.coefficient + cycle (1, value.element) =
      value.coefficient + representation.ρ value.element vector + cycle (value.element, 1)
    rw [trivial, trivial, twoCocycle_one_left representation cycle value.element,
      twoCocycle_one_right representation cycle value.element, unit_zero, map_zero, add_zero, add_zero, add_comm]
  · exact (one_mul _).trans (mul_one _).symm

theorem twoCocycleExtension_torsion_kernel (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0)
    (value : TwoCocycleExtension representation cycle unit_zero)
    (kernel : twoCocycleExtensionProjection representation cycle unit_zero value = 1)
    (power : ℕ) (positive : 0 < power) (torsion : value ^ power = 1) : value = 1 := by
  have description := twoCocycleExtension_kernel representation cycle unit_zero value kernel
  have powers := congrArg TwoCocycleExtension.coefficient torsion
  rw [description, twoCocycleExtensionInclusion_power] at powers
  change (power : ℂ) • value.coefficient = 0 at powers
  have coefficient_zero := (smul_eq_zero.mp powers).resolve_left (by exact_mod_cast Nat.ne_of_gt positive)
  rw [description, coefficient_zero]
  exact (twoCocycleExtensionInclusion representation cycle unit_zero).map_one

theorem twoCocycleExtension_section_boundary (representation : Rep ℂ G)
    (cycle : groupCohomology.cocycles₂ representation) (unit_zero : cycle (1, 1) = 0)
    (splitting : G →* TwoCocycleExtension representation cycle unit_zero)
    (projects : ∀ element, twoCocycleExtensionProjection representation cycle unit_zero (splitting element) = element) :
    ∀ first second,
      representation.ρ first (-(splitting second).coefficient) - (-(splitting (first * second)).coefficient) +
        (-(splitting first).coefficient) = cycle (first, second) := by
  intro first second
  have equation := congrArg TwoCocycleExtension.coefficient (splitting.map_mul first second)
  change (splitting (first * second)).coefficient =
    (splitting first).coefficient + representation.ρ (splitting first).element (splitting second).coefficient +
      cycle ((splitting first).element, (splitting second).element) at equation
  change ∀ element, (splitting element).element = element at projects
  rw [projects, projects] at equation
  rw [map_neg]
  linear_combination (norm := abel) equation

end TernaryPeriodPolynomials.SphericalDetection.Helpers
