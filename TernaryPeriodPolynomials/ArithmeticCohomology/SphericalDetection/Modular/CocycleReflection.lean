module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Modular.Reflection

@[expose] public section


open GeneralEisenstein Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def modularCocycleReflection (degree : ℕ) (twist : ℤ) :
    Module.End ℂ (groupCohomology.cocycles₁ (modularBinaryRep degree twist)) where
  toFun cycle := ⟨fun matrix => binaryParityReflection degree (cycle (modularReflection matrix)), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro first second
    let value : SpecialLinearGroup (Fin 2) ℤ → Binary.HomogeneousPoly degree := cycle
    let action : SpecialLinearGroup (Fin 2) ℤ → Module.End ℂ (Binary.HomogeneousPoly degree) :=
      (modularBinaryRep degree twist).ρ
    have relation : value (modularReflection first * modularReflection second) =
        action (modularReflection first) (value (modularReflection second)) +
          value (modularReflection first) :=
      (groupCohomology.mem_cocycles₁_iff _).mp cycle.property
        (modularReflection first) (modularReflection second)
    change binaryParityReflection degree (value (modularReflection (first * second))) =
      action first (binaryParityReflection degree (value (modularReflection second))) +
        binaryParityReflection degree (value (modularReflection first))
    rw [map_mul, relation, map_add]
    exact congrArg (· + binaryParityReflection degree (value (modularReflection first)))
      (binaryParityReflection_modular_intertwines degree twist first (value (modularReflection second)))⟩
  map_add' first second := by
    apply groupCohomology.cocycles₁_ext
    intro matrix
    exact map_add (binaryParityReflection degree) (first (modularReflection matrix))
      (second (modularReflection matrix))
  map_smul' scalar cycle := by
    apply groupCohomology.cocycles₁_ext
    intro matrix
    exact map_smul (binaryParityReflection degree) scalar (cycle (modularReflection matrix))

theorem modularCocycleReflection_apply (degree : ℕ) (twist : ℤ)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist)) (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    modularCocycleReflection degree twist cycle matrix =
      binaryParityReflection degree (cycle (modularReflection matrix)) := rfl

theorem modularCocycleReflection_involutive (degree : ℕ) (twist : ℤ) :
    Function.Involutive (modularCocycleReflection degree twist) := by
  intro cycle
  apply groupCohomology.cocycles₁_ext
  intro matrix
  simp only [modularCocycleReflection_apply]
  rw [modularReflection_involutive matrix]
  exact binaryParityReflection_involutive degree (cycle matrix)

theorem modularCocycleReflection_boundary (degree : ℕ) (twist : ℤ)
    (polynomial : Binary.HomogeneousPoly degree) :
    modularCocycleReflection degree twist (oneBoundaryCycle (modularBinaryRep degree twist) polynomial) =
      oneBoundaryCycle (modularBinaryRep degree twist) (binaryParityReflection degree polynomial) := by
  apply groupCohomology.cocycles₁_ext
  intro matrix
  let action : Module.End ℂ (Binary.HomogeneousPoly degree) :=
    (modularBinaryRep degree twist).ρ matrix
  let reflectedAction : Module.End ℂ (Binary.HomogeneousPoly degree) :=
    (modularBinaryRep degree twist).ρ (modularReflection matrix)
  change binaryParityReflection degree
      (reflectedAction polynomial - polynomial) =
    action (binaryParityReflection degree polynomial) -
      binaryParityReflection degree polynomial
  rw [map_sub]
  exact congrArg (· - binaryParityReflection degree polynomial)
    (binaryParityReflection_modular_intertwines degree twist matrix polynomial)

def modularCocycleParity (degree : ℕ) (twist : ℤ) (parity : ℕ) :
    Module.End ℂ (groupCohomology.cocycles₁ (modularBinaryRep degree twist)) :=
  (2 : ℂ)⁻¹ • (LinearMap.id + (-1 : ℂ) ^ parity • modularCocycleReflection degree twist)

theorem modularCocycleParity_apply (degree : ℕ) (twist : ℤ) (parity : ℕ)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist)) (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    modularCocycleParity degree twist parity cycle matrix =
      (let value : Binary.HomogeneousPoly degree := cycle matrix
       (2 : ℂ)⁻¹ • (value + (-1 : ℂ) ^ parity •
        binaryParityReflection degree (cycle (modularReflection matrix)))) := rfl

theorem modularCocycleParity_T (degree : ℕ) (twist : ℤ) (parity : ℕ)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist)) (zero : cycle ModularGroup.T = 0) :
    modularCocycleParity degree twist parity cycle ModularGroup.T = 0 := by
  have inverse_zero : cycle ModularGroup.T⁻¹ = 0 := by
    have relation := groupCohomology.cocycles₁_map_inv cycle ModularGroup.T⁻¹
    rw [inv_inv, zero, map_zero] at relation
    exact neg_eq_zero.mp relation.symm
  rw [modularCocycleParity_apply, modularReflection_T, inverse_zero, zero]
  change (2 : ℂ)⁻¹ • ((0 : Binary.HomogeneousPoly degree) +
    (-1 : ℂ) ^ parity • binaryParityReflection degree 0) = 0
  rw [map_zero, smul_zero, add_zero, smul_zero]

theorem modularCocycleParity_S (degree : ℕ) (twist : ℤ) (parity : ℕ)
    (cycle : groupCohomology.cocycles₁ (modularBinaryRep degree twist))
    (inverse_value : cycle ModularGroup.S⁻¹ = cycle ModularGroup.S) :
    modularCocycleParity degree twist parity cycle ModularGroup.S =
      binaryParityComponent degree parity (cycle ModularGroup.S) := by
  rw [modularCocycleParity_apply, modularReflection_S, inverse_value]
  rfl

theorem modularCocycleParity_boundary (degree : ℕ) (twist : ℤ) (parity : ℕ)
    (polynomial : Binary.HomogeneousPoly degree) :
    modularCocycleParity degree twist parity
      (oneBoundaryCycle (modularBinaryRep degree twist) polynomial) =
        oneBoundaryCycle (modularBinaryRep degree twist)
          (binaryParityComponent degree parity polynomial) := by
  change (2 : ℂ)⁻¹ • (oneBoundaryCycle (modularBinaryRep degree twist) polynomial +
    (-1 : ℂ) ^ parity • modularCocycleReflection degree twist
      (oneBoundaryCycle (modularBinaryRep degree twist) polynomial)) = _
  rw [modularCocycleReflection_boundary]
  apply groupCohomology.cocycles₁_ext
  intro matrix
  let action : Module.End ℂ (Binary.HomogeneousPoly degree) :=
    (modularBinaryRep degree twist).ρ matrix
  change (2 : ℂ)⁻¹ • ((action polynomial - polynomial) +
    (-1 : ℂ) ^ parity • (action (binaryParityReflection degree polynomial) -
      binaryParityReflection degree polynomial)) =
    action ((2 : ℂ)⁻¹ • (polynomial + (-1 : ℂ) ^ parity • binaryParityReflection degree polynomial)) -
      (2 : ℂ)⁻¹ • (polynomial + (-1 : ℂ) ^ parity • binaryParityReflection degree polynomial)
  simp only [map_smul, map_add, smul_add, smul_sub]
  abel

end TernaryPeriodPolynomials.SphericalDetection.Helpers
