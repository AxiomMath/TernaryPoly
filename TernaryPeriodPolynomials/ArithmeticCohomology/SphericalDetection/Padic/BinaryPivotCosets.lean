module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PivotResidues

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicPrimePowerUnit {prime : ℕ} [Fact prime.Prime] (power : ℕ) : ℚ_[prime]ˣ :=
  Units.mk0 ((prime : ℚ_[prime]) ^ power)
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)))

theorem padicScale_exists_unit {prime : ℕ} [Fact prime.Prime] (reference scale : ℚ_[prime]ˣ)
    (same_norm : ‖scale.val‖ = ‖reference.val‖) :
    ∃ unit : ℤ_[prime]ˣ, scale = reference * Units.map PadicInt.Coe.ringHom.toMonoidHom unit := by
  have normalized : ‖scale.val / reference.val‖ = 1 := by
    rw [norm_div, same_norm, div_self (norm_ne_zero_iff.mpr reference.ne_zero)]
  refine ⟨PadicInt.mkUnits normalized, ?_⟩
  apply Units.ext
  change scale.val = reference.val * ((PadicInt.mkUnits normalized).val : ℚ_[prime])
  rw [PadicInt.mkUnits_eq, mul_div_cancel₀ _ reference.ne_zero]

def padicUpperPrimitiveRepresentative {prime : ℕ} [Fact prime.Prime] (power : ℕ)
    (index : Fin (prime ^ power)) : GeneralLinearGroup (Fin 2) ℚ_[prime] :=
  binaryUpperPivot (padicPrimePowerUnit power) (index.val : ℚ_[prime])

def padicLowerPrimitiveRepresentative {prime : ℕ} [Fact prime.Prime] (power : ℕ)
    (index : Fin (prime ^ power)) : GeneralLinearGroup (Fin 2) ℚ_[prime] :=
  binaryLowerPivot (padicPrimePowerUnit power) (index.val : ℚ_[prime])

theorem padicUpperPivot_normalize {prime : ℕ} [Fact prime.Prime] (power : ℕ)
    (scale : ℚ_[prime]ˣ) (offset : ℤ_[prime])
    (same_norm : ‖scale.val‖ = ‖(prime : ℚ_[prime]) ^ power‖) :
    ∃ compact : GeneralLinearGroup (Fin 2) ℤ_[prime],
      binaryUpperPivot scale (offset : ℚ_[prime]) =
        padicUpperPrimitiveRepresentative power (padicPivotResidue power offset) *
          GeneralLinearGroup.map PadicInt.Coe.ringHom compact := by
  obtain ⟨unit, scale_eq⟩ := padicScale_exists_unit (padicPrimePowerUnit power) scale same_norm
  obtain ⟨shift, offset_eq⟩ := padicPivotResidue_decomposition power offset
  refine ⟨binaryUpperPivot unit shift, ?_⟩
  have mapped := congrArg (fun value : ℤ_[prime] => (value : ℚ_[prime])) offset_eq
  change (offset : ℚ_[prime]) =
    ((padicPivotResidue power offset).val : ℚ_[prime]) +
      (padicPrimePowerUnit power).val * (shift : ℚ_[prime]) at mapped
  rw [scale_eq, mapped]
  exact binaryUpperPivot_same_coset PadicInt.Coe.ringHom _ _ unit shift

theorem padicLowerPivot_normalize {prime : ℕ} [Fact prime.Prime] (power : ℕ)
    (scale : ℚ_[prime]ˣ) (offset : ℤ_[prime])
    (same_norm : ‖scale.val‖ = ‖(prime : ℚ_[prime]) ^ power‖) :
    ∃ compact : GeneralLinearGroup (Fin 2) ℤ_[prime],
      binaryLowerPivot scale (offset : ℚ_[prime]) =
        padicLowerPrimitiveRepresentative power (padicPivotResidue power offset) *
          GeneralLinearGroup.map PadicInt.Coe.ringHom compact := by
  obtain ⟨unit, scale_eq⟩ := padicScale_exists_unit (padicPrimePowerUnit power) scale same_norm
  obtain ⟨shift, offset_eq⟩ := padicPivotResidue_decomposition power offset
  refine ⟨binaryLowerPivot unit shift, ?_⟩
  have mapped := congrArg (fun value : ℤ_[prime] => (value : ℚ_[prime])) offset_eq
  change (offset : ℚ_[prime]) =
    ((padicPivotResidue power offset).val : ℚ_[prime]) +
      (padicPrimePowerUnit power).val * (shift : ℚ_[prime]) at mapped
  rw [scale_eq, mapped]
  exact binaryLowerPivot_same_coset PadicInt.Coe.ringHom _ _ unit shift

end TernaryPeriodPolynomials.SphericalDetection.Helpers
