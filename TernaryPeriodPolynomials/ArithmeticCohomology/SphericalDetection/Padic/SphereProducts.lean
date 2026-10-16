module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.InverseDigits

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicPrimePowerUnit_succ {prime : ℕ} [Fact prime.Prime] (power : ℕ) :
    padicPrimePowerUnit 1 * padicPrimePowerUnit (prime := prime) power = padicPrimePowerUnit (power + 1) := by
  apply Units.ext
  change (prime : ℚ_[prime]) ^ 1 * (prime : ℚ_[prime]) ^ power = (prime : ℚ_[prime]) ^ (power + 1)
  rw [pow_one, pow_succ']

theorem padicUpperPivot_mul_upper_prime {prime : ℕ} [Fact prime.Prime] (power : ℕ) (base offset : ℚ_[prime]) :
    binaryUpperPivot (padicPrimePowerUnit power) base * binaryUpperPivot (padicPrimePowerUnit 1) offset =
      binaryUpperPivot (padicPrimePowerUnit (power + 1)) (base + (prime : ℚ_[prime]) ^ power * offset) := by
  rw [binaryUpperPivot_mul, mul_comm (padicPrimePowerUnit power), padicPrimePowerUnit_succ]
  rfl

theorem padicLowerPivot_mul_lower_prime {prime : ℕ} [Fact prime.Prime] (power : ℕ) (base : ℚ_[prime]) :
    binaryLowerPivot (padicPrimePowerUnit power) base * binaryLowerPivot (padicPrimePowerUnit 1) 0 =
      binaryLowerPivot (padicPrimePowerUnit (power + 1)) base := by
  rw [binaryLowerPivot_mul, mul_comm (padicPrimePowerUnit power), padicPrimePowerUnit_succ, mul_zero, add_zero]

theorem padicUpperPivot_mul_lower_prime {prime : ℕ} [Fact prime.Prime] (power : ℕ) (base : ℚ_[prime]) :
    binaryUpperPivot (padicPrimePowerUnit (power + 1)) base * binaryLowerPivot (padicPrimePowerUnit 1) 0 =
      GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) * binaryUpperPivot (padicPrimePowerUnit power) base := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryUpperPivot, binaryLowerPivot, padicPrimePowerUnit, GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.natCast_apply, Matrix.mul_apply, Fin.sum_univ_two, pow_succ', mul_comm]

theorem padicLowerPivot_mul_upper_zero {prime : ℕ} [Fact prime.Prime] (power : ℕ) (base : ℚ_[prime]) :
    binaryLowerPivot (padicPrimePowerUnit (power + 1)) base * binaryUpperPivot (padicPrimePowerUnit 1) 0 =
      GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) * binaryLowerPivot (padicPrimePowerUnit power) base := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryUpperPivot, binaryLowerPivot, padicPrimePowerUnit, GeneralLinearGroup.coe_scalar,
      Matrix.scalar, Matrix.natCast_apply, Matrix.mul_apply, Fin.sum_univ_two, pow_succ', mul_comm]

theorem padicLowerPivot_mul_upper_nonzero {prime : ℕ} [Fact prime.Prime] (power : ℕ) (base : ℚ_[prime])
    (index : Fin prime) (nonzero : index.val ≠ 0) :
    ∃ compact : GeneralLinearGroup (Fin 2) ℤ_[prime],
      binaryLowerPivot (padicPrimePowerUnit power) base *
        binaryUpperPivot (padicPrimePowerUnit 1) (index.val : ℚ_[prime]) =
        binaryLowerPivot (padicPrimePowerUnit (power + 1))
          (base + (prime : ℚ_[prime]) ^ power * ((padicResidueInverse index).val : ℚ_[prime])) *
          GeneralLinearGroup.map PadicInt.Coe.ringHom compact := by
  obtain ⟨quotient, relation⟩ := padicResidueInverse_quotient index nonzero
  have mapped_relation : (padicPrimePowerUnit (prime := prime) 1).val * (quotient : ℚ_[prime]) +
      (index.val : ℚ_[prime]) * ((padicResidueInverse index).val : ℚ_[prime]) = 1 := by
    have mapped := congrArg PadicInt.Coe.ringHom relation
    simp only [map_add, map_mul, map_natCast, map_one] at mapped
    change (prime : ℚ_[prime]) * (quotient : ℚ_[prime]) +
      (index.val : ℚ_[prime]) * ((padicResidueInverse index).val : ℚ_[prime]) = 1 at mapped
    simpa only [padicPrimePowerUnit, Units.val_mk0, pow_one] using mapped
  let compact := binaryLowerCarryCompact (prime : ℤ_[prime]) (index.val : ℤ_[prime])
    ((padicResidueInverse index).val : ℤ_[prime]) quotient relation
  have compact_map : GeneralLinearGroup.map PadicInt.Coe.ringHom compact =
      binaryLowerCarryCompact (padicPrimePowerUnit (prime := prime) 1).val (index.val : ℚ_[prime])
        ((padicResidueInverse index).val : ℚ_[prime]) (quotient : ℚ_[prime]) mapped_relation := by
    apply Units.ext
    funext row column
    rw [GeneralLinearGroup.map_apply]
    change PadicInt.Coe.ringHom ((binaryLowerCarryCompact _ _ _ _ relation).val row column) = _
    rw [binaryLowerCarryCompact_val, binaryLowerCarryCompact_val]
    fin_cases row <;> fin_cases column <;> simp [padicPrimePowerUnit]
    all_goals rfl
  refine ⟨compact, ?_⟩
  have carrying := binaryLowerPivot_upper_carry (padicPrimePowerUnit 1) (padicPrimePowerUnit power)
    base (index.val : ℚ_[prime]) ((padicResidueInverse index).val : ℚ_[prime]) (quotient : ℚ_[prime]) mapped_relation
  rw [padicPrimePowerUnit_succ, ← compact_map] at carrying
  exact carrying

end TernaryPeriodPolynomials.SphericalDetection.Helpers
