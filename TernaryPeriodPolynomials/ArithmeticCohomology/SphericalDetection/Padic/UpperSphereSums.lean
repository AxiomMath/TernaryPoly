module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.DigitSums

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicUpperSphere_forward_sum {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M) (power : ℕ) :
    (∑ residue : Fin (prime ^ power), ∑ digit : Fin prime,
      value (binaryUpperPivot (padicPrimePowerUnit power) (residue.val : ℚ_[prime]) *
        binaryUpperPivot (padicPrimePowerUnit 1) (digit.val : ℚ_[prime]))) =
      ∑ index : Fin (prime ^ (power + 1)),
        value (binaryUpperPivot (padicPrimePowerUnit (power + 1)) (index.val : ℚ_[prime])) := by
  rw [← padicDigit_sum prime power (fun index =>
    value (binaryUpperPivot (padicPrimePowerUnit (power + 1)) (index.val : ℚ_[prime])))]
  apply Finset.sum_congr rfl
  intro residue _
  apply Finset.sum_congr rfl
  intro digit _
  rw [padicUpperPivot_mul_upper_prime, padicDigitEquiv_val, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]

theorem padicUpperSphere_backward_sum {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (base : GeneralLinearGroup (Fin 2) ℚ_[prime]) (power : ℕ) :
    (∑ index : Fin (prime ^ (power + 1)), value (base * binaryUpperPivot (padicPrimePowerUnit power) (index.val : ℚ_[prime]))) =
      prime • ∑ index : Fin (prime ^ power), value (base * binaryUpperPivot (padicPrimePowerUnit power) (index.val : ℚ_[prime])) := by
  rw [← padicDigit_sum prime power (fun index =>
    value (base * binaryUpperPivot (padicPrimePowerUnit power) (index.val : ℚ_[prime])))]
  have equal (residue : Fin (prime ^ power)) (digit : Fin prime) :
      value (base * binaryUpperPivot (padicPrimePowerUnit power)
        ((padicDigitEquiv prime power (digit, residue)).val : ℚ_[prime])) =
      value (base * binaryUpperPivot (padicPrimePowerUnit power) (residue.val : ℚ_[prime])) := by
    have cast : ((padicDigitEquiv prime power (digit, residue)).val : ℚ_[prime]) =
        (residue.val : ℚ_[prime]) + (prime : ℚ_[prime]) ^ power * ((digit.val : ℤ_[prime]) : ℚ_[prime]) := by
      simp only [padicDigitEquiv_val, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, PadicInt.coe_natCast]
    rw [cast, binaryUpperPivot_integral_shift, ← mul_assoc, fixed]
  simp_rw [equal]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.smul_sum]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
