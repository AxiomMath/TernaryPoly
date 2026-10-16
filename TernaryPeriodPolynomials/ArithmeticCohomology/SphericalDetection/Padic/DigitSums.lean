module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.SphereProducts

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicDigitEquiv (prime power : ℕ) : Fin prime × Fin (prime ^ power) ≃ Fin (prime ^ (power + 1)) :=
  finProdFinEquiv.trans (finCongr (pow_succ' prime power).symm)

theorem padicDigitEquiv_val (prime power : ℕ) (digit : Fin prime) (residue : Fin (prime ^ power)) :
    (padicDigitEquiv prime power (digit, residue)).val = residue.val + prime ^ power * digit.val :=
  finProdFinEquiv_apply_val (digit, residue)

theorem padicDigit_sum {M : Type*} [AddCommMonoid M] (prime power : ℕ)
    (value : Fin (prime ^ (power + 1)) → M) :
    (∑ residue : Fin (prime ^ power), ∑ digit : Fin prime, value (padicDigitEquiv prime power (digit, residue))) =
      ∑ index, value index := by
  have equality := Equiv.sum_comp (padicDigitEquiv prime power) value
  rw [Fintype.sum_prod_type] at equality
  rw [Finset.sum_comm]
  exact equality

theorem sum_option_swap_value {A M : Type*} [Fintype A] [DecidableEq A] [AddCommMonoid M] (zero : A) (value : Option A → M) :
    (∑ index, value index) = value (some zero) + ∑ index : A, if index = zero then value none else value (some index) := by
  classical
  calc
    _ = ∑ index, value (Equiv.swap none (some zero) index) := (Equiv.sum_comp (Equiv.swap none (some zero)) value).symm
    _ = _ := by
      rw [Fintype.sum_option, Equiv.swap_apply_left]
      congr 1
      apply Finset.sum_congr rfl
      intro index _
      by_cases same : index = zero <;> simp [Equiv.swap_apply_def, same]

theorem binaryUpperPivot_integral_shift {prime : ℕ} [Fact prime.Prime] (power : ℕ)
    (base : ℚ_[prime]) (shift : ℤ_[prime]) :
    binaryUpperPivot (padicPrimePowerUnit power) (base + (prime : ℚ_[prime]) ^ power * (shift : ℚ_[prime])) =
      binaryUpperPivot (padicPrimePowerUnit power) base *
        GeneralLinearGroup.map PadicInt.Coe.ringHom (binaryUpperPivot 1 shift) := by
  have equality := binaryUpperPivot_same_coset PadicInt.Coe.ringHom (padicPrimePowerUnit power) base 1 shift
  simp only [map_one, mul_one] at equality
  exact equality

theorem binaryLowerPivot_integral_shift {prime : ℕ} [Fact prime.Prime] (power : ℕ)
    (base : ℚ_[prime]) (shift : ℤ_[prime]) :
    binaryLowerPivot (padicPrimePowerUnit power) (base + (prime : ℚ_[prime]) ^ power * (shift : ℚ_[prime])) =
      binaryLowerPivot (padicPrimePowerUnit power) base *
        GeneralLinearGroup.map PadicInt.Coe.ringHom (binaryLowerPivot 1 shift) := by
  have equality := binaryLowerPivot_same_coset PadicInt.Coe.ringHom (padicPrimePowerUnit power) base 1 shift
  simp only [map_one, mul_one] at equality
  exact equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
