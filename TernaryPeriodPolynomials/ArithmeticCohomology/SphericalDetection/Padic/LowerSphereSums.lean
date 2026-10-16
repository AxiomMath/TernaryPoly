module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.UpperSphereSums

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicLowerSphere_backward_sum {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (base : GeneralLinearGroup (Fin 2) ℚ_[prime]) (power : ℕ) :
    (∑ index : Fin (prime ^ (power + 1)), value (base * binaryLowerPivot (padicPrimePowerUnit (power + 1))
      ((prime * index.val : ℕ) : ℚ_[prime]))) =
      prime • ∑ index : Fin (prime ^ power), value (base * binaryLowerPivot (padicPrimePowerUnit (power + 1))
        ((prime * index.val : ℕ) : ℚ_[prime])) := by
  rw [← padicDigit_sum prime power (fun index =>
    value (base * binaryLowerPivot (padicPrimePowerUnit (power + 1)) ((prime * index.val : ℕ) : ℚ_[prime])))]
  have equal (residue : Fin (prime ^ power)) (digit : Fin prime) :
      value (base * binaryLowerPivot (padicPrimePowerUnit (power + 1))
        ((prime * (padicDigitEquiv prime power (digit, residue)).val : ℕ) : ℚ_[prime])) =
      value (base * binaryLowerPivot (padicPrimePowerUnit (power + 1)) ((prime * residue.val : ℕ) : ℚ_[prime])) := by
    have cast : ((prime * (padicDigitEquiv prime power (digit, residue)).val : ℕ) : ℚ_[prime]) =
        ((prime * residue.val : ℕ) : ℚ_[prime]) + (prime : ℚ_[prime]) ^ (power + 1) *
          ((digit.val : ℤ_[prime]) : ℚ_[prime]) := by
      simp only [padicDigitEquiv_val, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, PadicInt.coe_natCast, pow_succ']
      ring
    rw [cast, binaryLowerPivot_integral_shift, ← mul_assoc, fixed]
  simp_rw [equal]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [Finset.smul_sum]

theorem padicLowerSphere_step_sum {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (power : ℕ) (base : ℚ_[prime]) :
    (∑ index : Option (Fin prime), value (binaryLowerPivot (padicPrimePowerUnit (power + 1)) base *
      padicPrimeForwardRepresentative index)) =
      value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) * binaryLowerPivot (padicPrimePowerUnit power) base) +
      ∑ digit : Fin prime, value (binaryLowerPivot (padicPrimePowerUnit (power + 2))
        (base + (prime : ℚ_[prime]) ^ (power + 1) * (digit.val : ℚ_[prime]))) := by
  let zero : Fin prime := ⟨0, Nat.Prime.pos Fact.out⟩
  rw [sum_option_swap_value zero]
  have zero_term : value (binaryLowerPivot (padicPrimePowerUnit (power + 1)) base *
      padicPrimeForwardRepresentative (some zero)) =
      value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) * binaryLowerPivot (padicPrimePowerUnit power) base) := by
    change value (binaryLowerPivot (padicPrimePowerUnit (power + 1)) base * binaryUpperPivot (padicPrimePowerUnit 1) (0 : ℕ)) = _
    rw [Nat.cast_zero, padicLowerPivot_mul_upper_zero]
  rw [zero_term]
  apply congrArg (fun result => value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) *
    binaryLowerPivot (padicPrimePowerUnit power) base) + result)
  have equal (index : Fin prime) :
      (if index = zero then value (binaryLowerPivot (padicPrimePowerUnit (power + 1)) base * padicPrimeForwardRepresentative none)
        else value (binaryLowerPivot (padicPrimePowerUnit (power + 1)) base * padicPrimeForwardRepresentative (some index))) =
      value (binaryLowerPivot (padicPrimePowerUnit (power + 2))
        (base + (prime : ℚ_[prime]) ^ (power + 1) * ((padicResidueInverse index).val : ℚ_[prime]))) := by
    by_cases same : index = zero
    · subst index
      rw [ite_eq_left rfl, padicResidueInverse_zero]
      simp only [padicPrimeForwardRepresentative, padicLowerPivot_mul_lower_prime, Nat.cast_zero, mul_zero, add_zero]
    · have nonzero : index.val ≠ 0 := fun equality => same (Fin.ext equality)
      obtain ⟨compact, equality⟩ := padicLowerPivot_mul_upper_nonzero (power + 1) base index nonzero
      rw [ite_eq_right same]
      change value (binaryLowerPivot (padicPrimePowerUnit (power + 1)) base *
        binaryUpperPivot (padicPrimePowerUnit 1) (index.val : ℚ_[prime])) = _
      rw [equality, fixed]
  simp_rw [equal]
  exact Equiv.sum_comp padicResidueInverse (fun digit : Fin prime => value (binaryLowerPivot (padicPrimePowerUnit (power + 2))
    (base + (prime : ℚ_[prime]) ^ (power + 1) * (digit.val : ℚ_[prime]))))

theorem padicLowerSphere_forward_sum {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M) (power : ℕ) :
    (∑ residue : Fin (prime ^ power), ∑ digit : Fin prime,
      value (binaryLowerPivot (padicPrimePowerUnit (power + 2))
        (((prime * residue.val : ℕ) : ℚ_[prime]) + (prime : ℚ_[prime]) ^ (power + 1) * (digit.val : ℚ_[prime])))) =
      ∑ index : Fin (prime ^ (power + 1)),
        value (binaryLowerPivot (padicPrimePowerUnit (power + 2)) ((prime * index.val : ℕ) : ℚ_[prime])) := by
  rw [← padicDigit_sum prime power (fun index =>
    value (binaryLowerPivot (padicPrimePowerUnit (power + 2)) ((prime * index.val : ℕ) : ℚ_[prime])))]
  apply Finset.sum_congr rfl
  intro residue _
  apply Finset.sum_congr rfl
  intro digit _
  have cast : ((prime * (padicDigitEquiv prime power (digit, residue)).val : ℕ) : ℚ_[prime]) =
      ((prime * residue.val : ℕ) : ℚ_[prime]) + (prime : ℚ_[prime]) ^ (power + 1) * (digit.val : ℚ_[prime]) := by
    simp only [padicDigitEquiv_val, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, pow_succ']
    ring
  rw [cast]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
