module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.LowerSphereSums

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicSphereSum_step_raw {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (power : ℕ) :
    padicSphereSum (fun matrix => ∑ index : Option (Fin prime), value (matrix * padicPrimeForwardRepresentative index)) (power + 1) =
      padicSphereSum value (power + 2) +
      prime • (∑ index : Fin (prime ^ power), value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) *
        binaryUpperPivot (padicPrimePowerUnit power) (index.val : ℚ_[prime]))) +
      ∑ index : Fin (prime ^ power), value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) *
        binaryLowerPivot (padicPrimePowerUnit power) ((prime * index.val : ℕ) : ℚ_[prime])) := by
  have upper :
      (∑ residue : Fin (prime ^ (power + 1)), ∑ index : Option (Fin prime),
        value (binaryUpperPivot (padicPrimePowerUnit (power + 1)) (residue.val : ℚ_[prime]) * padicPrimeForwardRepresentative index)) =
      prime • (∑ index : Fin (prime ^ power), value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) *
        binaryUpperPivot (padicPrimePowerUnit power) (index.val : ℚ_[prime]))) +
      ∑ index : Fin (prime ^ (power + 2)), value (binaryUpperPivot (padicPrimePowerUnit (power + 2)) (index.val : ℚ_[prime])) := by
    simp_rw [Fintype.sum_option, padicPrimeForwardRepresentative, padicUpperPivot_mul_lower_prime]
    rw [Finset.sum_add_distrib, padicUpperSphere_backward_sum value fixed,
      padicUpperSphere_forward_sum value (power + 1)]
  have lower :
      (∑ residue : Fin (prime ^ power), ∑ index : Option (Fin prime),
        value (binaryLowerPivot (padicPrimePowerUnit (power + 1)) ((prime * residue.val : ℕ) : ℚ_[prime]) *
          padicPrimeForwardRepresentative index)) =
      (∑ index : Fin (prime ^ power), value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) *
        binaryLowerPivot (padicPrimePowerUnit power) ((prime * index.val : ℕ) : ℚ_[prime]))) +
      ∑ index : Fin (prime ^ (power + 1)), value (binaryLowerPivot (padicPrimePowerUnit (power + 2))
        ((prime * index.val : ℕ) : ℚ_[prime])) := by
    simp_rw [padicLowerSphere_step_sum value fixed power]
    rw [Finset.sum_add_distrib, padicLowerSphere_forward_sum]
  rw [padicSphereSum_succ, upper, lower, padicSphereSum_succ]
  ac_rfl

theorem padicSphereSum_step_succ {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (power : ℕ) :
    padicSphereSum (fun matrix => ∑ index : Option (Fin prime), value (matrix * padicPrimeForwardRepresentative index)) (power + 2) =
      padicSphereSum value (power + 3) +
        prime • padicSphereSum (fun matrix => value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) * matrix))
          (power + 1) := by
  rw [padicSphereSum_step_raw value fixed (power + 1), padicLowerSphere_backward_sum value fixed,
    padicSphereSum_succ (fun matrix => value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) * matrix)) power,
    smul_add, add_assoc]

theorem padicPrimePowerUnit_zero {prime : ℕ} [Fact prime.Prime] : padicPrimePowerUnit (prime := prime) 0 = 1 := by
  apply Units.ext
  exact pow_zero _

theorem binaryUpperPivot_one_zero {R : Type*} [CommRing R] : (binaryUpperPivot 1 0 : GeneralLinearGroup (Fin 2) R) = 1 := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> simp [binaryUpperPivot]

theorem binaryLowerPivot_one_zero {R : Type*} [CommRing R] : (binaryLowerPivot 1 0 : GeneralLinearGroup (Fin 2) R) = 1 := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;> simp [binaryLowerPivot]

theorem padicSphereSum_step_one {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix) :
    padicSphereSum (fun matrix => ∑ index : Option (Fin prime), value (matrix * padicPrimeForwardRepresentative index)) 1 =
      padicSphereSum value 2 + (prime + 1) • value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1)) := by
  rw [padicSphereSum_step_raw value fixed 0]
  have upper_zero : (∑ index : Fin (prime ^ 0), value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) *
      binaryUpperPivot (padicPrimePowerUnit 0) (index.val : ℚ_[prime]))) =
      value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1)) := by
    change (∑ index : Fin 1, value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) *
      binaryUpperPivot (padicPrimePowerUnit 0) (index.val : ℚ_[prime]))) = _
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, Nat.cast_zero, padicPrimePowerUnit_zero, binaryUpperPivot_one_zero, mul_one]
  have lower_zero : (∑ index : Fin (prime ^ 0), value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) *
      binaryLowerPivot (padicPrimePowerUnit 0) ((prime * index.val : ℕ) : ℚ_[prime]))) =
      value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1)) := by
    change (∑ index : Fin 1, value (GeneralLinearGroup.scalar (Fin 2) (padicPrimePowerUnit 1) *
      binaryLowerPivot (padicPrimePowerUnit 0) ((prime * index.val : ℕ) : ℚ_[prime]))) = _
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, Nat.mul_zero, Nat.cast_zero, padicPrimePowerUnit_zero, binaryLowerPivot_one_zero, mul_one]
  rw [upper_zero, lower_zero]
  rw [add_nsmul, one_nsmul, add_assoc]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
