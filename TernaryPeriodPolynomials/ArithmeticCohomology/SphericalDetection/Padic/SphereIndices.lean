module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Cusp.PadicSphereOperator

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicLowerIndexEquiv {prime : ℕ} [Fact prime.Prime] (power : ℕ) :
    Fin (prime ^ power) ≃ {index : Fin (prime ^ (power + 1)) // prime ∣ index.val} where
  toFun index := ⟨⟨prime * index.val, by
    rw [pow_succ']
    exact Nat.mul_lt_mul_of_pos_left index.isLt (Nat.Prime.pos Fact.out)⟩, dvd_mul_right _ _⟩
  invFun index := ⟨index.val.val / prime, by
    apply (Nat.div_lt_iff_lt_mul (Nat.Prime.pos Fact.out)).mpr
    simpa only [← pow_succ] using index.val.isLt⟩
  left_inv index := by
    apply Fin.ext
    exact Nat.mul_div_cancel_left index.val (Nat.Prime.pos Fact.out)
  right_inv index := by
    apply Subtype.ext
    apply Fin.ext
    simpa only [Nat.mul_comm] using Nat.div_mul_cancel index.property

theorem padicLowerIndexEquiv_val {prime : ℕ} [Fact prime.Prime] (power : ℕ) (index : Fin (prime ^ power)) :
    (padicLowerIndexEquiv power index).val.val = prime * index.val := rfl

def padicSphereRepresentative {prime : ℕ} [Fact prime.Prime] (power : ℕ) :
    Fin (prime ^ (power + 1)) ⊕ Fin (prime ^ power) → GeneralLinearGroup (Fin 2) ℚ_[prime]
  | .inl index => binaryUpperPivot (padicPrimePowerUnit (power + 1)) (index.val : ℚ_[prime])
  | .inr index => binaryLowerPivot (padicPrimePowerUnit (power + 1)) ((prime * index.val : ℕ) : ℚ_[prime])

def padicSphereSum {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M) : ℕ → M
  | 0 => value 1
  | power + 1 => ∑ index : Fin (prime ^ (power + 1)) ⊕ Fin (prime ^ power), value (padicSphereRepresentative power index)

theorem padicSphereSum_zero {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M) : padicSphereSum value 0 = value 1 := rfl

theorem padicSphereSum_succ {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M) (power : ℕ) :
    padicSphereSum value (power + 1) =
      (∑ index : Fin (prime ^ (power + 1)), value (binaryUpperPivot (padicPrimePowerUnit (power + 1)) (index.val : ℚ_[prime]))) +
      ∑ index : Fin (prime ^ power),
        value (binaryLowerPivot (padicPrimePowerUnit (power + 1)) ((prime * index.val : ℕ) : ℚ_[prime])) := by
  simp only [padicSphereSum, Fintype.sum_sum_type, padicSphereRepresentative]

theorem padicSphereSum_eq_primitive {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M) (power : ℕ) :
    padicSphereSum value (power + 1) =
      ∑ index : Fin (prime ^ (power + 1)) ⊕ {index : Fin (prime ^ (power + 1)) // prime ∣ index.val},
        value (padicPrimitiveRepresentative (power + 1) index) := by
  rw [padicSphereSum_succ, Fintype.sum_sum_type]
  apply congrArg₂ (· + ·) rfl
  exact Equiv.sum_comp (padicLowerIndexEquiv power)
    (fun index => value (padicPrimitiveRepresentative (power + 1) (.inr index)))

theorem padicSphereSum_one {prime : ℕ} [Fact prime.Prime] {M : Type*} [AddCommMonoid M]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → M) :
    padicSphereSum value 1 = ∑ index : Option (Fin prime), value (padicPrimeForwardRepresentative index) := by
  rw [padicSphereSum_eq_primitive, padicPrimitive_one_sum]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
