module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.LowerCarry

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicResidueInverse {prime : ℕ} [Fact prime.Prime] : Equiv.Perm (Fin prime) := by
  letI : NeZero prime := ⟨Nat.Prime.ne_zero Fact.out⟩
  exact { toFun := fun index => ⟨((index.val : ZMod prime)⁻¹).val, ZMod.val_lt _⟩
          invFun := fun index => ⟨((index.val : ZMod prime)⁻¹).val, ZMod.val_lt _⟩
          left_inv := by
            intro index
            apply Fin.ext
            change (((((index.val : ZMod prime)⁻¹).val : ZMod prime)⁻¹).val) = index.val
            rw [ZMod.natCast_zmod_val, inv_inv, ZMod.val_natCast, Nat.mod_eq_of_lt index.isLt]
          right_inv := by
            intro index
            apply Fin.ext
            change (((((index.val : ZMod prime)⁻¹).val : ZMod prime)⁻¹).val) = index.val
            rw [ZMod.natCast_zmod_val, inv_inv, ZMod.val_natCast, Nat.mod_eq_of_lt index.isLt] }

theorem padicResidueInverse_cast {prime : ℕ} [Fact prime.Prime] (index : Fin prime) :
    ((padicResidueInverse index).val : ZMod prime) = (index.val : ZMod prime)⁻¹ :=
  ZMod.natCast_zmod_val _

theorem padicResidueInverse_zero {prime : ℕ} [Fact prime.Prime] :
    padicResidueInverse (⟨0, Nat.Prime.pos Fact.out⟩ : Fin prime) = ⟨0, Nat.Prime.pos Fact.out⟩ := by
  apply Fin.ext
  change (((0 : ℕ) : ZMod prime)⁻¹).val = 0
  rw [Nat.cast_zero, _root_.inv_zero, ZMod.val_zero]

theorem padicResidueInverse_mul {prime : ℕ} [Fact prime.Prime] (index : Fin prime) (nonzero : index.val ≠ 0) :
    (index.val : ZMod prime) * ((padicResidueInverse index).val : ZMod prime) = 1 := by
  rw [padicResidueInverse_cast]
  apply mul_inv_cancel₀
  intro zero
  apply nonzero
  exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ _).mp zero) index.isLt

theorem padicResidueInverse_quotient {prime : ℕ} [Fact prime.Prime] (index : Fin prime) (nonzero : index.val ≠ 0) :
    ∃ quotient : ℤ_[prime], (prime : ℤ_[prime]) * quotient +
      (index.val : ℤ_[prime]) * ((padicResidueInverse index).val : ℤ_[prime]) = 1 := by
  have divisible : (prime : ℤ) ∣ 1 - (index.val : ℤ) * ((padicResidueInverse index).val : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ prime).mp
    push_cast
    rw [padicResidueInverse_mul index nonzero, sub_self]
  obtain ⟨quotient, equality⟩ := divisible
  refine ⟨(quotient : ℤ_[prime]), ?_⟩
  have mapped := congrArg (Int.castRingHom ℤ_[prime]) equality
  simp only [map_sub, map_one, map_mul, Int.coe_castRingHom, Int.cast_natCast] at mapped
  linear_combination -mapped

end TernaryPeriodPolynomials.SphericalDetection.Helpers
