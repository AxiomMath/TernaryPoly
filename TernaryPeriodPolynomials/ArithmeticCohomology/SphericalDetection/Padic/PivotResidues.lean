module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Local.BinaryTriangularCosets

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicPivotResidue {prime : ℕ} [Fact prime.Prime] (power : ℕ) (value : ℤ_[prime]) : Fin (prime ^ power) :=
  letI : NeZero (prime ^ power) := ⟨pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)⟩
  ⟨(PadicInt.toZModPow power value).val, (PadicInt.toZModPow power value).val_lt⟩

theorem padicPivotResidue_spec {prime : ℕ} [Fact prime.Prime] (power : ℕ) (value : ℤ_[prime]) :
    (prime : ℤ_[prime]) ^ power ∣ value - ((padicPivotResidue power value).val : ℤ_[prime]) := by
  apply Ideal.mem_span_singleton.mp
  rw [← PadicInt.ker_toZModPow]
  change PadicInt.toZModPow power (value - ((padicPivotResidue power value).val : ℤ_[prime])) = 0
  rw [map_sub, map_natCast]
  change PadicInt.toZModPow power value - ((PadicInt.toZModPow power value).val : ZMod (prime ^ power)) = 0
  rw [ZMod.natCast_zmod_val, sub_self]

theorem padicPivotResidue_decomposition {prime : ℕ} [Fact prime.Prime] (power : ℕ) (value : ℤ_[prime]) :
    ∃ shift : ℤ_[prime], value = ((padicPivotResidue power value).val : ℤ_[prime]) +
      (prime : ℤ_[prime]) ^ power * shift := by
  obtain ⟨shift, equality⟩ := padicPivotResidue_spec power value
  exact ⟨shift, sub_eq_iff_eq_add.mp equality |>.trans (add_comm _ _)⟩

theorem padicPivotResidue_unique {prime : ℕ} [Fact prime.Prime] (power : ℕ) (value : ℤ_[prime])
    (index : Fin (prime ^ power))
    (congruent : (prime : ℤ_[prime]) ^ power ∣ value - (index.val : ℤ_[prime])) :
    index = padicPivotResidue power value := by
  have reduced : PadicInt.toZModPow power (value - (index.val : ℤ_[prime])) = 0 := by
    change value - (index.val : ℤ_[prime]) ∈ RingHom.ker (PadicInt.toZModPow power)
    rw [PadicInt.ker_toZModPow]
    exact Ideal.mem_span_singleton.mpr congruent
  rw [map_sub, map_natCast, sub_eq_zero] at reduced
  apply Fin.ext
  change index.val = (PadicInt.toZModPow power value).val
  rw [reduced, ZMod.val_natCast, Nat.mod_eq_of_lt index.isLt]

theorem padicPivotResidue_divisible {prime : ℕ} [Fact prime.Prime] (power : ℕ) (value : ℤ_[prime])
    (positive : 0 < power) (divisible : (prime : ℤ_[prime]) ∣ value) :
    prime ∣ (padicPivotResidue power value).val := by
  have power_divides : (prime : ℤ_[prime]) ∣ (prime : ℤ_[prime]) ^ power := dvd_pow_self _ (ne_of_gt positive)
  have residue_divides : (prime : ℤ_[prime]) ∣ ((padicPivotResidue power value).val : ℤ_[prime]) := by
    have difference := power_divides.trans (padicPivotResidue_spec power value)
    simpa only [sub_sub_cancel] using dvd_sub divisible difference
  have integer_divides : (prime : ℤ) ∣ ((padicPivotResidue power value).val : ℤ) := by
    have lifted : (prime : ℤ_[prime]) ^ 1 ∣ (((padicPivotResidue power value).val : ℤ) : ℤ_[prime]) := by
      simpa only [pow_one, Int.cast_natCast] using residue_divides
    simpa only [pow_one] using (PadicInt.pow_p_dvd_int_iff 1 _).mp lifted
  exact_mod_cast integer_divides

end TernaryPeriodPolynomials.SphericalDetection.Helpers
