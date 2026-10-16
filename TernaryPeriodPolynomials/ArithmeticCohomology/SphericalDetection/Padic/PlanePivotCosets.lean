module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.BinaryPivotCosets

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicPlanePivotOffset {prime : ℕ} [Fact prime.Prime] (pivot : ℚ_[prime]ˣ) (other : ℚ_[prime])
    (dominant : ‖other‖ ≤ ‖pivot.val‖) : ℤ_[prime] :=
  ⟨-other * pivot.inv, by
    change ‖-other * (pivot⁻¹).val‖ ≤ 1
    rw [Units.val_inv_eq_inv_val, ← div_eq_mul_inv, norm_div, norm_neg]
    exact (div_le_one (norm_pos_iff.mpr pivot.ne_zero)).mpr dominant⟩

theorem padicPlaneFirstPivot_coset {prime : ℕ} [Fact prime.Prime] (power : ℕ)
    (pivot : ℚ_[prime]ˣ) (other : ℚ_[prime]) (dominant : ‖other‖ ≤ ‖pivot.val‖)
    (shell : ‖pivot.val⁻¹‖ = ‖(prime : ℚ_[prime]) ^ power‖) :
    ∃ (index : Fin (prime ^ power)) (compact : GeneralLinearGroup (Fin 2) ℤ_[prime]),
      planeFirstPivotBinary pivot other = padicUpperPrimitiveRepresentative power index *
        GeneralLinearGroup.map PadicInt.Coe.ringHom compact := by
  let offset := padicPlanePivotOffset pivot other dominant
  have same_norm : ‖(-pivot⁻¹).val‖ = ‖(prime : ℚ_[prime]) ^ power‖ := by
    simpa only [Units.val_neg, Units.val_inv_eq_inv_val, norm_neg] using shell
  obtain ⟨compact, factors⟩ := padicUpperPivot_normalize power (-pivot⁻¹) offset same_norm
  refine ⟨padicPivotResidue power offset, compact * binaryPivotSwap, ?_⟩
  rw [planeFirstPivotBinary_upper]
  change binaryUpperPivot (-pivot⁻¹) (offset : ℚ_[prime]) * binaryPivotSwap = _
  rw [factors, map_mul, binaryPivotSwap_map, mul_assoc]

theorem padicPlanePivotOffset_divisible {prime : ℕ} [Fact prime.Prime]
    (pivot : ℚ_[prime]ˣ) (other : ℚ_[prime]) (dominant : ‖other‖ < ‖pivot.val‖) :
    (prime : ℤ_[prime]) ∣ padicPlanePivotOffset pivot other dominant.le := by
  apply (PadicInt.norm_lt_one_iff_dvd _).mp
  change ‖-other * (pivot⁻¹).val‖ < 1
  rw [Units.val_inv_eq_inv_val, ← div_eq_mul_inv, norm_div, norm_neg]
  exact (div_lt_one (norm_pos_iff.mpr pivot.ne_zero)).mpr dominant

theorem padicPlaneSecondPivot_coset {prime : ℕ} [Fact prime.Prime] (power : ℕ)
    (positive : 0 < power) (pivot : ℚ_[prime]ˣ) (other : ℚ_[prime])
    (dominant : ‖other‖ < ‖pivot.val‖)
    (shell : ‖pivot.val⁻¹‖ = ‖(prime : ℚ_[prime]) ^ power‖) :
    ∃ (index : Fin (prime ^ power)), prime ∣ index.val ∧
      ∃ compact : GeneralLinearGroup (Fin 2) ℤ_[prime],
        planeSecondPivotBinary pivot other = padicLowerPrimitiveRepresentative power index *
          GeneralLinearGroup.map PadicInt.Coe.ringHom compact := by
  let offset := padicPlanePivotOffset pivot other dominant.le
  have same_norm : ‖(-pivot⁻¹).val‖ = ‖(prime : ℚ_[prime]) ^ power‖ := by
    simpa only [Units.val_neg, Units.val_inv_eq_inv_val, norm_neg] using shell
  obtain ⟨compact, factors⟩ := padicLowerPivot_normalize power (-pivot⁻¹) offset same_norm
  refine ⟨padicPivotResidue power offset, padicPivotResidue_divisible power offset positive
    (padicPlanePivotOffset_divisible pivot other dominant), compact, ?_⟩
  rw [planeSecondPivotBinary_lower]
  exact factors

end TernaryPeriodPolynomials.SphericalDetection.Helpers
