module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PlaneInductionCoordinates

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicPivotShell_large {prime : ℕ} [Fact prime.Prime] {power : ℕ} (positive : 0 < power)
    {value : ℚ_[prime]} (member : value ∈ padicPivotShell power) : 1 < ‖value‖ := by
  change ‖value‖ = (prime : ℝ) ^ power at member
  rw [member]
  exact_mod_cast Nat.one_lt_pow (ne_of_gt positive) (Nat.Prime.one_lt Fact.out)

theorem padicFirstPivot_region_factorization {prime : ℕ} [Fact prime.Prime]
    (power : ℕ) (pivot : ℚ_[prime]ˣ) (other : ℚ_[prime]) (index : Fin (prime ^ power))
    (member : (pivot.val, other) ∈ padicPivotRegion power index) :
    ∃ compact : GeneralLinearGroup (Fin 2) ℤ_[prime],
      planeFirstPivotBinary pivot other = padicUpperPrimitiveRepresentative power index *
        GeneralLinearGroup.map PadicInt.Coe.ringHom compact := by
  have residue := (padicPivotRegion_mem_iff_residue power pivot other index member.1).mp member
  obtain ⟨integral, same, residue_eq⟩ := (padicResidueClass_mem power index _).mp residue
  have same_norm : ‖(-pivot⁻¹).val‖ = ‖(prime : ℚ_[prime]) ^ power‖ := by
    simpa only [Units.val_neg, Units.val_inv_eq_inv_val, norm_neg] using padicPivotShell_inverse_norm member.1
  obtain ⟨compact, factors⟩ := padicUpperPivot_normalize power (-pivot⁻¹) integral same_norm
  rw [residue_eq, same] at factors
  refine ⟨compact * binaryPivotSwap, ?_⟩
  rw [planeFirstPivotBinary_upper, factors, map_mul, binaryPivotSwap_map, mul_assoc]

theorem padicSecondPivot_region_factorization {prime : ℕ} [Fact prime.Prime]
    (power : ℕ) (pivot : ℚ_[prime]ˣ) (other : ℚ_[prime]) (index : Fin (prime ^ power))
    (member : (pivot.val, other) ∈ padicPivotRegion power index) :
    ∃ compact : GeneralLinearGroup (Fin 2) ℤ_[prime],
      planeSecondPivotBinary pivot other = padicLowerPrimitiveRepresentative power index *
        GeneralLinearGroup.map PadicInt.Coe.ringHom compact := by
  have residue := (padicPivotRegion_mem_iff_residue power pivot other index member.1).mp member
  obtain ⟨integral, same, residue_eq⟩ := (padicResidueClass_mem power index _).mp residue
  have same_norm : ‖(-pivot⁻¹).val‖ = ‖(prime : ℚ_[prime]) ^ power‖ := by
    simpa only [Units.val_neg, Units.val_inv_eq_inv_val, norm_neg] using padicPivotShell_inverse_norm member.1
  obtain ⟨compact, factors⟩ := padicLowerPivot_normalize power (-pivot⁻¹) integral same_norm
  rw [residue_eq, same] at factors
  exact ⟨compact, (planeSecondPivotBinary_lower pivot other).trans factors⟩

theorem padicPlanePivotCoordinates_first_region {prime : ℕ} [Fact prime.Prime]
    (power : ℕ) (positive : 0 < power) (index : Fin (prime ^ power))
    (pair : ℚ_[prime] × ℚ_[prime]) (member : pair ∈ padicPivotRegion power index) :
    ∃ compact : GeneralLinearGroup (Fin 2) ℤ_[prime],
      (padicPlanePivotCoordinates pair.1 pair.2).block = padicUpperPrimitiveRepresentative power index *
        GeneralLinearGroup.map PadicInt.Coe.ringHom compact := by
  have dominant : ‖pair.2‖ ≤ ‖pair.1‖ := by
    have union_mem : pair ∈ ⋃ index : Fin (prime ^ power), padicPivotRegion power index :=
      Set.mem_iUnion.mpr ⟨index, member⟩
    rw [padicPivotRegion_union] at union_mem
    exact union_mem.2
  rw [padicPlanePivotCoordinates_first pair.1 pair.2 (padicPivotShell_large positive member.1) dominant]
  exact padicFirstPivot_region_factorization power _ pair.2 index member

theorem padicPlanePivotCoordinates_second_region {prime : ℕ} [Fact prime.Prime]
    (power : ℕ) (positive : 0 < power) (index : Fin (prime ^ power)) (divisible : prime ∣ index.val)
    (pair : ℚ_[prime] × ℚ_[prime]) (member : pair.swap ∈ padicPivotRegion power index) :
    ∃ compact : GeneralLinearGroup (Fin 2) ℤ_[prime],
      (padicPlanePivotCoordinates pair.1 pair.2).block = padicLowerPrimitiveRepresentative power index *
        GeneralLinearGroup.map PadicInt.Coe.ringHom compact := by
  have dominant : ‖pair.1‖ < ‖pair.2‖ :=
    (padicPivotRegion_strict_iff power positive index pair.swap member).mpr divisible
  rw [padicPlanePivotCoordinates_second pair.1 pair.2 (padicPivotShell_large positive member.1) dominant]
  exact padicSecondPivot_region_factorization power _ pair.1 index member

theorem padicPlanePivotValue_first_region {prime : ℕ} [Fact prime.Prime]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (power : ℕ) (positive : 0 < power) (index : Fin (prime ^ power))
    (pair : ℚ_[prime] × ℚ_[prime]) (member : pair ∈ padicPivotRegion power index) :
    value (padicPlanePivotCoordinates pair.1 pair.2).block = value (padicUpperPrimitiveRepresentative power index) := by
  obtain ⟨compact, factors⟩ := padicPlanePivotCoordinates_first_region power positive index pair member
  rw [factors, fixed]

theorem padicPlanePivotValue_second_region {prime : ℕ} [Fact prime.Prime]
    (value : GeneralLinearGroup (Fin 2) ℚ_[prime] → ℂ)
    (fixed : ∀ matrix compact, value (matrix * GeneralLinearGroup.map PadicInt.Coe.ringHom compact) = value matrix)
    (power : ℕ) (positive : 0 < power) (index : Fin (prime ^ power)) (divisible : prime ∣ index.val)
    (pair : ℚ_[prime] × ℚ_[prime]) (member : pair.swap ∈ padicPivotRegion power index) :
    value (padicPlanePivotCoordinates pair.1 pair.2).block = value (padicLowerPrimitiveRepresentative power index) := by
  obtain ⟨compact, factors⟩ := padicPlanePivotCoordinates_second_region power positive index divisible pair member
  rw [factors, fixed]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
