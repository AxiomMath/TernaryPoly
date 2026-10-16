module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PivotRegionPartition

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicPivotResidue_divisible_iff {prime : ℕ} [Fact prime.Prime] (power : ℕ)
    (positive : 0 < power) (value : ℤ_[prime]) :
    prime ∣ (padicPivotResidue power value).val ↔ (prime : ℤ_[prime]) ∣ value := by
  constructor
  · intro divisible
    obtain ⟨shift, decomposition⟩ := padicPivotResidue_decomposition power value
    rw [decomposition]
    apply dvd_add
    · obtain ⟨multiple, equality⟩ := divisible
      exact ⟨(multiple : ℤ_[prime]), by exact_mod_cast equality⟩
    · exact dvd_mul_of_dvd_left (dvd_pow_self _ (ne_of_gt positive)) shift
  · exact padicPivotResidue_divisible power value positive

theorem padicPivotOffset_strict_iff {prime : ℕ} [Fact prime.Prime]
    (pivot : ℚ_[prime]ˣ) (other : ℚ_[prime]) :
    ‖-other * pivot.inv‖ < 1 ↔ ‖other‖ < ‖pivot.val‖ := by
  change ‖-other * (pivot⁻¹).val‖ < 1 ↔ _
  rw [Units.val_inv_eq_inv_val, ← div_eq_mul_inv, norm_div, norm_neg,
    div_lt_one (norm_pos_iff.mpr pivot.ne_zero)]

theorem padicPivotRegion_strict_iff {prime : ℕ} [Fact prime.Prime]
    (power : ℕ) (positive : 0 < power) (index : Fin (prime ^ power))
    (pair : ℚ_[prime] × ℚ_[prime]) (member : pair ∈ padicPivotRegion power index) :
    ‖pair.2‖ < ‖pair.1‖ ↔ prime ∣ index.val := by
  let pivot := Units.mk0 pair.1 (padicPivotShell_ne_zero member.1)
  have residue := (padicPivotRegion_mem_iff_residue power pivot pair.2 index member.1).mp member
  obtain ⟨integral, same, residue_eq⟩ := (padicResidueClass_mem power index _).mp residue
  rw [← residue_eq, padicPivotResidue_divisible_iff power positive, ← PadicInt.norm_lt_one_iff_dvd]
  change ‖pair.2‖ < ‖pivot.val‖ ↔ ‖(integral : ℚ_[prime])‖ < 1
  rw [same, padicPivotOffset_strict_iff]

theorem padicStrictPivotRegion_union {prime : ℕ} [Fact prime.Prime] (power : ℕ) (positive : 0 < power) :
    (⋃ index : {index : Fin (prime ^ power) // prime ∣ index.val}, padicPivotRegion power index.val) =
      {pair : ℚ_[prime] × ℚ_[prime] | pair.1 ∈ padicPivotShell power ∧ ‖pair.2‖ < ‖pair.1‖} := by
  ext pair
  constructor
  · intro member
    obtain ⟨index, member⟩ := Set.mem_iUnion.mp member
    exact ⟨member.1, (padicPivotRegion_strict_iff power positive index.val pair member).mpr index.property⟩
  · intro member
    have weak : pair ∈ ⋃ index : Fin (prime ^ power), padicPivotRegion power index := by
      rw [padicPivotRegion_union]
      exact ⟨member.1, member.2.le⟩
    obtain ⟨index, index_mem⟩ := Set.mem_iUnion.mp weak
    exact Set.mem_iUnion.mpr ⟨⟨index, (padicPivotRegion_strict_iff power positive index pair index_mem).mp member.2⟩,
      index_mem⟩

theorem padicPivotRegions_opposite_disjoint {prime : ℕ} [Fact prime.Prime]
    (power : ℕ) (positive : 0 < power) (first second : Fin (prime ^ power)) (divisible : prime ∣ second.val) :
    Disjoint (padicPivotRegion power first) (Prod.swap ⁻¹' padicPivotRegion power second) := by
  apply Set.disjoint_left.mpr
  intro pair first_mem second_mem
  have first_weak : ‖pair.2‖ ≤ ‖pair.1‖ := by
    have union_mem : pair ∈ ⋃ index : Fin (prime ^ power), padicPivotRegion power index :=
      Set.mem_iUnion.mpr ⟨first, first_mem⟩
    rw [padicPivotRegion_union] at union_mem
    exact union_mem.2
  have second_strict := (padicPivotRegion_strict_iff power positive second pair.swap second_mem).mpr divisible
  exact (not_lt_of_ge first_weak) second_strict

end TernaryPeriodPolynomials.SphericalDetection.Helpers
