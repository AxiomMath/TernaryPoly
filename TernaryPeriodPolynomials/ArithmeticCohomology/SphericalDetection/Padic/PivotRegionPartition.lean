module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PivotRegionMeasure

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicPivotShell_ne_zero {prime : ℕ} [Fact prime.Prime] {power : ℕ} {value : ℚ_[prime]}
    (member : value ∈ padicPivotShell power) : value ≠ 0 := by
  have positive : 0 < (prime : ℝ) ^ power := pow_pos (by exact_mod_cast (Nat.Prime.pos Fact.out)) _
  apply norm_pos_iff.mp
  change ‖value‖ = (prime : ℝ) ^ power at member
  rwa [member]

theorem padicPivotShell_inverse_norm {prime : ℕ} [Fact prime.Prime] {power : ℕ} {value : ℚ_[prime]}
    (member : value ∈ padicPivotShell power) : ‖value⁻¹‖ = ‖(prime : ℚ_[prime]) ^ power‖ := by
  change ‖value‖ = (prime : ℝ) ^ power at member
  rw [norm_inv, member, Padic.norm_p_pow, zpow_neg, zpow_natCast]

theorem padicPivotOffset_integral_iff {prime : ℕ} [Fact prime.Prime]
    (pivot : ℚ_[prime]ˣ) (other : ℚ_[prime]) :
    ‖-other * pivot.inv‖ ≤ 1 ↔ ‖other‖ ≤ ‖pivot.val‖ := by
  change ‖-other * (pivot⁻¹).val‖ ≤ 1 ↔ _
  rw [Units.val_inv_eq_inv_val, ← div_eq_mul_inv, norm_div, norm_neg,
    div_le_one (norm_pos_iff.mpr pivot.ne_zero)]

theorem padicPivotRegion_mem_iff_residue {prime : ℕ} [Fact prime.Prime]
    (power : ℕ) (pivot : ℚ_[prime]ˣ) (other : ℚ_[prime]) (index : Fin (prime ^ power))
    (member : pivot.val ∈ padicPivotShell power) :
    (pivot.val, other) ∈ padicPivotRegion power index ↔
      -other * pivot.inv ∈ padicResidueClass power index := by
  have equality := Set.ext_iff.mp
    (padicPivotFiber_translate power pivot index (padicPivotShell_inverse_norm member)) other
  change (-other * pivot.inv ∈ padicResidueClass power index) ↔
    ‖other + (index.val : ℚ_[prime]) * pivot.val‖ ≤ 1 at equality
  exact (and_iff_right member).trans equality.symm

theorem padicPivotRegion_disjoint {prime : ℕ} [Fact prime.Prime] (power : ℕ) :
    Pairwise (fun first second : Fin (prime ^ power) =>
      Disjoint (padicPivotRegion power first) (padicPivotRegion power second)) := by
  intro first second distinct
  apply Set.disjoint_left.mpr
  intro pair first_mem second_mem
  let pivot := Units.mk0 pair.1 (padicPivotShell_ne_zero first_mem.1)
  have first_residue := (padicPivotRegion_mem_iff_residue power pivot pair.2 first first_mem.1).mp first_mem
  have second_residue := (padicPivotRegion_mem_iff_residue power pivot pair.2 second first_mem.1).mp second_mem
  exact Set.disjoint_left.mp (padicResidueClass_disjoint power distinct) first_residue second_residue

theorem padicPivotRegion_union {prime : ℕ} [Fact prime.Prime] (power : ℕ) :
    (⋃ index : Fin (prime ^ power), padicPivotRegion power index) =
      {pair : ℚ_[prime] × ℚ_[prime] | pair.1 ∈ padicPivotShell power ∧ ‖pair.2‖ ≤ ‖pair.1‖} := by
  ext pair
  constructor
  · intro member
    obtain ⟨index, member⟩ := Set.mem_iUnion.mp member
    refine ⟨member.1, ?_⟩
    let pivot := Units.mk0 pair.1 (padicPivotShell_ne_zero member.1)
    have residue := (padicPivotRegion_mem_iff_residue power pivot pair.2 index member.1).mp member
    obtain ⟨integral, same, _⟩ := (padicResidueClass_mem power index _).mp residue
    have integral_norm : ‖-pair.2 * pivot.inv‖ ≤ 1 := same ▸ integral.property
    exact (padicPivotOffset_integral_iff pivot pair.2).mp integral_norm
  · intro member
    let pivot := Units.mk0 pair.1 (padicPivotShell_ne_zero member.1)
    let offset := padicPlanePivotOffset pivot pair.2 member.2
    apply Set.mem_iUnion.mpr
    refine ⟨padicPivotResidue power offset, ?_⟩
    apply (padicPivotRegion_mem_iff_residue power pivot pair.2 _ member.1).mpr
    exact (padicResidueClass_mem power _ _).mpr ⟨offset, rfl, rfl⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
