module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PlanePivotCosets

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicPrimePowerLattice {prime : ℕ} [Fact prime.Prime] (power : ℕ) : Set ℚ_[prime] :=
  {value | ‖value‖ ≤ ‖(prime : ℚ_[prime]) ^ power‖}

theorem padicPrimePowerLattice_measurable {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]] (power : ℕ) :
    MeasurableSet (padicPrimePowerLattice (prime := prime) power) :=
  (isClosed_le continuous_norm continuous_const).measurableSet

theorem padicPrimePowerLattice_mem {prime : ℕ} [Fact prime.Prime] (power : ℕ) (value : ℚ_[prime]) :
    value ∈ padicPrimePowerLattice power ↔
      ∃ integral : ℤ_[prime], value = (prime : ℚ_[prime]) ^ power * (integral : ℚ_[prime]) := by
  have nonzero : (prime : ℚ_[prime]) ^ power ≠ 0 := (padicPrimePowerUnit power).ne_zero
  constructor
  · intro member
    have quotient : ‖value / (prime : ℚ_[prime]) ^ power‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr nonzero)).mpr member
    refine ⟨⟨value / (prime : ℚ_[prime]) ^ power, quotient⟩, ?_⟩
    exact (mul_div_cancel₀ value nonzero).symm
  · rintro ⟨integral, rfl⟩
    change ‖(prime : ℚ_[prime]) ^ power * (integral : ℚ_[prime])‖ ≤ _
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) integral.property

theorem padicPrimePowerLattice_integral {prime : ℕ} [Fact prime.Prime] {power : ℕ} {value : ℚ_[prime]}
    (member : value ∈ padicPrimePowerLattice power) : ‖value‖ ≤ 1 := by
  obtain ⟨integral, rfl⟩ := (padicPrimePowerLattice_mem power value).mp member
  exact (PadicInt.subring prime).mul_mem
    ((PadicInt.subring prime).pow_mem (prime : ℤ_[prime]).property power) integral.property

def padicResidueClass {prime : ℕ} [Fact prime.Prime] (power : ℕ) (index : Fin (prime ^ power)) : Set ℚ_[prime] :=
  (fun value => value - (index.val : ℚ_[prime])) ⁻¹' padicPrimePowerLattice power

theorem padicResidueClass_measurable {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]] (power : ℕ) (index : Fin (prime ^ power)) :
    MeasurableSet (padicResidueClass power index) :=
  (padicPrimePowerLattice_measurable power).preimage (continuous_id.sub continuous_const).measurable

theorem padicResidueClass_mem {prime : ℕ} [Fact prime.Prime] (power : ℕ)
    (index : Fin (prime ^ power)) (value : ℚ_[prime]) :
    value ∈ padicResidueClass power index ↔
      ∃ integral : ℤ_[prime], (integral : ℚ_[prime]) = value ∧ padicPivotResidue power integral = index := by
  constructor
  · intro member
    obtain ⟨shift, difference⟩ := (padicPrimePowerLattice_mem power (value - (index.val : ℚ_[prime]))).mp member
    let integral : ℤ_[prime] := (index.val : ℤ_[prime]) + (prime : ℤ_[prime]) ^ power * shift
    refine ⟨integral, ?_, ?_⟩
    · change (index.val : ℚ_[prime]) + (prime : ℚ_[prime]) ^ power * (shift : ℚ_[prime]) = value
      exact (sub_eq_iff_eq_add.mp difference |>.trans (add_comm _ _)).symm
    · apply (padicPivotResidue_unique power integral index _).symm
      exact ⟨shift, by dsimp only [integral]; ring⟩
  · rintro ⟨integral, rfl, index_eq⟩
    obtain ⟨shift, decomposition⟩ := padicPivotResidue_decomposition power integral
    rw [index_eq] at decomposition
    apply (padicPrimePowerLattice_mem power _).mpr
    refine ⟨shift, ?_⟩
    have equality := congrArg (fun x : ℤ_[prime] => (x : ℚ_[prime])) decomposition
    change (integral : ℚ_[prime]) = (index.val : ℚ_[prime]) +
      (prime : ℚ_[prime]) ^ power * (shift : ℚ_[prime]) at equality
    rw [equality]
    ring

theorem padicResidueClass_disjoint {prime : ℕ} [Fact prime.Prime] (power : ℕ) :
    Pairwise (fun first second : Fin (prime ^ power) =>
      Disjoint (padicResidueClass power first) (padicResidueClass power second)) := by
  intro first second distinct
  apply Set.disjoint_left.mpr
  intro value first_mem second_mem
  obtain ⟨first_integral, first_eq, first_residue⟩ := (padicResidueClass_mem power first value).mp first_mem
  obtain ⟨second_integral, second_eq, second_residue⟩ := (padicResidueClass_mem power second value).mp second_mem
  have same : first_integral = second_integral := Subtype.ext (first_eq.trans second_eq.symm)
  exact distinct (first_residue.symm.trans ((congrArg (padicPivotResidue power) same).trans second_residue))

theorem padicResidueClass_union {prime : ℕ} [Fact prime.Prime] (power : ℕ) :
    (⋃ index : Fin (prime ^ power), padicResidueClass power index) = {value : ℚ_[prime] | ‖value‖ ≤ 1} := by
  ext value
  constructor
  · intro member
    obtain ⟨index, member⟩ := Set.mem_iUnion.mp member
    obtain ⟨integral, rfl, _⟩ := (padicResidueClass_mem power index value).mp member
    exact integral.property
  · intro integral
    apply Set.mem_iUnion.mpr
    refine ⟨padicPivotResidue power ⟨value, integral⟩, ?_⟩
    exact (padicResidueClass_mem power _ value).mpr ⟨⟨value, integral⟩, rfl, rfl⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
