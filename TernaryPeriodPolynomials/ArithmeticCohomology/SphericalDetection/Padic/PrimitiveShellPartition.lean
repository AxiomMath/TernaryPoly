module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PivotRegionIntegrals

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def padicPrimitiveRegion {prime : ℕ} [Fact prime.Prime] (power : ℕ) :
    (Fin (prime ^ power) ⊕ {index : Fin (prime ^ power) // prime ∣ index.val}) → Set (ℚ_[prime] × ℚ_[prime])
  | .inl index => padicPivotRegion power index
  | .inr index => Prod.swap ⁻¹' padicPivotRegion power index.val

def padicPrimitiveRepresentative {prime : ℕ} [Fact prime.Prime] (power : ℕ) :
    (Fin (prime ^ power) ⊕ {index : Fin (prime ^ power) // prime ∣ index.val}) → GeneralLinearGroup (Fin 2) ℚ_[prime]
  | .inl index => padicUpperPrimitiveRepresentative power index
  | .inr index => padicLowerPrimitiveRepresentative power index.val

theorem padicPrimitiveRegion_disjoint {prime : ℕ} [Fact prime.Prime]
    (power : ℕ) (positive : 0 < power) :
    Pairwise (fun first second => Disjoint (padicPrimitiveRegion (prime := prime) power first)
      (padicPrimitiveRegion power second)) := by
  intro first second distinct
  cases first with
  | inl first =>
      cases second with
      | inl second => exact padicPivotRegion_disjoint power (fun same => distinct (congrArg Sum.inl same))
      | inr second => exact padicPivotRegions_opposite_disjoint power positive first second.val second.property
  | inr first =>
      cases second with
      | inl second => exact (padicPivotRegions_opposite_disjoint power positive second first.val first.property).symm
      | inr second =>
          exact (padicPivotRegion_disjoint power
            (fun same => distinct (congrArg Sum.inr (Subtype.ext same)))).preimage Prod.swap

theorem padicPrimitiveRegion_union {prime : ℕ} [Fact prime.Prime] (power : ℕ) (positive : 0 < power) :
    (⋃ index, padicPrimitiveRegion (prime := prime) power index) =
      {pair : ℚ_[prime] × ℚ_[prime] | max ‖pair.1‖ ‖pair.2‖ = (prime : ℝ) ^ power} := by
  ext pair
  constructor
  · intro member
    obtain ⟨index, member⟩ := Set.mem_iUnion.mp member
    cases index with
    | inl index =>
        have weak : pair ∈ ⋃ index : Fin (prime ^ power), padicPivotRegion power index :=
          Set.mem_iUnion.mpr ⟨index, member⟩
        rw [padicPivotRegion_union] at weak
        change max ‖pair.1‖ ‖pair.2‖ = _
        rw [max_eq_left weak.2]
        exact weak.1
    | inr index =>
        have strict : ‖pair.1‖ < ‖pair.2‖ :=
          (padicPivotRegion_strict_iff power positive index.val pair.swap member).mpr index.property
        change max ‖pair.1‖ ‖pair.2‖ = _
        rw [max_eq_right strict.le]
        exact member.1
  · intro member
    change max ‖pair.1‖ ‖pair.2‖ = (prime : ℝ) ^ power at member
    by_cases dominant : ‖pair.2‖ ≤ ‖pair.1‖
    · rw [max_eq_left dominant] at member
      have weak : pair ∈ ⋃ index : Fin (prime ^ power), padicPivotRegion power index := by
        rw [padicPivotRegion_union]
        exact ⟨member, dominant⟩
      obtain ⟨index, member⟩ := Set.mem_iUnion.mp weak
      exact Set.mem_iUnion.mpr ⟨Sum.inl index, member⟩
    · have strict := lt_of_not_ge dominant
      rw [max_eq_right strict.le] at member
      have stronger : pair.swap ∈ ⋃ index : {index : Fin (prime ^ power) // prime ∣ index.val},
          padicPivotRegion power index.val := by
        rw [padicStrictPivotRegion_union power positive]
        exact ⟨member, strict⟩
      obtain ⟨index, member⟩ := Set.mem_iUnion.mp stronger
      exact Set.mem_iUnion.mpr ⟨Sum.inr index, member⟩

theorem padicPrimitiveRegion_measurable {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]] (power : ℕ)
    (index : Fin (prime ^ power) ⊕ {index : Fin (prime ^ power) // prime ∣ index.val}) :
    MeasurableSet (padicPrimitiveRegion power index) := by
  cases index with
  | inl index => exact padicPivotRegion_measurable power index
  | inr index => exact (padicPivotRegion_measurable power index.val).preimage measurable_swap

end TernaryPeriodPolynomials.SphericalDetection.Helpers
