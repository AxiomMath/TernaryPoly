module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Padic.PrimitiveShellIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem padicNorm_large_exists_power {prime : ℕ} [Fact prime.Prime] (value : ℚ_[prime])
    (large : 1 < ‖value‖) : ∃ power : ℕ, ‖value‖ = (prime : ℝ) ^ (power + 1) := by
  have nonzero : value ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one large)
  have negative : value.valuation < 0 := by
    apply lt_of_not_ge
    intro nonnegative
    exact (not_le_of_gt large) ((Padic.norm_le_one_iff_val_nonneg value).mpr nonnegative)
  have cast : ((-value.valuation).toNat : ℤ) = -value.valuation := Int.toNat_of_nonneg (by omega)
  have positive : 0 < (-value.valuation).toNat := by omega
  obtain ⟨power, equality⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt positive)
  refine ⟨power, ?_⟩
  rw [Padic.norm_eq_zpow_neg_valuation nonzero, ← cast, zpow_natCast, equality]

def padicPlaneIntegrationRegion {prime : ℕ} [Fact prime.Prime] : ℕ → Set (ℚ_[prime] × ℚ_[prime])
  | 0 => {pair | ‖pair.1‖ ≤ 1 ∧ ‖pair.2‖ ≤ 1}
  | power + 1 => {pair | max ‖pair.1‖ ‖pair.2‖ = (prime : ℝ) ^ (power + 1)}

theorem padicPlaneIntegrationRegion_measurable {prime : ℕ} [Fact prime.Prime]
    [MeasurableSpace ℚ_[prime]] [BorelSpace ℚ_[prime]] (power : ℕ) :
    MeasurableSet (padicPlaneIntegrationRegion (prime := prime) power) := by
  cases power with
  | zero =>
      exact ((isClosed_le continuous_fst.norm continuous_const).inter
        (isClosed_le continuous_snd.norm continuous_const)).measurableSet
  | succ power =>
      exact (isClosed_eq (continuous_fst.norm.max continuous_snd.norm) continuous_const).measurableSet

theorem padicPlaneIntegrationRegion_zero_disjoint {prime : ℕ} [Fact prime.Prime] (power : ℕ) :
    Disjoint (padicPlaneIntegrationRegion (prime := prime) 0) (padicPlaneIntegrationRegion (power + 1)) := by
  apply Set.disjoint_left.mpr
  intro pair integral shell
  have maximum : max ‖pair.1‖ ‖pair.2‖ ≤ 1 := max_le integral.1 integral.2
  change max ‖pair.1‖ ‖pair.2‖ = (prime : ℝ) ^ (power + 1) at shell
  rw [shell] at maximum
  have large : (1 : ℝ) < (prime : ℝ) ^ (power + 1) := by
    exact_mod_cast Nat.one_lt_pow (Nat.succ_ne_zero power) (Nat.Prime.one_lt Fact.out)
  exact (not_le_of_gt large) maximum

theorem padicPlaneIntegrationRegion_disjoint {prime : ℕ} [Fact prime.Prime] :
    Pairwise (fun first second => Disjoint (padicPlaneIntegrationRegion (prime := prime) first)
      (padicPlaneIntegrationRegion second)) := by
  intro first second distinct
  cases first with
  | zero =>
      cases second with
      | zero => exact (distinct rfl).elim
      | succ second => exact padicPlaneIntegrationRegion_zero_disjoint second
  | succ first =>
      cases second with
      | zero => exact (padicPlaneIntegrationRegion_zero_disjoint first).symm
      | succ second =>
          apply Set.disjoint_left.mpr
          intro pair first_mem second_mem
          have equal_powers : (prime : ℝ) ^ (first + 1) = (prime : ℝ) ^ (second + 1) :=
            first_mem.symm.trans second_mem
          have positive : (0 : ℝ) < prime := by exact_mod_cast (Nat.Prime.pos Fact.out)
          have not_one : (prime : ℝ) ≠ 1 := ne_of_gt (by exact_mod_cast (Nat.Prime.one_lt Fact.out))
          exact distinct ((pow_right_inj₀ positive not_one).mp equal_powers)

theorem padicPlaneIntegrationRegion_union {prime : ℕ} [Fact prime.Prime] :
    (⋃ power, padicPlaneIntegrationRegion (prime := prime) power) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro pair
  by_cases integral : ‖pair.1‖ ≤ 1 ∧ ‖pair.2‖ ≤ 1
  · exact Set.mem_iUnion.mpr ⟨0, integral⟩
  · by_cases dominant : ‖pair.2‖ ≤ ‖pair.1‖
    · have large : 1 < ‖pair.1‖ := by
        by_contra! small
        exact integral ⟨small, dominant.trans small⟩
      obtain ⟨power, equality⟩ := padicNorm_large_exists_power pair.1 large
      refine Set.mem_iUnion.mpr ⟨power + 1, ?_⟩
      change max ‖pair.1‖ ‖pair.2‖ = _
      rw [max_eq_left dominant, equality]
    · have strict := lt_of_not_ge dominant
      have large : 1 < ‖pair.2‖ := by
        by_contra! small
        exact integral ⟨strict.le.trans small, small⟩
      obtain ⟨power, equality⟩ := padicNorm_large_exists_power pair.2 large
      refine Set.mem_iUnion.mpr ⟨power + 1, ?_⟩
      change max ‖pair.1‖ ‖pair.2‖ = _
      rw [max_eq_right strict.le, equality]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
