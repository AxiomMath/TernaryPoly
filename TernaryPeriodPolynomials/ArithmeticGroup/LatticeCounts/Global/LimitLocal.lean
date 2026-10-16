module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.Haar
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.Shell.LitSet
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PadicMeasures

@[expose] public section


/-!
# Local weight integral for the global finite integral (Claude Sonnet 5.5)

The weight `(max 1 (max ‖s‖ ‖t‖))^(-b)` on `ℚ_p²` has integral at most `1/(1 - p^(2-b))` for `b > 3`.
-/

open MeasureTheory
open scoped ENNReal
open TernaryPeriodPolynomials.Argument.LatticeCounts.Padic

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitLocal

variable (p : ℕ) [Fact p.Prime]

/-- The local weight `(max 1 (max ‖s‖ ‖t‖))^(-b)`. -/
def phiR (b : ℝ) (z : ℚ_[p] × ℚ_[p]) : ℝ := (max 1 (max ‖z.1‖ ‖z.2‖)) ^ (-b)

theorem phiR_nonneg (b : ℝ) (z : ℚ_[p] × ℚ_[p]) : 0 ≤ phiR p b z :=
  Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _

theorem phiR_measurable (b : ℝ) : Measurable (phiR p b) := by
  unfold phiR
  exact (Measurable.pow_const (measurable_const.max ((measurable_fst.norm).max (measurable_snd.norm))) _)

/-- Every point of `ℚ_p²` is in `ℤ_p²` or in a shell `r ≥ 1`. -/
theorem exists_level (z : ℚ_[p] × ℚ_[p]) : ∃ r : ℕ, (r = 0 ∧ z ∈ Zp2 p) ∨ (1 ≤ r ∧ z ∈ pairShell p r) := by
  by_cases h : max ‖z.1‖ ‖z.2‖ ≤ 1
  · exact ⟨0, Or.inl ⟨rfl, le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩⟩
  · push Not at h
    have hp : (1 : ℝ) < p := Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt
    have key : ∀ x : ℚ_[p], 1 < ‖x‖ → ∃ r : ℕ, 1 ≤ r ∧ ‖x‖ = (p : ℝ) ^ r := by
      intro x hx
      have hx0 : x ≠ 0 := by
        rintro rfl; rw [norm_zero] at hx; linarith
      rw [Padic.norm_eq_zpow_neg_valuation hx0] at hx ⊢
      have hpos : 0 < -x.valuation := by
        by_contra hneg
        push Not at hneg
        have := zpow_le_one_of_nonpos₀ hp.le hneg
        linarith
      refine ⟨(-x.valuation).toNat, by omega, ?_⟩
      rw [← zpow_natCast, Int.toNat_of_nonneg hpos.le]
    rcases le_total ‖z.1‖ ‖z.2‖ with hle | hle
    · rw [max_eq_right hle] at h
      obtain ⟨r, hr, hx⟩ := key _ h
      exact ⟨r, Or.inr ⟨hr, by show max ‖z.1‖ ‖z.2‖ = _; rw [max_eq_right hle]; exact hx⟩⟩
    · rw [max_eq_left hle] at h
      obtain ⟨r, hr, hx⟩ := key _ h
      exact ⟨r, Or.inr ⟨hr, by show max ‖z.1‖ ‖z.2‖ = _; rw [max_eq_left hle]; exact hx⟩⟩

/-- The level sets `ℤ_p²` (`r = 0`) and the shells `r ≥ 1`. -/
def lev (r : ℕ) : Set (ℚ_[p] × ℚ_[p]) := if r = 0 then Zp2 p else pairShell p r

theorem lev_measurable (r : ℕ) : MeasurableSet (lev p r) := by
  unfold lev
  split_ifs with h
  · exact (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).measurableSet.inter
      (isClosed_le (continuous_norm.comp continuous_snd) continuous_const).measurableSet
  · exact (ShellLitSet.isOpen_pairShell (Nat.one_le_iff_ne_zero.2 h)).measurableSet

theorem iUnion_lev : ⋃ r, lev p r = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨r, h⟩ := exists_level p z
  rcases h with ⟨rfl, hz⟩ | ⟨hr, hz⟩
  · exact Set.mem_iUnion.2 ⟨0, by simp [lev, hz]⟩
  · exact Set.mem_iUnion.2 ⟨r, by simp [lev, hz, Nat.one_le_iff_ne_zero.1 hr]⟩

theorem disjoint_lev : Pairwise (Function.onFun Disjoint (lev p)) := by
  have hp : (1 : ℝ) < p := Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt
  intro r r' hne
  rw [Function.onFun, Set.disjoint_left]
  intro z hz hz'
  unfold lev at hz hz'
  by_cases h0 : r = 0
  · by_cases h0' : r' = 0
    · exact hne (h0.trans h0'.symm)
    · rw [ite_eq_left h0] at hz; rw [ite_eq_right h0'] at hz'
      have h1 : max ‖z.1‖ ‖z.2‖ ≤ 1 := max_le hz.1 hz.2
      have h2 : max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ r' := hz'
      have : (1 : ℝ) < (p : ℝ) ^ r' := one_lt_pow₀ hp h0'
      linarith
  · rw [ite_eq_right h0] at hz
    by_cases h0' : r' = 0
    · rw [ite_eq_left h0'] at hz'
      have h1 : max ‖z.1‖ ‖z.2‖ ≤ 1 := max_le hz'.1 hz'.2
      have h2 : max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ r := hz
      have : (1 : ℝ) < (p : ℝ) ^ r := one_lt_pow₀ hp h0
      linarith
    · rw [ite_eq_right h0'] at hz'
      have h2 : (p : ℝ) ^ r = (p : ℝ) ^ r' := hz.symm.trans hz'
      exact hne (Nat.pow_right_injective (Fact.out : p.Prime).two_le (by exact_mod_cast h2))

theorem phiR_on_lev (b : ℝ) (r : ℕ) {z : ℚ_[p] × ℚ_[p]} (hz : z ∈ lev p r) :
    phiR p b z = ((p : ℝ) ^ (-b)) ^ r := by
  unfold lev at hz
  unfold phiR
  by_cases h0 : r = 0
  · rw [ite_eq_left h0] at hz
    rw [max_eq_left (max_le hz.1 hz.2)]
    simp [h0]
  · rw [ite_eq_right h0] at hz
    have h2 : max ‖z.1‖ ‖z.2‖ = (p : ℝ) ^ r := hz
    have hp : (1 : ℝ) < p := Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt
    have : (1 : ℝ) ≤ (p : ℝ) ^ r := one_le_pow₀ hp.le
    rw [h2, max_eq_right this]
    exact (Real.rpow_pow_comm (by linarith) (-b) r).symm

/-- **The local integral of the weight is at most `1/(1 - p^{2-b})`** (`b > 3`, normalized Haar measure on `ℚ_p`). -/
theorem lintegral_phiR_le (b : ℝ) (hb : 3 < b) {μ₁ : Measure ℚ_[p]} [SigmaFinite μ₁] [μ₁.IsAddLeftInvariant]
    (h1 : μ₁ {x | ‖x‖ ≤ 1} = 1) :
    ∫⁻ z, ENNReal.ofReal (phiR p b z) ∂(μ₁.prod μ₁) ≤ ENNReal.ofReal ((1 - (p : ℝ) ^ (2 - b))⁻¹) := by
  have hp : (1 : ℝ) < p := Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  set q : ℝ := (p : ℝ) ^ (2 - b) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hp0.le _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hxq : ∀ r : ℕ, ((p : ℝ) ^ (-b)) ^ r * ((p : ℝ) ^ 2) ^ r = q ^ r := by
    intro r
    rw [← mul_pow, hq, Real.rpow_sub hp0, div_eq_mul_inv, ← Real.rpow_neg hp0.le]
    congr 1
    rw [show ((p : ℝ) ^ 2) = (p : ℝ) ^ (2 : ℝ) by norm_cast]
    ring_nf
  have hμ : ∀ r : ℕ, (μ₁.prod μ₁) (lev p r) ≤ ENNReal.ofReal (((p : ℝ) ^ 2) ^ r) := by
    intro r
    by_cases h0 : r = 0
    · subst h0
      simp only [lev, ite_true, pow_zero, ENNReal.ofReal_one]
      exact (prod_measure_Zp2 p h1).le
    · simp only [lev, ite_eq_right h0]
      rw [shell_measure_prod_rat p h1 (Nat.one_le_iff_ne_zero.2 h0)]
      apply ENNReal.ofReal_le_ofReal
      rw [← pow_mul]
      have : (0 : ℝ) ≤ ((p : ℝ) ^ 2)⁻¹ := by positivity
      nlinarith [pow_nonneg hp0.le (2 * r)]
  have hterm : ∀ r : ℕ, ∫⁻ z in lev p r, ENNReal.ofReal (phiR p b z) ∂(μ₁.prod μ₁) ≤ ENNReal.ofReal (q ^ r) := by
    intro r
    rw [setLIntegral_congr_fun (lev_measurable p r) (fun z hz => by rw [phiR_on_lev p b r hz]), setLIntegral_const]
    calc ENNReal.ofReal (((p : ℝ) ^ (-b)) ^ r) * (μ₁.prod μ₁) (lev p r)
        ≤ ENNReal.ofReal (((p : ℝ) ^ (-b)) ^ r) * ENNReal.ofReal (((p : ℝ) ^ 2) ^ r) :=
          by gcongr; exact hμ r
      _ = ENNReal.ofReal (q ^ r) := by
          rw [← ENNReal.ofReal_mul (pow_nonneg (Real.rpow_nonneg hp0.le _) _), hxq]
  calc ∫⁻ z, ENNReal.ofReal (phiR p b z) ∂(μ₁.prod μ₁)
      = ∫⁻ z in ⋃ r, lev p r, ENNReal.ofReal (phiR p b z) ∂(μ₁.prod μ₁) := by
        rw [iUnion_lev, Measure.restrict_univ]
    _ = ∑' r, ∫⁻ z in lev p r, ENNReal.ofReal (phiR p b z) ∂(μ₁.prod μ₁) :=
        lintegral_iUnion (lev_measurable p) (disjoint_lev p) _
    _ ≤ ∑' r : ℕ, ENNReal.ofReal (q ^ r) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' r : ℕ, q ^ r) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun r => pow_nonneg hq0 r) (summable_geometric_of_lt_one hq0 hq1)).symm
    _ = ENNReal.ofReal ((1 - q)⁻¹) := by rw [tsum_geometric_of_lt_one hq0 hq1]

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitLocal
