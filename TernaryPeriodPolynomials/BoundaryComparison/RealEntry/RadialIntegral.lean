module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.PolarIntegrability
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section


/-! The radial integral `∫ ρ in Ioi 0, ρ(√(1+ρ²))⁻¹^(n+3) dρ = 1/(n+1)`, computed via the
fundamental theorem of calculus on `(0,∞)` with antiderivative `(1+ρ²)^(1-(n+3)/2)/(2-(n+3))`.
Used for clause (iii) of `real_constant_term_entry` (Appendix C.5). -/


open MeasureTheory Set Filter Topology

namespace TernaryPeriodPolynomials.Argument

/-- Pointwise, the inverse `(n+3)`-power radial weight `(√(1+ρ²))⁻¹^(n+3)` (a natural-number
power) agrees with the real-power form `(1+ρ²)^(-(n+3)/2)`. -/
theorem sqrt_inv_pow_eq_rpow (n : ℕ) (ρ : ℝ) :
    (Real.sqrt (1 + ρ ^ 2))⁻¹ ^ (n + 3) = (1 + ρ ^ 2) ^ (-(((n : ℝ) + 3) / 2)) := by
  have hx : (0 : ℝ) ≤ 1 + ρ ^ 2 := by positivity
  rw [inv_pow, ← Real.rpow_natCast (Real.sqrt (1 + ρ ^ 2)) (n + 3),
    ← Real.rpow_div_two_eq_sqrt _ hx, ← Real.rpow_neg hx]
  congr 1
  push_cast
  ring

/-- `ρ(1+ρ²)^{-k/2} ≤ ρ(√(1+ρ²))⁻¹³` for `ρ ≥ 0`, where `k = n+3 ≥ 3`: since `1+ρ² ≥ 1` and the
exponent `-k/2 ≤ -3/2`, raising a number `≥ 1` to a more negative power only shrinks it. -/
theorem rpow_le_sqrt_inv_cube (n : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ρ * (1 + ρ ^ 2) ^ (-(((n : ℝ) + 3) / 2)) ≤ ρ * (Real.sqrt (1 + ρ ^ 2))⁻¹ ^ 3 := by
  have hcube : (Real.sqrt (1 + ρ ^ 2))⁻¹ ^ 3 = (1 + ρ ^ 2) ^ (-((3 : ℝ) / 2)) := by
    have hx : (0 : ℝ) ≤ 1 + ρ ^ 2 := by positivity
    rw [inv_pow, ← Real.rpow_natCast (Real.sqrt (1 + ρ ^ 2)) 3,
      ← Real.rpow_div_two_eq_sqrt _ hx, ← Real.rpow_neg hx]
    norm_num
  rw [hcube]
  apply mul_le_mul_of_nonneg_left _ hρ
  apply Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ρ])
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- The scaled radial weight `ρ(1+ρ²)^{-(n+3)/2}` is integrable on `(0,∞)`, by comparison with
`radial_dominant_integrableOn` via `rpow_le_sqrt_inv_cube` and `radial_scaled_dominant_bound`. -/
theorem radial_rpow_integrableOn (n : ℕ) :
    IntegrableOn (fun ρ : ℝ => ρ * (1 + ρ ^ 2) ^ (-(((n : ℝ) + 3) / 2))) (Set.Ioi (0 : ℝ)) := by
  refine Integrable.mono' radial_dominant_integrableOn ?_ ?_
  · have hcont : Continuous (fun ρ : ℝ => (1 + ρ ^ 2) ^ (-(((n : ℝ) + 3) / 2))) :=
      (continuous_const.add (continuous_id.pow 2)).rpow_const
        (fun ρ => Or.inl (show (1 : ℝ) + ρ ^ 2 ≠ 0 by positivity))
    exact (continuous_id.mul hcont).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
      with ρ hρ
    have hρ0 : 0 ≤ ρ := le_of_lt hρ
    have hρ' : ‖ρ‖ = ρ := by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]
    have hnn : (0 : ℝ) ≤ ρ * (1 + ρ ^ 2) ^ (-(((n : ℝ) + 3) / 2)) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, hρ']
    have h1 := rpow_le_sqrt_inv_cube n ρ hρ0
    have h2 := radial_scaled_dominant_bound ρ hρ0
    linarith

/-- The radial integral `∫ ρ in Ioi 0, ρ(√(1+ρ²))⁻¹^(n+3) dρ = 1/(n+1)`, via the fundamental
theorem of calculus with antiderivative `F ρ = (1+ρ²)^(1-(n+3)/2)/(2-(n+3))`. -/
theorem radial_integral (n : ℕ) :
    (∫ ρ in Set.Ioi (0 : ℝ), ρ * (Real.sqrt (1 + ρ ^ 2))⁻¹ ^ (n + 3)) = 1 / ((n : ℝ) + 1) := by
  have hrw : ∀ ρ : ℝ, ρ * (Real.sqrt (1 + ρ ^ 2))⁻¹ ^ (n + 3) =
      ρ * (1 + ρ ^ 2) ^ (-(((n : ℝ) + 3) / 2)) := fun ρ => by rw [sqrt_inv_pow_eq_rpow]
  simp_rw [hrw]
  set k : ℝ := (n : ℝ) + 3 with hk_def
  set p : ℝ := 1 - k / 2 with hp_def
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp_neg : p < 0 := by rw [hp_def, hk_def]; linarith
  have h2p : (2 : ℝ) - k ≠ 0 := by rw [hk_def]; intro h; nlinarith
  have hp1 : p - 1 = -(k / 2) := by rw [hp_def]; ring
  have h2pk : (2 : ℝ) * p = 2 - k := by rw [hp_def]; ring
  have hderiv : ∀ ρ ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun x : ℝ => (1 + x ^ 2) ^ p / (2 - k)) (ρ * (1 + ρ ^ 2) ^ (-(k / 2))) ρ := by
    intro ρ _
    have hbase : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * ρ) ρ := by
      simpa using (hasDerivAt_pow 2 ρ).const_add (1 : ℝ)
    have hpos : (0 : ℝ) < 1 + ρ ^ 2 := by positivity
    have hpow := hbase.rpow_const (p := p) (Or.inl hpos.ne')
    have hdiv := hpow.div_const (2 - k)
    have heq : (2 * ρ * p * (1 + ρ ^ 2) ^ (p - 1)) / (2 - k) = ρ * (1 + ρ ^ 2) ^ (-(k / 2)) := by
      rw [hp1, div_eq_iff h2p, ← h2pk]; ring
    rwa [heq] at hdiv
  have hint : IntegrableOn (fun ρ : ℝ => ρ * (1 + ρ ^ 2) ^ (-(k / 2))) (Set.Ioi (0 : ℝ)) := by
    rw [hk_def]; exact radial_rpow_integrableOn n
  have htendsto : Tendsto (fun x : ℝ => (1 + x ^ 2) ^ p / (2 - k)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun ρ : ℝ => 1 + ρ ^ 2) atTop atTop :=
      Filter.tendsto_atTop_mono
        (fun ρ => show ρ ≤ 1 + ρ ^ 2 by nlinarith [sq_nonneg (ρ - 1)]) tendsto_id
    have hy : (0 : ℝ) < -p := by linarith
    have h2 : Tendsto (fun ρ : ℝ => (1 + ρ ^ 2) ^ p) atTop (𝓝 0) := by
      have hpy : (fun ρ : ℝ => (1 + ρ ^ 2) ^ p) =
          (fun x : ℝ => x ^ (-(-p))) ∘ (fun ρ : ℝ => 1 + ρ ^ 2) := by
        funext ρ
        simp [neg_neg]
      rw [hpy]
      exact (tendsto_rpow_neg_atTop hy).comp h1
    simpa using h2.div_const (2 - k)
  have hres := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htendsto
  rw [hres]
  have h0 : ((1 : ℝ) + (0 : ℝ) ^ 2) ^ p = 1 := by norm_num
  rw [h0, hk_def]
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hd : (2 : ℝ) - ((n : ℝ) + 3) ≠ 0 := fun h => hn1 (by linarith)
  field_simp
  ring

end TernaryPeriodPolynomials.Argument
