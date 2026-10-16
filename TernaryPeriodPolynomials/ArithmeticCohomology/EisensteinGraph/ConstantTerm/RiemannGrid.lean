module

public import Mathlib

@[expose] public section


/-!
# Riemann sums on the unit square

For a continuous function `φ : ℝ × ℝ → ℂ`, the grid averages
`K⁻² ∑_{a,b<K} φ (a/K, b/K)` converge to the integral of `φ` over `[0,1]²`.
-/

namespace TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm

open MeasureTheory Set Filter

/-- Quantitative one-dimensional Riemann sum estimate on `[0,1]` for a continuous function
with a uniform modulus of continuity at scale `1 / K`. -/
theorem norm_riemannSum_sub_integral_le (f : ℝ → ℂ) (hf : Continuous f) (K : ℕ) (hK : 0 < K)
    (ε : ℝ)
    (h : ∀ y ∈ Icc (0 : ℝ) 1, ∀ y' ∈ Icc (0 : ℝ) 1, |y - y'| ≤ 1 / K → ‖f y - f y'‖ ≤ ε) :
    ‖(1 / (K : ℂ)) * ∑ b ∈ Finset.range K, f ((b : ℝ) / K) - ∫ y in (0 : ℝ)..1, f y‖ ≤ ε := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hKne : (K : ℝ) ≠ 0 := hKpos.ne'
  have hsplit : ∫ y in (0 : ℝ)..1, f y =
      ∑ b ∈ Finset.range K, ∫ y in ((b : ℝ) / K)..(((b + 1 : ℕ) : ℝ) / K), f y := by
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := f)
      (a := fun b : ℕ => (b : ℝ) / K) (n := K) (fun k _ => hf.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_div, div_self hKne] at this
    exact this.symm
  have hterm : ∀ b ∈ Finset.range K,
      ‖(1 / (K : ℂ)) * f ((b : ℝ) / K) - ∫ y in ((b : ℝ) / K)..(((b + 1 : ℕ) : ℝ) / K), f y‖
        ≤ ε / K := by
    intro b hb
    have hb' : b + 1 ≤ K := Finset.mem_range.mp hb
    have hb'' : ((b + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast hb'
    have hlen : ((b + 1 : ℕ) : ℝ) / K - (b : ℝ) / K = 1 / K := by
      push_cast; ring
    have hle : (b : ℝ) / K ≤ ((b + 1 : ℕ) : ℝ) / K := by
      rw [← sub_nonneg, hlen]; positivity
    have hconst : (1 / (K : ℂ)) * f ((b : ℝ) / K) =
        ∫ _y in ((b : ℝ) / K)..(((b + 1 : ℕ) : ℝ) / K), f ((b : ℝ) / K) := by
      rw [intervalIntegral.integral_const, hlen]
      simp [Complex.real_smul]
    have hdiff : (1 / (K : ℂ)) * f ((b : ℝ) / K) -
        ∫ y in ((b : ℝ) / K)..(((b + 1 : ℕ) : ℝ) / K), f y =
        ∫ y in ((b : ℝ) / K)..(((b + 1 : ℕ) : ℝ) / K), (f ((b : ℝ) / K) - f y) := by
      rw [hconst]
      exact (intervalIntegral.integral_sub intervalIntegrable_const
        (hf.intervalIntegrable _ _)).symm
    rw [hdiff]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (b : ℝ) / K)
      (b := ((b + 1 : ℕ) : ℝ) / K) (C := ε) (f := fun y => f ((b : ℝ) / K) - f y) ?_
    · rw [abs_of_nonneg (sub_nonneg.mpr hle), hlen] at this
      calc _ ≤ ε * (1 / K) := this
        _ = ε / K := by ring
    · intro y hy
      rw [uIoc_of_le hle] at hy
      have hb0 : (0 : ℝ) ≤ (b : ℝ) / K := by positivity
      have h1 : ((b + 1 : ℕ) : ℝ) / K ≤ 1 := by
        rw [div_le_one hKpos]; exact hb''
      refine h ((b : ℝ) / K) ⟨hb0, by linarith [hy.1, hy.2]⟩ y
        ⟨by linarith [hy.1], by linarith [hy.2]⟩ ?_
      exact abs_le.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩
  rw [hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ b ∈ Finset.range K, ‖(1 / (K : ℂ)) * f ((b : ℝ) / K) -
          ∫ y in ((b : ℝ) / K)..(((b + 1 : ℕ) : ℝ) / K), f y‖ := norm_sum_le _ _
    _ ≤ ∑ _b ∈ Finset.range K, ε / K := Finset.sum_le_sum hterm
    _ = ε := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- Riemann sums over the unit square converge to the integral over the square. -/
theorem tendsto_gridSum_integral (φ : ℝ × ℝ → ℂ) (hφ : Continuous φ) :
    Filter.Tendsto
      (fun K : ℕ => (1 / (K : ℂ) ^ 2) •
        ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, φ ((a : ℝ) / K, (b : ℝ) / K))
      Filter.atTop
      (nhds (∫ p in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, φ p)) := by
  have hcomp : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod isCompact_Icc
  have hφx : ∀ x : ℝ, Continuous fun y : ℝ => φ (x, y) := fun x => by fun_prop
  set F : ℝ → ℂ := fun x => ∫ y in (0 : ℝ)..1, φ (x, y) with hF
  have hFc : Continuous F :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x y => φ (x, y)) (μ := volume) hφ 0 1
  have hFub : ∫ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, φ p = ∫ x in (0 : ℝ)..1, F x := by
    have hint : Integrable φ
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hφ.continuousOn.integrableOn_compact hcomp
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint,
      intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc (fun x _ => ?_)
    simp only [hF]
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  rw [hFub, Metric.tendsto_atTop]
  intro ε hε
  have huc := hcomp.uniformContinuousOn_of_continuous hφ.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδφ⟩ := huc (ε / 4) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N + 1, fun K hK => ?_⟩
  have hKpos' : 0 < K := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hKpos'
  have hKne : (K : ℝ) ≠ 0 := hKpos.ne'
  have hKN : (N : ℝ) < K := by exact_mod_cast (by omega : N < K)
  have hKδ : 1 / (K : ℝ) < δ := by
    rw [div_lt_iff₀ hKpos]
    have := (div_lt_iff₀ hδ).mp (hN.trans hKN)
    linarith
  -- inner estimate
  have hG : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖(1 / (K : ℂ)) * ∑ b ∈ Finset.range K, φ (x, (b : ℝ) / K) - F x‖ ≤ ε / 4 := by
    intro x hx
    refine norm_riemannSum_sub_integral_le (fun y => φ (x, y)) (hφx x) K hKpos' _ ?_
    intro y hy y' hy' hyy
    have := hδφ (x, y) (Set.mk_mem_prod hx hy) (x, y') (Set.mk_mem_prod hx hy') (by
      rw [Prod.dist_eq]
      simp only [dist_self, Real.dist_eq]
      exact max_lt hδ (lt_of_le_of_lt hyy hKδ))
    rw [dist_eq_norm] at this
    exact this.le
  -- modulus of F
  have hFmod : ∀ x ∈ Icc (0 : ℝ) 1, ∀ x' ∈ Icc (0 : ℝ) 1, |x - x'| ≤ 1 / K →
      ‖F x - F x'‖ ≤ ε / 4 := by
    intro x hx x' hx' hxx
    have hdiff : F x - F x' = ∫ y in (0 : ℝ)..1, (φ (x, y) - φ (x', y)) := by
      simp only [hF]
      rw [intervalIntegral.integral_sub]
      · exact (hφx x).intervalIntegrable _ _
      · exact (hφx x').intervalIntegrable _ _
    rw [hdiff]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := ε / 4) (f := fun y => φ (x, y) - φ (x', y)) ?_
    · calc _ ≤ ε / 4 * |(1 : ℝ) - 0| := this
        _ = ε / 4 := by norm_num
    · intro y hy
      have := hδφ (x, y) (Set.mk_mem_prod hx ?_) (x', y) (Set.mk_mem_prod hx' ?_) (by
        rw [Prod.dist_eq]
        simp only [dist_self, Real.dist_eq]
        exact max_lt (lt_of_le_of_lt hxx hKδ) hδ)
      · rw [dist_eq_norm] at this
        exact this.le
      · rw [uIoc_of_le zero_le_one] at hy
        exact ⟨hy.1.le, hy.2⟩
      · rw [uIoc_of_le zero_le_one] at hy
        exact ⟨hy.1.le, hy.2⟩
  have hA : ‖(1 / (K : ℂ)) * ∑ a ∈ Finset.range K, F ((a : ℝ) / K) -
      ∫ x in (0 : ℝ)..1, F x‖ ≤ ε / 4 :=
    norm_riemannSum_sub_integral_le F hFc K hKpos' _ hFmod
  have hB : ‖(1 / (K : ℂ)) * ∑ a ∈ Finset.range K,
      ((1 / (K : ℂ)) * ∑ b ∈ Finset.range K, φ ((a : ℝ) / K, (b : ℝ) / K) - F ((a : ℝ) / K))‖
      ≤ ε / 4 := by
    have hterm : ∀ a ∈ Finset.range K,
        ‖(1 / (K : ℂ)) * ∑ b ∈ Finset.range K, φ ((a : ℝ) / K, (b : ℝ) / K) -
          F ((a : ℝ) / K)‖ ≤ ε / 4 := by
      intro a ha
      have ha' : a + 1 ≤ K := Finset.mem_range.mp ha
      have : (a : ℝ) / K ∈ Icc (0 : ℝ) 1 :=
        ⟨by positivity, by rw [div_le_one hKpos]; exact_mod_cast (by omega : a ≤ K)⟩
      exact hG _ this
    have hs : ‖∑ a ∈ Finset.range K, ((1 / (K : ℂ)) *
        ∑ b ∈ Finset.range K, φ ((a : ℝ) / K, (b : ℝ) / K) - F ((a : ℝ) / K))‖
        ≤ ∑ _a ∈ Finset.range K, ε / 4 :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    have hn : ‖(1 / (K : ℂ))‖ = 1 / (K : ℝ) := by simp
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hn]
    field_simp
  have hEq : (1 / (K : ℂ) ^ 2) •
      ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, φ ((a : ℝ) / K, (b : ℝ) / K) -
      ∫ x in (0 : ℝ)..1, F x =
      (1 / (K : ℂ)) * ∑ a ∈ Finset.range K,
        ((1 / (K : ℂ)) * ∑ b ∈ Finset.range K, φ ((a : ℝ) / K, (b : ℝ) / K) -
          F ((a : ℝ) / K)) +
      ((1 / (K : ℂ)) * ∑ a ∈ Finset.range K, F ((a : ℝ) / K) - ∫ x in (0 : ℝ)..1, F x) := by
    have h1 : (1 / (K : ℂ) ^ 2) *
        ∑ a ∈ Finset.range K, ∑ b ∈ Finset.range K, φ ((a : ℝ) / K, (b : ℝ) / K) =
        (1 / (K : ℂ)) * ∑ a ∈ Finset.range K,
          ((1 / (K : ℂ)) * ∑ b ∈ Finset.range K, φ ((a : ℝ) / K, (b : ℝ) / K)) := by
      simp only [← Finset.mul_sum]
      ring
    rw [smul_eq_mul, h1, Finset.sum_sub_distrib]
    ring
  rw [dist_eq_norm, hEq]
  exact lt_of_le_of_lt ((norm_add_le _ _).trans (add_le_add hB hA)) (by linarith)

end TernaryPeriodPolynomials.EisensteinGraph.ConstantTerm
