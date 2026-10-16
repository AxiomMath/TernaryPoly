module

public import Mathlib
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.Basic
public import Batteries.Data.MLList.Basic
public import Batteries.Lean.LawfulMonadLift
public import Batteries.Lean.Meta.Simp
public import Batteries.Recycling.MonadSatisfying.Lean
public import Batteries.Util.Pickle

@[expose] public section


/-!
# Taylor coefficients of holomorphic functions on the unit disc

For a holomorphic `H : ℂ → E` on the open unit disc, `taylorCoeff H n` (the Cauchy integral
over the circle of radius `1/2`) is the `n`-th Taylor coefficient at `0`.  This file proves that
the Taylor series converges to `H` on the whole disc (`hasSum_taylorCoeff`), that the coefficients
are determined by any such expansion (`taylorCoeff_eq_of_hasSum`), that a series with
polynomially bounded coefficients defines a holomorphic function with exactly these coefficients
(`taylorCoeff_tsum_of_bound`), and the elementary calculus of the coefficients: rotation,
constants, linearity and the Cauchy estimate.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped Real NNReal ENNReal

namespace TernaryPeriodPolynomials.Regularity

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The formal power series `∑ c n • z ^ n`, as a formal multilinear series. -/
def coeffSeries (c : ℕ → E) : FormalMultilinearSeries ℂ ℂ E := fun n =>
  ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (c n)

omit [CompleteSpace E] in
theorem coeffSeries_apply (c : ℕ → E) (n : ℕ) (z : ℂ) :
    coeffSeries c n (fun _ => z) = z ^ n • c n := by
  simp [coeffSeries, ContinuousMultilinearMap.mkPiRing_apply]

omit [CompleteSpace E] in
theorem norm_coeffSeries (c : ℕ → E) (n : ℕ) : ‖coeffSeries c n‖ = ‖c n‖ :=
  ContinuousMultilinearMap.norm_mkPiRing _

omit [CompleteSpace E] in
theorem series_apply_pow (p : FormalMultilinearSeries ℂ ℂ E) (n : ℕ) (z : ℂ) :
    p n (fun _ => z) = z ^ n • p n (fun _ => 1) :=
  p.apply_eq_pow_smul_coeff

theorem hasFPowerSeriesOnBall_cauchy {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    {r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    HasFPowerSeriesOnBall H (cauchyPowerSeries H 0 r) 0 (r.toNNReal : ℝ≥0∞) := by
  have hsub : Metric.closedBall (0 : ℂ) ((r.toNNReal : ℝ≥0) : ℝ) ⊆ Metric.ball 0 1 :=
    Metric.closedBall_subset_ball (by rw [Real.coe_toNNReal r hr0.le]; exact hr)
  have h := (hH.mono hsub).hasFPowerSeriesOnBall (Real.toNNReal_pos.2 hr0)
  rwa [Real.coe_toNNReal r hr0.le] at h

theorem cauchyPowerSeries_eq_half {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    {r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    cauchyPowerSeries H 0 r = cauchyPowerSeries H 0 (1 / 2) :=
  (hasFPowerSeriesOnBall_cauchy hH hr0 hr).hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesOnBall_cauchy hH (by norm_num) (by norm_num)).hasFPowerSeriesAt

/-- The Taylor series of a function holomorphic on the unit disc converges to it on the disc. -/
theorem hasSum_taylorCoeff {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1)) {ζ : ℂ}
    (hζ : ‖ζ‖ < 1) : HasSum (fun n => ζ ^ n • taylorCoeff H n) (H ζ) := by
  obtain ⟨r, hr1, hr2⟩ := exists_between hζ
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg ζ) hr1
  have hmem : ζ ∈ Metric.eball (0 : ℂ) (r.toNNReal : ℝ≥0∞) := by
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right, Real.coe_toNNReal r hr0.le]
    exact hr1
  have hs := (hasFPowerSeriesOnBall_cauchy hH hr0 hr2).hasSum hmem
  rw [zero_add] at hs
  have hfun : ∀ n, (cauchyPowerSeries H 0 r n fun _ => ζ) = ζ ^ n • taylorCoeff H n := fun n => by
    rw [series_apply_pow (cauchyPowerSeries H 0 r) n ζ, taylorCoeff,
      cauchyPowerSeries_eq_half hH hr0 hr2]
  simpa only [hfun] using hs

/-- The Taylor coefficients are determined by any power series expansion of `H` near `0`. -/
theorem taylorCoeff_eq_of_hasSum {H : ℂ → E} {c : ℕ → E} {r : ℝ}
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1)) (hr : 0 < r)
    (hc : ∀ ζ : ℂ, ‖ζ‖ < r → HasSum (fun n => ζ ^ n • c n) (H ζ)) (n : ℕ) :
    taylorCoeff H n = c n := by
  have hρ0 : 0 < r / 2 := by positivity
  have hρr : r / 2 < r := by linarith
  have hnorm : ‖((r / 2 : ℝ) : ℂ)‖ < r := by
    rw [Complex.norm_real, Real.norm_of_nonneg hρ0.le]
    exact hρr
  have hs := (hc _ hnorm).summable.tendsto_atTop_zero
  have h2 : Tendsto (fun n : ℕ => ‖c n‖ * (r / 2) ^ n) atTop (𝓝 0) := by
    have h3 := hs.norm
    simp only [norm_zero, norm_smul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hρ0.le] at h3
    exact h3.congr fun n => mul_comm _ _
  have hrad : ((r / 2).toNNReal : ℝ≥0∞) ≤ (coeffSeries c).radius := by
    refine (coeffSeries c).le_radius_of_tendsto (l := 0) ?_
    simp only [norm_coeffSeries, Real.coe_toNNReal (r / 2) hρ0.le]
    exact h2
  have hb : HasFPowerSeriesOnBall H (coeffSeries c) 0 ((r / 2).toNNReal : ℝ≥0∞) := by
    refine ⟨hrad, ENNReal.coe_pos.2 (Real.toNNReal_pos.2 hρ0), fun {y} hy => ?_⟩
    have hy' : ‖y‖ < r := by
      have h4 := hy
      simp only [Metric.eball_coe, Metric.mem_ball, dist_zero_right,
        Real.coe_toNNReal (r / 2) hρ0.le] at h4
      linarith
    have e : (fun m : ℕ => coeffSeries c m fun _ => y) = fun m => y ^ m • c m :=
      funext fun m => coeffSeries_apply c m y
    rw [e, zero_add]
    exact hc y hy'
  have huniq := hb.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesOnBall_cauchy hH (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num)).hasFPowerSeriesAt
  have h5 := congrArg (fun p : FormalMultilinearSeries ℂ ℂ E => p n (fun _ => (1 : ℂ))) huniq
  simp only [coeffSeries_apply, one_pow, one_smul] at h5
  rw [taylorCoeff]
  exact h5.symm

theorem norm_taylorCoeff_le_norm {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    {r : ℝ} (hr0 : 0 < r) (hr : r < 1) (n : ℕ) :
    ‖taylorCoeff H n‖ ≤ ‖cauchyPowerSeries H 0 r n‖ := by
  have h1 : taylorCoeff H n = cauchyPowerSeries H 0 r n (fun _ => 1) := by
    rw [taylorCoeff, cauchyPowerSeries_eq_half hH hr0 hr]
  rw [h1]
  calc ‖cauchyPowerSeries H 0 r n (fun _ => 1)‖
      ≤ ‖cauchyPowerSeries H 0 r n‖ * ∏ _i : Fin n, ‖(1 : ℂ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖cauchyPowerSeries H 0 r n‖ := by simp

theorem summable_norm_taylorCoeff {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) : Summable (fun n => ‖taylorCoeff H n‖ * r ^ n) := by
  obtain ⟨r', hrr', hr'1⟩ := exists_between hr
  have hr'0 : 0 < r' := lt_of_le_of_lt hr0 hrr'
  have hb := hasFPowerSeriesOnBall_cauchy hH hr'0 hr'1
  have hlt : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < (cauchyPowerSeries H 0 r').radius :=
    lt_of_lt_of_le (ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_toNNReal_iff hr'0).2 hrr')) hb.r_le
  have hsum := (cauchyPowerSeries H 0 r').summable_norm_mul_pow hlt
  rw [Real.coe_toNNReal r hr0] at hsum
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 n))
    (fun n => ?_) hsum
  exact mul_le_mul_of_nonneg_right (norm_taylorCoeff_le_norm hH hr'0 hr'1 n) (pow_nonneg hr0 n)

/-- **Cauchy estimate**: `‖taylorCoeff H n‖ ≤ 2 ^ n M` if `‖H‖ ≤ M` on the circle of radius
`1/2`. -/
theorem norm_taylorCoeff_le {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1)) {M : ℝ}
    (hM : ∀ ζ : ℂ, ‖ζ‖ = 1 / 2 → ‖H ζ‖ ≤ M) (n : ℕ) : ‖taylorCoeff H n‖ ≤ 2 ^ n * M := by
  have h1 : ‖taylorCoeff H n‖ ≤ ‖cauchyPowerSeries H 0 (1 / 2) n‖ :=
    norm_taylorCoeff_le_norm hH (by norm_num) (by norm_num) n
  have h2 : ∫ θ in (0 : ℝ)..2 * π, ‖H (circleMap 0 (1 / 2) θ)‖ ≤ M * (2 * π) := by
    have h3 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
      (C := M) (f := fun θ => ‖H (circleMap 0 (1 / 2) θ)‖) (fun θ _ => by
        simp only [norm_norm]
        refine hM _ ?_
        rw [norm_circleMap_zero, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)])
    calc ∫ θ in (0 : ℝ)..2 * π, ‖H (circleMap 0 (1 / 2) θ)‖
        ≤ ‖∫ θ in (0 : ℝ)..2 * π, ‖H (circleMap 0 (1 / 2) θ)‖‖ := Real.le_norm_self _
      _ ≤ M * |2 * π - 0| := h3
      _ = M * (2 * π) := by rw [sub_zero, abs_of_pos (by positivity)]
  calc ‖taylorCoeff H n‖ ≤ ‖cauchyPowerSeries H 0 (1 / 2) n‖ := h1
    _ ≤ ((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, ‖H (circleMap 0 (1 / 2) θ)‖) * |(1 / 2 : ℝ)|⁻¹ ^ n :=
        norm_cauchyPowerSeries_le H 0 (1 / 2) n
    _ ≤ ((2 * π)⁻¹ * (M * (2 * π))) * |(1 / 2 : ℝ)|⁻¹ ^ n := by gcongr
    _ = 2 ^ n * M := by
        have hpi : π ≠ 0 := Real.pi_ne_zero
        have h3 : (2 * π)⁻¹ * (M * (2 * π)) = M := by field_simp
        rw [h3, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), one_div, inv_inv, mul_comm]

theorem taylorCoeff_zero_eq {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1)) :
    taylorCoeff H 0 = H 0 := by
  have h := hasSum_taylorCoeff hH (ζ := 0) (by simp)
  have h2 := hasSum_single (f := fun m : ℕ => (0 : ℂ) ^ m • taylorCoeff H m) 0
    (fun m hm => by simp [hm])
  have h3 := h.unique h2
  simpa using h3.symm

theorem taylorCoeff_const (e : E) (n : ℕ) :
    taylorCoeff (fun _ : ℂ => e) n = if n = 0 then e else 0 := by
  refine taylorCoeff_eq_of_hasSum (c := fun n => if n = 0 then e else 0)
    (differentiableOn_const e) one_pos (fun ζ _ => ?_) n
  have h := hasSum_single (f := fun m : ℕ => ζ ^ m • (if m = 0 then e else 0)) 0
    (fun m hm => by simp [hm])
  simpa using h

theorem taylorCoeff_add {F G : ℂ → E} (hF : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hG : DifferentiableOn ℂ G (Metric.ball 0 1)) (n : ℕ) :
    taylorCoeff (fun ζ => F ζ + G ζ) n = taylorCoeff F n + taylorCoeff G n := by
  refine taylorCoeff_eq_of_hasSum (c := fun n => taylorCoeff F n + taylorCoeff G n)
    (hF.add hG) one_pos (fun ζ hζ => ?_) n
  have h := (hasSum_taylorCoeff hF hζ).add (hasSum_taylorCoeff hG hζ)
  show HasSum (fun m : ℕ => ζ ^ m • (taylorCoeff F m + taylorCoeff G m)) (F ζ + G ζ)
  simpa only [smul_add] using h

theorem taylorCoeff_smul {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1)) (a : ℂ)
    (n : ℕ) : taylorCoeff (fun ζ => a • H ζ) n = a • taylorCoeff H n := by
  refine taylorCoeff_eq_of_hasSum (c := fun n => a • taylorCoeff H n) (hH.const_smul a)
    one_pos (fun ζ hζ => ?_) n
  have h := (hasSum_taylorCoeff hH hζ).const_smul a
  have e : (fun m : ℕ => ζ ^ m • a • taylorCoeff H m) = fun m => a • ζ ^ m • taylorCoeff H m :=
    funext fun m => smul_comm _ _ _
  show HasSum (fun m : ℕ => ζ ^ m • a • taylorCoeff H m) (a • H ζ)
  rw [e]
  exact h

theorem taylorCoeff_comp_mul {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1)) {u : ℂ}
    (hu : ‖u‖ = 1) (a : ℂ) (n : ℕ) :
    taylorCoeff (fun ζ => a • H (u * ζ)) n = (a * u ^ n) • taylorCoeff H n := by
  have hmaps : ∀ ζ : ℂ, ‖ζ‖ < 1 → ‖u * ζ‖ < 1 := fun ζ hζ => by
    rw [norm_mul, hu, one_mul]
    exact hζ
  have hd : DifferentiableOn ℂ (fun ζ : ℂ => a • H (u * ζ)) (Metric.ball 0 1) := by
    refine DifferentiableOn.const_smul ?_ a
    exact hH.comp (by fun_prop : Differentiable ℂ fun ζ : ℂ => u * ζ).differentiableOn
      (fun ζ hζ => mem_ball_zero_iff.2 (hmaps ζ (mem_ball_zero_iff.1 hζ)))
  refine taylorCoeff_eq_of_hasSum (c := fun n => (a * u ^ n) • taylorCoeff H n) hd one_pos
    (fun ζ hζ => ?_) n
  have h := (hasSum_taylorCoeff hH (hmaps ζ hζ)).const_smul a
  have e : (fun m : ℕ => ζ ^ m • (a * u ^ m) • taylorCoeff H m) =
      fun m => a • (u * ζ) ^ m • taylorCoeff H m := by
    funext m
    rw [smul_smul, smul_smul, mul_pow]
    congr 1
    ring
  show HasSum (fun m : ℕ => ζ ^ m • (a * u ^ m) • taylorCoeff H m) (a • H (u * ζ))
  rw [e]
  exact h

omit [NormedSpace ℂ E] [CompleteSpace E] in
/-- A series with polynomially bounded coefficients converges absolutely inside the unit disc. -/
theorem summable_norm_of_bound {c : ℕ → E} {C : ℝ} {N : ℕ}
    (hc : ∀ n, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ N) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun n => ‖c n‖ * r ^ n) := by
  have hs : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ N * r ^ n) := by
    rcases hr0.eq_or_lt with h0 | hpos
    · subst h0
      refine summable_of_ne_finset_zero (s := {0}) fun b hb => ?_
      have hb' : b ≠ 0 := by simpa using hb
      simp [zero_pow hb']
    · have h1 : Summable (fun n : ℕ => (n : ℝ) ^ N * r ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one N (by rwa [Real.norm_of_nonneg hr0])
      have h2 : Summable (fun n : ℕ => r⁻¹ * (((n + 1 : ℕ) : ℝ) ^ N * r ^ (n + 1))) :=
        ((summable_nat_add_iff 1).2 h1).mul_left r⁻¹
      refine h2.congr fun n => ?_
      have hinv : r⁻¹ * r = 1 := inv_mul_cancel₀ hpos.ne'
      push_cast
      rw [pow_succ]
      calc r⁻¹ * (((n : ℝ) + 1) ^ N * (r ^ n * r)) = ((n : ℝ) + 1) ^ N * r ^ n * (r⁻¹ * r) := by
            ring
        _ = ((n : ℝ) + 1) ^ N * r ^ n := by rw [hinv, mul_one]
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0 n))
    (fun n => ?_) (hs.mul_left C)
  calc ‖c n‖ * r ^ n ≤ (C * ((n : ℝ) + 1) ^ N) * r ^ n :=
        mul_le_mul_of_nonneg_right (hc n) (pow_nonneg hr0 n)
    _ = C * (((n : ℝ) + 1) ^ N * r ^ n) := by ring

theorem differentiableOn_tsum_of_bound {c : ℕ → E} {C : ℝ} {N : ℕ}
    (hc : ∀ n, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ N) :
    DifferentiableOn ℂ (fun ζ : ℂ => ∑' n, ζ ^ n • c n) (Metric.ball 0 1) := by
  intro z hz
  obtain ⟨r, hzr, hr1⟩ := exists_between (mem_ball_zero_iff.1 hz)
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hzr.le
  have hF : ∀ n : ℕ, DifferentiableOn ℂ (fun ζ : ℂ => ζ ^ n • c n) (Metric.ball 0 r) :=
    fun n => (by fun_prop : Differentiable ℂ fun ζ : ℂ => ζ ^ n • c n).differentiableOn
  have hle : ∀ (n : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) r → ‖w ^ n • c n‖ ≤ ‖c n‖ * r ^ n := by
    intro n w hw
    have hw' : ‖w‖ ≤ r := (mem_ball_zero_iff.1 hw).le
    rw [norm_smul, norm_pow, mul_comm]
    gcongr
  have hd : DifferentiableOn ℂ (fun ζ : ℂ => ∑' n, ζ ^ n • c n) (Metric.ball 0 r) :=
    Complex.differentiableOn_tsum_of_summable_norm (summable_norm_of_bound hc hr0 hr1) hF
      Metric.isOpen_ball hle
  exact (hd.differentiableAt
    (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hzr))).differentiableWithinAt

theorem taylorCoeff_tsum_of_bound {c : ℕ → E} {C : ℝ} {N : ℕ}
    (hc : ∀ n, ‖c n‖ ≤ C * ((n : ℝ) + 1) ^ N) (n : ℕ) :
    taylorCoeff (fun ζ : ℂ => ∑' n, ζ ^ n • c n) n = c n := by
  refine taylorCoeff_eq_of_hasSum (c := c) (differentiableOn_tsum_of_bound hc) one_pos
    (fun ζ hζ => ?_) n
  have hs : Summable (fun n => ζ ^ n • c n) := by
    refine Summable.of_norm ?_
    refine (summable_norm_of_bound hc (norm_nonneg ζ) hζ).congr fun n => ?_
    rw [norm_smul, norm_pow, mul_comm]
  exact hs.hasSum

end Taylor

end TernaryPeriodPolynomials.Regularity

end
