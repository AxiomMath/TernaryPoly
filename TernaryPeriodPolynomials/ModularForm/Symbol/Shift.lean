module

public import TernaryPeriodPolynomials.ModularForm.Endpoint.Shift
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section


noncomputable section
open Complex MvPolynomial MeasureTheory Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspSymbol
open BinaryCuspPeriod

/-- The actual horizontal contour integral from i*t to r+i*t. -/
def horizontalShiftIntegral {d : ℕ} (f : Forms d) (x y : ℂ) (r t : ℝ) : ℂ :=
  ∫ s : ℝ in 0..r, periodIntegrand f x y ((s : ℂ)+I*t)

/-- A uniform polynomial bound for the weight factor on any fixed bounded horizontal interval. -/
theorem horizontalShift_weight_bound (x y : ℂ) {s t : ℝ} (hs : |s| ≤ t)
    (ht : 1 ≤ t) : ‖((s : ℂ)+I*t)*y-x‖ ≤ t*(2*‖y‖+‖x‖) := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hz : ‖(s : ℂ)+I*t‖ ≤ 2*t := by
    calc
      ‖(s : ℂ)+I*t‖ ≤ ‖(s : ℂ)‖+‖I*(t : ℂ)‖ := norm_add_le _ _
      _ = |s|+t := by simp [abs_of_nonneg ht0]
      _ ≤ 2*t := by linarith
  calc
    ‖((s : ℂ)+I*t)*y-x‖ ≤ ‖((s : ℂ)+I*t)*y‖+‖x‖ := norm_sub_le _ _
    _ = ‖(s : ℂ)+I*t‖*‖y‖+‖x‖ := by rw [norm_mul]
    _ ≤ (2*t)*‖y‖+t*‖x‖ := by nlinarith [norm_nonneg x, norm_nonneg y]
    _ = t*(2*‖y‖+‖x‖) := by ring

/-- The actual horizontal integral vanishes at infinity by uniform cusp exponential decay. -/
theorem horizontalShiftIntegral_tendsto_zero {d : ℕ} (f : Forms d) (x y : ℂ) (r : ℝ) :
    Tendsto (horizontalShiftIntegral f x y r) atTop (𝓝 0) := by
  obtain ⟨c, hc, C, hC, T, hbound⟩ := cusp_uniform_horizontal_decay f
  have hlim : Tendsto (fun t : ℝ => (C*(2*‖y‖+‖x‖)^d*|r|)*(t^d*Real.exp (-c*t)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ) c hc).const_mul
      (C*(2*‖y‖+‖x‖)^d*|r|)
    simpa [Real.rpow_natCast] using h
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (1 : ℝ), eventually_ge_atTop |r|] with t ht ht1 htr
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := r) (f := fun s : ℝ => periodIntegrand f x y ((s : ℂ)+I*t))
    (C := C*(2*‖y‖+‖x‖)^d*(t^d*Real.exp (-c*t))) ?_
  · simpa [horizontalShiftIntegral, mul_assoc, mul_left_comm, mul_comm] using hi
  intro s hs
  have hs' : |s| ≤ t := le_trans (by
    simpa using Set.abs_sub_left_of_mem_uIcc (Set.uIoc_subset_uIcc hs)) htr
  calc
    ‖periodIntegrand f x y ((s : ℂ)+I*t)‖ =
        ‖f (ofComplex ((s : ℂ)+I*t))‖ * ‖((s : ℂ)+I*t)*y-x‖^d := by
      simp [periodIntegrand, norm_pow]
    _ ≤ (C*Real.exp (-c*t)) * (t*(2*‖y‖+‖x‖))^d :=
      mul_le_mul (hbound t ht ht0 s)
        (pow_le_pow_left₀ (norm_nonneg _) (horizontalShift_weight_bound x y hs' ht1) d)
        (pow_nonneg (norm_nonneg _) _) (mul_nonneg hC.le (Real.exp_pos _).le)
    _ = C*(2*‖y‖+‖x‖)^d*(t^d*Real.exp (-c*t)) := by rw [mul_pow]; ring

/-- The actual horizontal contour computes the difference of normalized primitive values. -/
theorem horizontalShiftIntegral_eq_sub {d : ℕ} (f : Forms d) (x y : ℂ) (r : ℝ) {t : ℝ} (ht : 0 < t) :
    horizontalShiftIntegral f x y r t =
      eichlerIntegral f x y ((r : ℂ)+I*t) - eichlerIntegral f x y (I*t) := by
  have hpos (s : ℝ) : 0 < ((s : ℂ)+I*t).im := by simpa using ht
  have hc : ContinuousOn (fun s : ℝ => periodIntegrand f x y ((s : ℂ)+I*t))
      (Set.uIcc (0 : ℝ) r) :=
    (periodIntegrand_differentiableOn f x y).continuousOn.comp
      (by fun_prop : ContinuousOn (fun s : ℝ => (s : ℂ)+I*t) (Set.uIcc (0 : ℝ) r))
      (fun s _ => hpos s)
  have hd (s : ℝ) (_hs : s ∈ Set.uIcc (0 : ℝ) r) :
      HasDerivAt (fun u : ℝ => eichlerIntegral f x y ((u : ℂ)+I*t))
        (periodIntegrand f x y ((s : ℂ)+I*t)) s := by
    have hline : HasDerivAt (fun u : ℝ => (u : ℂ)+I*t) (1 : ℂ) s := by
      simpa using (hasDerivAt_id s).ofReal_comp.add_const (I*t)
    have h := ((eichlerIntegral_hasDerivAt f x y _ (hpos s)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hline
    simpa [Function.comp_def] using! h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simpa [horizontalShiftIntegral] using h

/-- The translated vertical approach also has zero infinity-normalized primitive limit. -/
theorem eichlerIntegral_realShift_axis_tendsto_infty {d : ℕ} (f : Forms d) (x y : ℂ) (r : ℝ) :
    Tendsto (fun t : ℝ => eichlerIntegral f x y ((r : ℂ)+I*t)) atTop (𝓝 0) := by
  have h := (horizontalShiftIntegral_tendsto_zero f x y r).add
    (eichlerIntegral_axis_tendsto_infty f x y)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [horizontalShiftIntegral_eq_sub f x y r ht, sub_add_cancel]


end TernaryPoly.BinaryCuspSymbol
