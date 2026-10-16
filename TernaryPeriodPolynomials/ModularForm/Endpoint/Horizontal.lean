module

public import TernaryPeriodPolynomials.ModularForm.Endpoint.Primitive
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section


noncomputable section
open Complex MvPolynomial MeasureTheory Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspPeriod

/-- The actual horizontal contour integral at height t. -/
def horizontalIntegral {d : ℕ} (f : Forms d) (x y : ℂ) (t : ℝ) : ℂ :=
  ∫ s : ℝ in 0..1, periodIntegrand f x y ((s : ℂ)+I*t)

/-- Uniform exponential decay on every horizontal line sufficiently high in the upper half plane. -/
theorem cusp_uniform_horizontal_decay {d : ℕ} (f : Forms d) :
    ∃ c > 0, ∃ C > 0, ∃ T : ℝ, ∀ t : ℝ, T ≤ t → 0 < t → ∀ s : ℝ,
      ‖f (ofComplex ((s : ℂ)+I*t))‖ ≤ C * Real.exp (-c*t) := by
  obtain ⟨c, hc, ho⟩ := CuspFormClass.exp_decay_atImInfty' f
  obtain ⟨C, hC, hbound⟩ := ho.exists_pos
  obtain ⟨T, hT⟩ := (atImInfty_mem _).mp hbound.bound
  refine ⟨c, hc, C, hC, T, ?_⟩
  intro t ht hpos s
  have hz : 0 < ((s : ℂ)+I*t).im := by simpa using hpos
  have h := hT (ofComplex ((s : ℂ)+I*t)) (by simpa [ofComplex_apply_of_im_pos hz] using ht)
  simpa [ofComplex_apply_of_im_pos hz, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using h

/-- A uniform polynomial bound for the weight factor on the unit horizontal interval. -/
theorem horizontal_weight_bound (x y : ℂ) {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ht : 1 ≤ t) : ‖((s : ℂ)+I*t)*y-x‖ ≤ t*(2*‖y‖+‖x‖) := by
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hz : ‖(s : ℂ)+I*t‖ ≤ 2*t := by
    calc
      ‖(s : ℂ)+I*t‖ ≤ ‖(s : ℂ)‖+‖I*(t : ℂ)‖ := norm_add_le _ _
      _ = s+t := by simp [abs_of_nonneg hs.1, abs_of_nonneg ht0]
      _ ≤ 2*t := by linarith [hs.2]
  calc
    ‖((s : ℂ)+I*t)*y-x‖ ≤ ‖((s : ℂ)+I*t)*y‖+‖x‖ := norm_sub_le _ _
    _ = ‖(s : ℂ)+I*t‖*‖y‖+‖x‖ := by rw [norm_mul]
    _ ≤ (2*t)*‖y‖+t*‖x‖ := by nlinarith [norm_nonneg x, norm_nonneg y]
    _ = t*(2*‖y‖+‖x‖) := by ring

/-- The actual horizontal integral vanishes at infinity by uniform cusp exponential decay. -/
theorem horizontalIntegral_tendsto_zero {d : ℕ} (f : Forms d) (x y : ℂ) :
    Tendsto (horizontalIntegral f x y) atTop (𝓝 0) := by
  obtain ⟨c, hc, C, hC, T, hbound⟩ := cusp_uniform_horizontal_decay f
  have hlim : Tendsto (fun t : ℝ => C*(2*‖y‖+‖x‖)^d*(t^d*Real.exp (-c*t)))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (d : ℝ) c hc).const_mul
      (C*(2*‖y‖+‖x‖)^d)
    simpa [Real.rpow_natCast] using h
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (1 : ℝ)] with t ht ht1
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun s : ℝ => periodIntegrand f x y ((s : ℂ)+I*t))
    (C := C*(2*‖y‖+‖x‖)^d*(t^d*Real.exp (-c*t))) ?_
  · simpa [horizontalIntegral] using hi
  intro s hs
  have hs' : s ∈ Set.Icc (0 : ℝ) 1 := by
    have hs0 : 0 < s ∧ s ≤ 1 := by simpa using hs
    exact ⟨hs0.1.le, hs0.2⟩
  calc
    ‖periodIntegrand f x y ((s : ℂ)+I*t)‖ =
        ‖f (ofComplex ((s : ℂ)+I*t))‖ * ‖((s : ℂ)+I*t)*y-x‖^d := by
      simp [periodIntegrand, norm_pow]
    _ ≤ (C*Real.exp (-c*t)) * (t*(2*‖y‖+‖x‖))^d :=
      mul_le_mul (hbound t ht ht0 s)
        (pow_le_pow_left₀ (norm_nonneg _) (horizontal_weight_bound x y hs' ht1) d)
        (pow_nonneg (norm_nonneg _) _) (mul_nonneg hC.le (Real.exp_pos _).le)
    _ = C*(2*‖y‖+‖x‖)^d*(t^d*Real.exp (-c*t)) := by rw [mul_pow]; ring

end TernaryPoly.BinaryCuspPeriod
