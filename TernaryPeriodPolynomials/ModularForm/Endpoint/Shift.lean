module

public import TernaryPeriodPolynomials.ModularForm.Endpoint.Horizontal

@[expose] public section

noncomputable section
open Complex MeasureTheory Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspPeriod

/-- The actual horizontal contour computes the difference of normalized primitive values. -/
theorem horizontalIntegral_eq_sub {d : ℕ} (f : Forms d) (x y : ℂ) {t : ℝ} (ht : 0 < t) :
    horizontalIntegral f x y t =
      eichlerIntegral f x y (1+I*t) - eichlerIntegral f x y (I*t) := by
  have hpos (s : ℝ) : 0 < ((s : ℂ)+I*t).im := by simpa using ht
  have hc : ContinuousOn (fun s : ℝ => periodIntegrand f x y ((s : ℂ)+I*t))
      (Set.uIcc (0 : ℝ) 1) :=
    (periodIntegrand_differentiableOn f x y).continuousOn.comp
      (by fun_prop : ContinuousOn (fun s : ℝ => (s : ℂ)+I*t) (Set.uIcc (0 : ℝ) 1))
      (fun s _ => hpos s)
  have hd (s : ℝ) (_hs : s ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun u : ℝ => eichlerIntegral f x y ((u : ℂ)+I*t))
        (periodIntegrand f x y ((s : ℂ)+I*t)) s := by
    have hline : HasDerivAt (fun u : ℝ => (u : ℂ)+I*t) (1 : ℂ) s := by
      simpa using (hasDerivAt_id s).ofReal_comp.add_const (I*t)
    have h := ((eichlerIntegral_hasDerivAt f x y _ (hpos s)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s hline
    simpa [Function.comp_def] using! h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simpa [horizontalIntegral] using h

/-- The translated vertical approach also has zero infinity-normalized primitive limit. -/
theorem eichlerIntegral_shift_axis_tendsto_infty {d : ℕ} (f : Forms d) (x y : ℂ) :
    Tendsto (fun t : ℝ => eichlerIntegral f x y (1+I*t)) atTop (𝓝 0) := by
  have h := (horizontalIntegral_tendsto_zero f x y).add
    (eichlerIntegral_axis_tendsto_infty f x y)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [horizontalIntegral_eq_sub f x y ht, sub_add_cancel]

end TernaryPoly.BinaryCuspPeriod
