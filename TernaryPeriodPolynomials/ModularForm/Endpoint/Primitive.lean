module

public import TernaryPeriodPolynomials.ModularForm.Endpoint.Ray

@[expose] public section


noncomputable section
open Complex MvPolynomial MeasureTheory Filter
open UpperHalfPlane hiding I
open scoped Topology

namespace TernaryPoly.BinaryCuspPeriod

/-- A fixed actual primitive, prior to normalization at the cusp. -/
def chosenPrimitive {d : ℕ} (f : Forms d) (x y : ℂ) : ℂ → ℂ :=
  Classical.choose (exists_period_primitive f x y)

/-- The chosen primitive differentiates to the actual period differential. -/
theorem chosenPrimitive_hasDerivAt {d : ℕ} (f : Forms d) (x y z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (chosenPrimitive f x y) (periodIntegrand f x y z) z :=
  Classical.choose_spec (exists_period_primitive f x y) z hz

/-- Normalization subtracts an explicit convergent integral, with no unspecified cusp limit. -/
def eichlerIntegral {d : ℕ} (f : Forms d) (x y z : ℂ) : ℂ :=
  chosenPrimitive f x y z - chosenPrimitive f x y I -
    ∫ t : ℝ in Set.Ioi 1, rayIntegrand f x y t

/-- The actual infinity-normalized primitive has the required holomorphic derivative. -/
theorem eichlerIntegral_hasDerivAt {d : ℕ} (f : Forms d) (x y z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (eichlerIntegral f x y) (periodIntegrand f x y z) z :=
  ((chosenPrimitive_hasDerivAt f x y z hz).sub_const _).sub_const _

/-- The genuine finite vertical fundamental theorem of calculus. -/
theorem rayIntegral_eq_primitive_sub {d : ℕ} (f : Forms d) (x y : ℂ)
    (F : ℂ → ℂ) (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (periodIntegrand f x y z) z)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ in a..b, rayIntegrand f x y t) = F (I*b) - F (I*a) := by
  have hpos (t : ℝ) (ht : t ∈ Set.uIcc a b) : 0 < (I*(t : ℂ)).im := by
    simp only [mul_im, Complex.I_re, ofReal_im, zero_mul, Complex.I_im, ofReal_re, one_mul, zero_add]
    exact lt_of_lt_of_le (lt_min ha hb) ht.1
  have hline (t : ℝ) : HasDerivAt (fun u : ℝ => I*(u : ℂ)) I t := by
    simpa using (hasDerivAt_id t).ofReal_comp.const_mul I
  have hc : ContinuousOn (rayIntegrand f x y) (Set.uIcc a b) :=
    ((periodIntegrand_differentiableOn f x y).continuousOn.comp
      (by fun_prop : ContinuousOn (fun t : ℝ => I*(t : ℂ)) (Set.uIcc a b)) hpos).mul
      continuousOn_const
  have hd (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      HasDerivAt (fun u : ℝ => F (I*u)) (rayIntegrand f x y t) t := by
    have h := ((hF _ (hpos t ht)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hline t)
    simpa [Function.comp_def, rayIntegrand, mul_comm] using! h
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

/-- On the imaginary axis, the normalized primitive is the negative actual integral tail. -/
theorem eichlerIntegral_axis {d : ℕ} (f : Forms d) (x y : ℂ) {t : ℝ} (ht : 0 < t) :
    eichlerIntegral f x y (I*t) = -∫ u : ℝ in Set.Ioi t, rayIntegrand f x y u := by
  have he := rayIntegral_eq_primitive_sub f x y (chosenPrimitive f x y)
    (chosenPrimitive_hasDerivAt f x y) (a := 1) (by norm_num) ht
  simp only [ofReal_one, mul_one] at he
  have hs := intervalIntegral.integral_interval_add_Ioi
    ((rayIntegrand_integrable f x y).mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))
    ((rayIntegrand_integrable f x y).mono_set (Set.Ioi_subset_Ioi ht.le))
  rw [he] at hs
  unfold eichlerIntegral
  linear_combination hs

/-- The actual Eichler primitive tends to zero at the infinite cusp along the vertical axis. -/
theorem eichlerIntegral_axis_tendsto_infty {d : ℕ} (f : Forms d) (x y : ℂ) :
    Tendsto (fun t : ℝ => eichlerIntegral f x y (I*t)) atTop (𝓝 0) := by
  have h := (tendsto_integral_Ioi_zero (f := rayIntegrand f x y) (μ := volume) tendsto_id).neg
  simp only [neg_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (eichlerIntegral_axis f x y ht).symm

/-- The value at the zero cusp is minus the literal full Mellin period. -/
theorem eichlerIntegral_axis_tendsto_zero {d : ℕ} (f : Forms d) (x y : ℂ) :
    Tendsto (fun t : ℝ => eichlerIntegral f x y (I*t)) (𝓝[Set.Ioi 0] 0)
      (𝓝 (-eval ![x,y] (period f))) := by
  rw [eval_period_eq_integral]
  have h := ((rayIntegrand_integrable f x y).continuousWithinAt_Ici_primitive_Ioi.mono
    Set.Ioi_subset_Ici_self).neg
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (eichlerIntegral_axis f x y ht).symm

end TernaryPoly.BinaryCuspPeriod
