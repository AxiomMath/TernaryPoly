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
# Radial moments of the unit disc

The moments `discMoment m a = ∫_{|ζ| < 1} |ζ|^m (1 - |ζ|²)^a dA` are computed in polar
coordinates: `discMoment m a = 2π ∫₀¹ r^(m+1) (1 - r²)^a dr` for `a > -1`.  For natural exponents
`a = j` the radial integral is `m! j! / (2 (m + j + 1)!)` by a Pascal-type recursion, which gives
the lower bound for `discMoment (2n) (k - 2)` and the decay `O((n+1)^(-(⌊k/2⌋-1)))` of
`discMoment n (k/2 - 2)`.  The file also contains the polar-coordinate decomposition of lower
integrals over the unit disc used for the weighted Parseval identity.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped Real NNReal ENNReal

namespace TernaryPeriodPolynomials.Regularity

section Radial

theorem hasDerivAt_rad0 {a : ℝ} (ha : -1 < a) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun r : ℝ => -(1 - r ^ 2) ^ (a + 1) / (2 * (a + 1))) (x * (1 - x ^ 2) ^ a) x := by
  have ha1 : 0 < a + 1 := by linarith
  have hpos : 0 < 1 - x ^ 2 := by nlinarith
  have h1 : HasDerivAt (fun r : ℝ => 1 - r ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have h2 := h1.rpow_const (p := a + 1) (Or.inl hpos.ne')
  have h3 := h2.neg.div_const (2 * (a + 1))
  refine h3.congr_deriv ?_
  rw [show a + 1 - 1 = a by ring, div_eq_iff (mul_ne_zero two_ne_zero ha1.ne')]
  ring

theorem continuous_antideriv0 {a : ℝ} (ha : -1 < a) :
    Continuous (fun r : ℝ => -(1 - r ^ 2) ^ (a + 1) / (2 * (a + 1))) := by
  have h : Continuous fun r : ℝ => (1 - r ^ 2) ^ (a + 1) :=
    (continuous_const.sub (continuous_pow 2)).rpow_const (fun x => Or.inr (by linarith))
  exact h.neg.div_const _

theorem integrableOn_rad0 {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun r : ℝ => r * (1 - r ^ 2) ^ a) (Ioc 0 1) :=
  intervalIntegral.integrableOn_deriv_of_nonneg (continuous_antideriv0 ha).continuousOn
    (fun x hx => hasDerivAt_rad0 ha hx.1 hx.2)
    (fun x hx => mul_nonneg hx.1.le (Real.rpow_nonneg (by nlinarith [hx.1, hx.2]) _))

theorem integral_rad0 {a : ℝ} (ha : -1 < a) :
    ∫ r in (0 : ℝ)..1, r * (1 - r ^ 2) ^ a = 1 / (2 * (a + 1)) := by
  have hint : IntervalIntegrable (fun r : ℝ => r * (1 - r ^ 2) ^ a) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 (integrableOn_rad0 ha)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuous_antideriv0 ha).continuousOn (fun x hx => hasDerivAt_rad0 ha hx.1 hx.2) hint]
  have ha1 : 0 < a + 1 := by linarith
  have h0 : (0 : ℝ) ^ (a + 1) = 0 := Real.zero_rpow ha1.ne'
  have hne : a + 1 ≠ 0 := ha1.ne'
  simp [h0]
  field_simp

theorem intervalIntegrable_rad (m : ℕ) {a : ℝ} (ha : -1 < a) :
    IntervalIntegrable (fun r : ℝ => r ^ (m + 1) * (1 - r ^ 2) ^ a) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hmeas : Measurable fun r : ℝ => r ^ (m + 1) * (1 - r ^ 2) ^ a := by fun_prop
  refine Integrable.mono' (integrableOn_rad0 ha) hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun r hr => ?_)
  have hr0 : 0 ≤ r := hr.1.le
  have hr1 : r ≤ 1 := hr.2
  have hnn : 0 ≤ (1 - r ^ 2) ^ a := Real.rpow_nonneg (by nlinarith) _
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hr0 _) hnn)]
  refine mul_le_mul_of_nonneg_right ?_ hnn
  calc r ^ (m + 1) = r ^ m * r := pow_succ r m
    _ ≤ 1 * r := mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 hr1) hr0
    _ = r := one_mul r

theorem integral_rad_pos (m : ℕ) {a : ℝ} (ha : -1 < a) :
    0 < ∫ r in (0 : ℝ)..1, r ^ (m + 1) * (1 - r ^ 2) ^ a :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_rad m ha)
    (fun r hr => mul_pos (pow_pos hr.1 _)
      (Real.rpow_pos_of_pos (by nlinarith [hr.1, hr.2]) _)) zero_lt_one

theorem lintegral_rad_eq (m : ℕ) {a : ℝ} (ha : -1 < a) :
    ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ (m + 1) * (1 - r ^ 2) ^ a) =
      ENNReal.ofReal (∫ r in (0 : ℝ)..1, r ^ (m + 1) * (1 - r ^ 2) ^ a) := by
  have hint : IntegrableOn (fun r : ℝ => r ^ (m + 1) * (1 - r ^ 2) ^ a) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 (intervalIntegrable_rad m ha)
  have hint' : IntegrableOn (fun r : ℝ => r ^ (m + 1) * (1 - r ^ 2) ^ a) (Ioo 0 1) :=
    hint.mono_set Ioo_subset_Ioc_self
  have hae : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun r : ℝ => r ^ (m + 1) * (1 - r ^ 2) ^ a :=
    (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun r hr =>
      mul_nonneg (pow_nonneg hr.1.le _) (Real.rpow_nonneg (by nlinarith [hr.1, hr.2]) _))
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal hint' hae]

end Radial

section Beta

theorem factorial_add_le (n : ℕ) : ∀ i : ℕ, (n + i).factorial ≤ n.factorial * (n + i) ^ i
  | 0 => by simp
  | i + 1 => by
    calc (n + (i + 1)).factorial = (n + i + 1) * (n + i).factorial := by
          rw [← add_assoc, Nat.factorial_succ]
      _ ≤ (n + i + 1) * (n.factorial * (n + i) ^ i) :=
          Nat.mul_le_mul_left _ (factorial_add_le n i)
      _ ≤ (n + i + 1) * (n.factorial * (n + i + 1) ^ i) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) _))
      _ = n.factorial * (n + (i + 1)) ^ (i + 1) := by ring

theorem rad_nat_closed (j : ℕ) : ∀ m : ℕ,
    (∫ r in (0 : ℝ)..1, r ^ (2 * m + 1) * (1 - r ^ 2) ^ j) * (2 * ((m + j + 1).factorial : ℝ)) =
      (m.factorial : ℝ) * j.factorial := by
  induction j with
  | zero =>
    intro m
    have h : (∫ r in (0 : ℝ)..1, r ^ (2 * m + 1) * (1 - r ^ 2) ^ 0) = 1 / (2 * (m : ℝ) + 2) := by
      simp only [pow_zero, mul_one, integral_pow]
      rw [one_pow, zero_pow (by omega : 2 * m + 1 + 1 ≠ 0), sub_zero]
      push_cast
      ring
    have hm1 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * m.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hne : (2 * (m : ℝ) + 2) ≠ 0 := by positivity
    rw [h, Nat.add_zero, hm1, Nat.factorial_zero, Nat.cast_one, mul_one]
    calc 1 / (2 * (m : ℝ) + 2) * (2 * (((m : ℝ) + 1) * m.factorial))
        = ((2 * (m : ℝ) + 2) / (2 * (m : ℝ) + 2)) * m.factorial := by ring
      _ = m.factorial := by rw [div_self hne, one_mul]
  | succ j ih =>
    intro m
    have hrec : (∫ r in (0 : ℝ)..1, r ^ (2 * m + 1) * (1 - r ^ 2) ^ (j + 1)) =
        (∫ r in (0 : ℝ)..1, r ^ (2 * m + 1) * (1 - r ^ 2) ^ j) -
          ∫ r in (0 : ℝ)..1, r ^ (2 * (m + 1) + 1) * (1 - r ^ 2) ^ j := by
      have hc1 : Continuous fun r : ℝ => r ^ (2 * m + 1) * (1 - r ^ 2) ^ j := by fun_prop
      have hc2 : Continuous fun r : ℝ => r ^ (2 * (m + 1) + 1) * (1 - r ^ 2) ^ j := by fun_prop
      rw [← intervalIntegral.integral_sub (hc1.intervalIntegrable 0 1)
        (hc2.intervalIntegrable 0 1)]
      refine intervalIntegral.integral_congr (fun r _ => ?_)
      show r ^ (2 * m + 1) * (1 - r ^ 2) ^ (j + 1) =
        r ^ (2 * m + 1) * (1 - r ^ 2) ^ j - r ^ (2 * (m + 1) + 1) * (1 - r ^ 2) ^ j
      ring
    have e1 := ih m
    have e2 := ih (m + 1)
    have hF : ((m + (j + 1) + 1).factorial : ℝ) =
        ((m : ℝ) + j + 2) * ((m + j + 1).factorial : ℝ) := by
      rw [show m + (j + 1) + 1 = (m + j + 1) + 1 by ring, Nat.factorial_succ]
      push_cast
      ring
    have hF2 : m + 1 + j + 1 = m + (j + 1) + 1 := by ring
    have hm1 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * m.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hj1 : ((j + 1).factorial : ℝ) = ((j : ℝ) + 1) * j.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hF2, hF, hm1] at e2
    rw [hrec, hF, hj1]
    linear_combination ((m : ℝ) + j + 2) * e1 - e2

theorem aux_ineq {P Jf Nn F D I : ℝ} {n : ℕ} (hP : 0 < P) (hJ : 0 < Jf) (hF : 0 < F)
    (hD : 0 < D) (hcl : I * (2 * F) = Nn * Jf) (hle : F ≤ Nn * D ^ n) :
    P * Jf / D ^ n ≤ 2 * P * I := by
  rw [div_le_iff₀ (pow_pos hD n)]
  have h1 : 2 * I * F = Nn * Jf := by linear_combination hcl
  have h2 : P * Jf * F ≤ 2 * P * I * D ^ n * F := by
    calc P * Jf * F ≤ P * Jf * (Nn * D ^ n) := by gcongr
      _ = P * (Nn * Jf) * D ^ n := by ring
      _ = P * (2 * I * F) * D ^ n := by rw [h1]
      _ = 2 * P * I * D ^ n * F := by ring
  exact le_of_mul_le_mul_right h2 hF

theorem aux_ineq2 {J P Bf Pf F X Y : ℝ} {m : ℕ} (hJ : 0 ≤ J) (hP : 0 < P) (hPf : 0 < Pf)
    (hY : 0 < Y) (hcl : J * (2 * F) = Pf * Bf) (hF : Pf * X ^ m ≤ F)
    (hYX : Y ≤ 2 * X) : 2 * P * J ≤ P * Bf * 2 ^ m / Y ^ m := by
  rw [le_div_iff₀ (pow_pos hY m)]
  have h1 : 2 * J * X ^ m ≤ Bf := by
    have h : Pf * (2 * J * X ^ m) ≤ Pf * Bf := by
      calc Pf * (2 * J * X ^ m) = J * (2 * (Pf * X ^ m)) := by ring
        _ ≤ J * (2 * F) := by gcongr
        _ = Pf * Bf := hcl
    exact le_of_mul_le_mul_left h hPf
  have h2 : Y ^ m ≤ (2 * X) ^ m := by gcongr
  rw [mul_pow] at h2
  calc 2 * P * J * Y ^ m ≤ 2 * P * J * (2 ^ m * X ^ m) := by gcongr
    _ = P * 2 ^ m * (2 * J * X ^ m) := by ring
    _ ≤ P * 2 ^ m * Bf := by gcongr
    _ = P * Bf * 2 ^ m := by ring

end Beta

section Polar

theorem measurable_polarCoord_symm :
    Measurable (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  have h : (fun p : ℝ × ℝ => Complex.polarCoord.symm p) =
      fun p => (p.1 : ℂ) * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I) :=
    funext Complex.polarCoord_symm_apply
  have h1 : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) :=
    Complex.continuous_ofReal.comp continuous_fst
  have h2 : Continuous fun p : ℝ × ℝ => (Real.cos p.2 : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_snd)
  have h3 : Continuous fun p : ℝ × ℝ => (Real.sin p.2 : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_snd)
  rw [h]
  exact (h1.mul (h2.add (h3.mul continuous_const))).measurable

theorem norm_polarCoord_symm (p : ℝ × ℝ) : ‖Complex.polarCoord.symm p‖ = |p.1| := by
  rw [Complex.polarCoord_symm_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.ofReal_cos, Complex.ofReal_sin, Complex.norm_cos_add_sin_mul_I, mul_one]

/-- Polar decomposition of a lower integral over the unit disc. -/
theorem lintegral_ball_polar {G : ℂ → ℝ≥0∞} (hG : ContinuousOn G (Metric.ball 0 1)) :
    ∫⁻ ζ in Metric.ball (0 : ℂ) 1, G ζ =
      ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal r *
        ∫⁻ θ in Ioo (-π) π, G (Complex.polarCoord.symm (r, θ)) := by
  classical
  have hs : MeasurableSet (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball.measurableSet
  have hmeas : Measurable ((Metric.ball (0 : ℂ) 1).indicator G) := by
    have e : (Metric.ball (0 : ℂ) 1).indicator G =
        (Metric.ball (0 : ℂ) 1).piecewise G (fun _ => 0) := by
      funext x
      by_cases hx : x ∈ Metric.ball (0 : ℂ) 1 <;>
        simp only [Set.indicator_apply, Set.piecewise, hx, ↓reduceIte]
    rw [e]
    exact hG.measurable_piecewise continuousOn_const hs
  have hf : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 *
      (Metric.ball (0 : ℂ) 1).indicator G (Complex.polarCoord.symm p)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hmeas.comp measurable_polarCoord_symm)
  have htarget : (volume : Measure (ℝ × ℝ)).restrict polarCoord.target =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π)) := by
    rw [polarCoord_target, Measure.prod_restrict, Measure.volume_eq_prod]
  have h2 := Complex.lintegral_comp_polarCoord_symm ((Metric.ball (0 : ℂ) 1).indicator G)
  simp only [smul_eq_mul] at h2
  have h3 : ∀ r ∈ Ioi (0 : ℝ),
      (∫⁻ θ in Ioo (-π) π, ENNReal.ofReal r *
        (Metric.ball (0 : ℂ) 1).indicator G (Complex.polarCoord.symm (r, θ))) =
      (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal r *
        ∫⁻ θ in Ioo (-π) π, G (Complex.polarCoord.symm (r, θ))) r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    by_cases h1 : r < 1
    · have hmem : ∀ θ : ℝ, Complex.polarCoord.symm (r, θ) ∈ Metric.ball (0 : ℂ) 1 := fun θ => by
        rw [mem_ball_zero_iff, norm_polarCoord_symm]
        simpa [abs_of_pos hr0] using h1
      have hind : ∀ θ : ℝ, (Metric.ball (0 : ℂ) 1).indicator G (Complex.polarCoord.symm (r, θ)) =
          G (Complex.polarCoord.symm (r, θ)) := fun θ => Set.indicator_of_mem (hmem θ) G
      rw [Set.indicator_of_mem (show r ∈ Iio (1 : ℝ) from h1)]
      simp only [hind]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    · have hmem : ∀ θ : ℝ, Complex.polarCoord.symm (r, θ) ∉ Metric.ball (0 : ℂ) 1 :=
        fun θ hθ => by
          rw [mem_ball_zero_iff, norm_polarCoord_symm] at hθ
          have : r < 1 := by simpa [abs_of_pos hr0] using hθ
          exact h1 this
      have hind : ∀ θ : ℝ, (Metric.ball (0 : ℂ) 1).indicator G (Complex.polarCoord.symm (r, θ)) =
          0 := fun θ => by
        rw [Set.indicator_apply, ite_eq_right (hmem θ)]
      have hnot : r ∉ Iio (1 : ℝ) := h1
      rw [Set.indicator_apply, ite_eq_right hnot]
      simp only [hind, mul_zero, lintegral_zero]
  rw [← lintegral_indicator hs G, ← h2, htarget, lintegral_prod _ hf.aemeasurable]
  calc _ = ∫⁻ r in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator (fun r => ENNReal.ofReal r *
        ∫⁻ θ in Ioo (-π) π, G (Complex.polarCoord.symm (r, θ))) r :=
        setLIntegral_congr_fun measurableSet_Ioi h3
    _ = _ := by
        rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          Iio_inter_Ioi]

end Polar

section Moments

theorem continuousOn_moment_ofReal (m : ℕ) (a : ℝ) :
    ContinuousOn (fun ζ : ℂ => ENNReal.ofReal (‖ζ‖ ^ m * (1 - ‖ζ‖ ^ 2) ^ a))
      (Metric.ball 0 1) := by
  refine ENNReal.continuous_ofReal.comp_continuousOn ?_
  refine ContinuousOn.mul (continuous_norm.pow m).continuousOn ?_
  refine ContinuousOn.rpow_const (continuous_const.sub (continuous_norm.pow 2)).continuousOn ?_
  intro ζ hζ
  have h := mem_ball_zero_iff.1 hζ
  have h1 : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  exact Or.inl h1.ne'

theorem continuousOn_moment (m : ℕ) (a : ℝ) :
    ContinuousOn (fun ζ : ℂ => ‖ζ‖ ^ m * (1 - ‖ζ‖ ^ 2) ^ a) (Metric.ball 0 1) := by
  refine ContinuousOn.mul (continuous_norm.pow m).continuousOn ?_
  refine ContinuousOn.rpow_const (continuous_const.sub (continuous_norm.pow 2)).continuousOn ?_
  intro ζ hζ
  have h := mem_ball_zero_iff.1 hζ
  have h1 : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
  exact Or.inl h1.ne'

theorem moment_nonneg (m : ℕ) (a : ℝ) {ζ : ℂ} (hζ : ζ ∈ Metric.ball (0 : ℂ) 1) :
    0 ≤ ‖ζ‖ ^ m * (1 - ‖ζ‖ ^ 2) ^ a := by
  have h := mem_ball_zero_iff.1 hζ
  exact mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (Real.rpow_nonneg (by nlinarith [norm_nonneg ζ]) _)

theorem lintegral_moment (m : ℕ) (a : ℝ) :
    ∫⁻ ζ in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (‖ζ‖ ^ m * (1 - ‖ζ‖ ^ 2) ^ a) =
      ENNReal.ofReal (2 * π) *
        ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r ^ (m + 1) * (1 - r ^ 2) ^ a) := by
  rw [lintegral_ball_polar (continuousOn_moment_ofReal m a)]
  have h : ∀ r ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal r * ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal (‖Complex.polarCoord.symm (r, θ)‖ ^ m *
        (1 - ‖Complex.polarCoord.symm (r, θ)‖ ^ 2) ^ a) =
      ENNReal.ofReal (2 * π) * ENNReal.ofReal (r ^ (m + 1) * (1 - r ^ 2) ^ a) := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hA : 0 ≤ r ^ m * (1 - r ^ 2) ^ a :=
      mul_nonneg (pow_nonneg hr0.le _) (Real.rpow_nonneg (by nlinarith [hr.1, hr.2]) _)
    have hnorm : ∀ θ : ℝ, ‖Complex.polarCoord.symm (r, θ)‖ = r := fun θ => by
      rw [norm_polarCoord_symm]
      exact abs_of_pos hr0
    simp only [hnorm]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo, ← ENNReal.ofReal_mul hA,
      ← ENNReal.ofReal_mul hr0.le, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
    congr 1
    ring
  refine (setLIntegral_congr_fun measurableSet_Ioo h).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem integrableOn_moment (m : ℕ) {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun ζ : ℂ => ‖ζ‖ ^ m * (1 - ‖ζ‖ ^ 2) ^ a) (Metric.ball 0 1) := by
  have hae : 0 ≤ᵐ[volume.restrict (Metric.ball (0 : ℂ) 1)]
      fun ζ : ℂ => ‖ζ‖ ^ m * (1 - ‖ζ‖ ^ 2) ^ a :=
    (ae_restrict_iff' Metric.isOpen_ball.measurableSet).2
      (Filter.Eventually.of_forall fun ζ hζ => moment_nonneg m a hζ)
  unfold IntegrableOn
  refine ⟨(continuousOn_moment m a).aestronglyMeasurable Metric.isOpen_ball.measurableSet, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal hae).2 ?_
  rw [lintegral_moment, lintegral_rad_eq m ha]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem discMoment_nonneg (m : ℕ) (a : ℝ) : 0 ≤ discMoment m a :=
  setIntegral_nonneg Metric.isOpen_ball.measurableSet fun _ hζ => moment_nonneg m a hζ

theorem ofReal_discMoment (m : ℕ) {a : ℝ} (ha : -1 < a) :
    ENNReal.ofReal (discMoment m a) = ENNReal.ofReal (2 * π) *
      ENNReal.ofReal (∫ r in (0 : ℝ)..1, r ^ (m + 1) * (1 - r ^ 2) ^ a) := by
  have hae : 0 ≤ᵐ[volume.restrict (Metric.ball (0 : ℂ) 1)]
      fun ζ : ℂ => ‖ζ‖ ^ m * (1 - ‖ζ‖ ^ 2) ^ a :=
    (ae_restrict_iff' Metric.isOpen_ball.measurableSet).2
      (Filter.Eventually.of_forall fun ζ hζ => moment_nonneg m a hζ)
  unfold discMoment
  rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_moment m ha) hae, lintegral_moment,
    lintegral_rad_eq m ha]

/-- The radial formula `discMoment m a = 2π ∫₀¹ r^(m+1) (1 - r²)^a dr`. -/
theorem discMoment_eq (m : ℕ) (a : ℝ) (ha : -1 < a) :
    discMoment m a = 2 * Real.pi * ∫ r in (0 : ℝ)..1, r ^ (m + 1) * (1 - r ^ 2) ^ a := by
  have hI := integral_rad_pos m ha
  have h := ofReal_discMoment m ha
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (discMoment_nonneg m a)
    (mul_pos (by positivity) hI).le).1 h

theorem discMoment_pos (m : ℕ) {a : ℝ} (ha : -1 < a) : 0 < discMoment m a := by
  rw [discMoment_eq m a ha]
  exact mul_pos (by positivity) (integral_rad_pos m ha)

theorem discMoment_zero (a : ℝ) (ha : -1 < a) : discMoment 0 a = Real.pi / (a + 1) := by
  rw [discMoment_eq 0 a ha]
  simp only [zero_add, pow_one]
  rw [integral_rad0 ha]
  have ha1 : a + 1 ≠ 0 := (show (0 : ℝ) < a + 1 by linarith).ne'
  field_simp

end Moments

section Bounds

theorem discMoment_two_mul_ge (k n : ℕ) (hk : 2 ≤ k) :
    Real.pi * (Nat.factorial (k - 2) : ℝ) / ((n : ℝ) + k) ^ (k - 1) ≤
      discMoment (2 * n) ((k : ℝ) - 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have e1 : j + 2 - 2 = j := by omega
  have e2 : j + 2 - 1 = j + 1 := by omega
  have e3 : ((j + 2 : ℕ) : ℝ) - 2 = (j : ℝ) := by push_cast; ring
  have hj : (-1 : ℝ) < j := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  rw [e1, e2, e3, discMoment_eq (2 * n) (j : ℝ) hj]
  have hI : (∫ r in (0 : ℝ)..1, r ^ (2 * n + 1) * (1 - r ^ 2) ^ (j : ℝ)) =
      ∫ r in (0 : ℝ)..1, r ^ (2 * n + 1) * (1 - r ^ 2) ^ j := by
    simp only [Real.rpow_natCast]
  rw [hI]
  have hcl := rad_nat_closed j n
  have hF : ((n + j + 1).factorial : ℝ) ≤
      (n.factorial : ℝ) * ((n : ℝ) + ((j + 2 : ℕ) : ℝ)) ^ (j + 1) := by
    have h1 := factorial_add_le n (j + 1)
    have h2 : (n + (j + 1)) ^ (j + 1) ≤ (n + (j + 2)) ^ (j + 1) :=
      Nat.pow_le_pow_left (by omega) _
    have h3 : (n + j + 1).factorial ≤ n.factorial * (n + (j + 2)) ^ (j + 1) := by
      calc (n + j + 1).factorial = (n + (j + 1)).factorial := by rw [add_assoc]
        _ ≤ n.factorial * (n + (j + 1)) ^ (j + 1) := h1
        _ ≤ n.factorial * (n + (j + 2)) ^ (j + 1) := Nat.mul_le_mul_left _ h2
    exact_mod_cast h3
  exact aux_ineq (by positivity) (by positivity) (by positivity) (by positivity) hcl hF

theorem discMoment_half_le' (k : ℕ) (hk : 6 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      discMoment n ((k : ℝ) / 2 - 2) ≤ C / ((n : ℝ) + 1) ^ (k / 2 - 1) := by
  obtain ⟨b, hb⟩ : ∃ b : ℕ, k / 2 = b + 2 := ⟨k / 2 - 2, by omega⟩
  have hkb : 2 * b + 4 ≤ k := by omega
  have hbR : (b : ℝ) ≤ (k : ℝ) / 2 - 2 := by
    have : (2 * b + 4 : ℝ) ≤ k := by exact_mod_cast hkb
    linarith
  have ha : (-1 : ℝ) < (k : ℝ) / 2 - 2 := by
    have : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    linarith
  refine ⟨Real.pi * b.factorial * 2 ^ (b + 1), by positivity, fun n => ?_⟩
  obtain ⟨p, s, hs, rfl⟩ : ∃ p s : ℕ, s ≤ 1 ∧ n = 2 * p + s :=
    ⟨n / 2, n % 2, by omega, by omega⟩
  rw [hb, show b + 2 - 1 = b + 1 by omega, discMoment_eq _ _ ha]
  have hmono : (∫ r in (0 : ℝ)..1, r ^ (2 * p + s + 1) * (1 - r ^ 2) ^ ((k : ℝ) / 2 - 2)) ≤
      ∫ r in (0 : ℝ)..1, r ^ (2 * p + 1) * (1 - r ^ 2) ^ b := by
    refine intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_rad _ ha)
      ((by fun_prop : Continuous fun r : ℝ => r ^ (2 * p + 1) * (1 - r ^ 2) ^ b).intervalIntegrable
        0 1) (fun r hr => ?_)
    have hr0 : 0 ≤ r := hr.1
    have hr1 : r ≤ 1 := hr.2
    have h1 : 0 ≤ 1 - r ^ 2 := by nlinarith
    have h2 : 1 - r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r]
    have h3 : (1 - r ^ 2) ^ ((k : ℝ) / 2 - 2) ≤ (1 - r ^ 2) ^ (b : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge' h1 h2 (Nat.cast_nonneg b) hbR
    rw [Real.rpow_natCast] at h3
    have h4 : r ^ (2 * p + s + 1) ≤ r ^ (2 * p + 1) := by
      have : r ^ (2 * p + s + 1) = r ^ (2 * p + 1) * r ^ s := by ring
      rw [this]
      exact mul_le_of_le_one_right (pow_nonneg hr0 _) (pow_le_one₀ hr0 hr1)
    exact mul_le_mul h4 h3 (Real.rpow_nonneg h1 _) (pow_nonneg hr0 _)
  have hcl := rad_nat_closed b p
  have hfac : (p.factorial : ℝ) * ((p : ℝ) + 1) ^ (b + 1) ≤ ((p + b + 1).factorial : ℝ) := by
    have h := Nat.factorial_mul_pow_le_factorial (m := p) (n := b + 1)
    rw [show p + (b + 1) = p + b + 1 by ring] at h
    exact_mod_cast h
  have hJ0 : 0 ≤ ∫ r in (0 : ℝ)..1, r ^ (2 * p + 1) * (1 - r ^ 2) ^ b :=
    intervalIntegral.integral_nonneg zero_le_one fun r hr =>
      mul_nonneg (pow_nonneg hr.1 _) (pow_nonneg (by nlinarith [hr.1, hr.2]) _)
  have hsR : (s : ℝ) ≤ 1 := by exact_mod_cast hs
  have hYX : ((2 * p + s : ℕ) : ℝ) + 1 ≤ 2 * ((p : ℝ) + 1) := by
    push_cast
    linarith
  have key := aux_ineq2 (m := b + 1) (P := Real.pi) (Bf := (b.factorial : ℝ))
    (X := (p : ℝ) + 1) (Y := ((2 * p + s : ℕ) : ℝ) + 1) hJ0 (by positivity) (by positivity)
    (by positivity) hcl hfac hYX
  calc 2 * Real.pi * ∫ r in (0 : ℝ)..1, r ^ (2 * p + s + 1) * (1 - r ^ 2) ^ ((k : ℝ) / 2 - 2)
      ≤ 2 * Real.pi * ∫ r in (0 : ℝ)..1, r ^ (2 * p + 1) * (1 - r ^ 2) ^ b :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ _ := key

theorem discMoment_half_le (k : ℕ) (hk : 6 ≤ k) :
    ∃ C : ℝ, ∀ n : ℕ, discMoment n ((k : ℝ) / 2 - 2) ≤ C / ((n : ℝ) + 1) ^ (k / 2 - 1) := by
  obtain ⟨C, _, hC⟩ := discMoment_half_le' k hk
  exact ⟨C, hC⟩

theorem aux_ratio {A B C u P S D : ℝ} {e g : ℕ} (hA0 : 0 ≤ A) (hB : 0 < B) (hP : 0 < P)
    (hS : 0 < S) (hu : 1 ≤ u) (hAC : A * u ^ e ≤ C) (hBP : P ≤ B * S * u ^ g)
    (hD : u ^ 4 ≤ D) (hexp : g + 2 ≤ 2 * e + 4) :
    A ^ 2 / (D * B) ≤ (C ^ 2 * S / P) * (1 / u ^ 2) := by
  have hupos : 0 < u := by linarith
  have hDpos : 0 < D := lt_of_lt_of_le (pow_pos hupos 4) hD
  have hDB : 0 < D * B := mul_pos hDpos hB
  have hAu : 0 ≤ A * u ^ e := mul_nonneg hA0 (pow_nonneg hupos.le e)
  have hsq : (A * u ^ e) ^ 2 ≤ C ^ 2 := by
    have := mul_self_le_mul_self hAu hAC
    nlinarith [this]
  have hpow : u ^ (g + 2) ≤ u ^ (2 * e + 4) := pow_le_pow_right₀ hu hexp
  have hBS : 0 ≤ B * S := mul_nonneg hB.le hS.le
  have key : A ^ 2 * P * u ^ 2 ≤ C ^ 2 * S * (D * B) := by
    calc A ^ 2 * P * u ^ 2 ≤ A ^ 2 * (B * S * u ^ g) * u ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBP (sq_nonneg A)) (sq_nonneg u)
      _ = B * S * (A ^ 2 * u ^ (g + 2)) := by ring
      _ ≤ B * S * (A ^ 2 * u ^ (2 * e + 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (sq_nonneg A)) hBS
      _ = B * S * ((A * u ^ e) ^ 2 * u ^ 4) := by ring
      _ ≤ B * S * (C ^ 2 * D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hsq hD (pow_nonneg hupos.le 4) (sq_nonneg C)) hBS
      _ = C ^ 2 * S * (D * B) := by ring
  rw [div_le_iff₀ hDB]
  have hu0 : u ≠ 0 := hupos.ne'
  have hP0 : P ≠ 0 := hP.ne'
  have e1 : C ^ 2 * S / P * (1 / u ^ 2) * (D * B) = C ^ 2 * S * (D * B) / (P * u ^ 2) := by
    field_simp
  rw [e1, le_div_iff₀ (mul_pos hP (pow_pos hupos 2))]
  calc A ^ 2 * (P * u ^ 2) = A ^ 2 * P * u ^ 2 := by ring
    _ ≤ _ := key

theorem summable_moment_ratio (k : ℕ) (hk : 6 ≤ k) :
    Summable (fun n : ℕ => discMoment n ((k : ℝ) / 2 - 2) ^ 2 /
      (((k : ℝ) + 2 * n) ^ 4 * discMoment (2 * n) ((k : ℝ) - 2))) := by
  obtain ⟨C, hC, hAC⟩ := discMoment_half_le' k hk
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = k / 2 - 1 := ⟨_, rfl⟩
  have h2e : k ≤ 2 * e + 3 := by omega
  have hkR : (6 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (-1 : ℝ) < (k : ℝ) - 2 := by linarith
  have hf0 : (0 : ℝ) < ((k - 2).factorial : ℝ) := by positivity
  have hP : 0 < Real.pi * ((k - 2).factorial : ℝ) := by positivity
  have hS : 0 < (k : ℝ) ^ (k - 1) := by positivity
  have hsum : Summable fun n : ℕ =>
      (C ^ 2 * (k : ℝ) ^ (k - 1) / (Real.pi * ((k - 2).factorial : ℝ))) *
        (1 / (((n + 1 : ℕ) : ℝ)) ^ 2) :=
    ((summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2))).mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum
  · have hB := discMoment_pos (2 * n) hk2
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) hB.le)
  · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hBge := discMoment_two_mul_ge k n (by omega)
    have hA := hAC n
    rw [← he] at hA
    have hupos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hAe : discMoment n ((k : ℝ) / 2 - 2) * ((n : ℝ) + 1) ^ e ≤ C := by
      rwa [le_div_iff₀ (pow_pos hupos e)] at hA
    have hnk : (n : ℝ) + k ≤ k * ((n : ℝ) + 1) := by nlinarith
    have hBP : Real.pi * ((k - 2).factorial : ℝ) ≤
        discMoment (2 * n) ((k : ℝ) - 2) * (k : ℝ) ^ (k - 1) * ((n : ℝ) + 1) ^ (k - 1) := by
      rw [div_le_iff₀ (pow_pos (by linarith : (0 : ℝ) < (n : ℝ) + k) _)] at hBge
      calc Real.pi * ((k - 2).factorial : ℝ)
          ≤ discMoment (2 * n) ((k : ℝ) - 2) * ((n : ℝ) + k) ^ (k - 1) := hBge
        _ ≤ discMoment (2 * n) ((k : ℝ) - 2) * (k * ((n : ℝ) + 1)) ^ (k - 1) := by
            have hB0 := (discMoment_pos (2 * n) hk2).le
            have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (n : ℝ) + k) hnk (k - 1)
            exact mul_le_mul_of_nonneg_left this hB0
        _ = discMoment (2 * n) ((k : ℝ) - 2) * (k : ℝ) ^ (k - 1) * ((n : ℝ) + 1) ^ (k - 1) := by
            rw [mul_pow]
            ring
    have hD : ((n : ℝ) + 1) ^ 4 ≤ ((k : ℝ) + 2 * n) ^ 4 :=
      pow_le_pow_left₀ hupos.le (by linarith) 4
    exact aux_ratio (discMoment_nonneg _ _) (discMoment_pos _ hk2) hP hS (by linarith) hAe hBP hD
      (by omega)

end Bounds

end TernaryPeriodPolynomials.Regularity

end
