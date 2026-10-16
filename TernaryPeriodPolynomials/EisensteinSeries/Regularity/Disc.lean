module

public import Mathlib
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.DiscTaylor
public import TernaryPeriodPolynomials.EisensteinSeries.Regularity.DiscMoments

@[expose] public section


/-!
# Weighted Parseval identity and mean value property on the unit disc

For `H` holomorphic on the open unit disc with Taylor coefficients `c n = taylorCoeff H n` and a
weight exponent `a > -1`:

* `lintegral_norm_sq_eq_tsum` (Hilbert space values):
  `∫_D ‖H‖² (1 - |ζ|²)^a = ∑ ‖c n‖² discMoment (2n) a`;
* `lintegral_norm_le_tsum`: `∫_D ‖H‖ (1 - |ζ|²)^a ≤ ∑ ‖c n‖ discMoment n a`;
* `integral_weight_smul_eq`: `∫_D (1 - |ζ|²)^a H = (π / (a + 1)) H 0` whenever the integrand is
  integrable.

The proofs decompose the integral in polar coordinates (`lintegral_ball_polar`), expand the
angular integral of `‖H(r e^{iθ})‖²` through the orthogonality of the characters `e^{inθ}`
(`integral_norm_sq_tsum`, proved by dominated convergence from the finite sums), and integrate
the resulting series termwise in `r`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped Real NNReal ENNReal

namespace TernaryPeriodPolynomials.Regularity

/-- The unit complex number `e^{iθ}`. -/
def ang (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem norm_ang (θ : ℝ) : ‖ang θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

theorem continuous_ang : Continuous ang :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

theorem polarCoord_symm_eq (r θ : ℝ) : Complex.polarCoord.symm (r, θ) = (r : ℂ) * ang θ := by
  simp only [Complex.polarCoord_symm_apply]
  rw [ang, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem norm_polarCoord_symm_of_pos {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ‖Complex.polarCoord.symm (r, θ)‖ = r := by
  rw [norm_polarCoord_symm]
  exact abs_of_pos hr

theorem polarCoord_symm_mem_ball {r : ℝ} (hr0 : 0 < r) (hr : r < 1) (θ : ℝ) :
    Complex.polarCoord.symm (r, θ) ∈ Metric.ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, norm_polarCoord_symm_of_pos hr0]
  exact hr

theorem conj_ang_pow_mul (θ : ℝ) (n m : ℕ) :
    starRingEnd ℂ (ang θ ^ n) * ang θ ^ m = Complex.exp (((m : ℂ) - n) * Complex.I * θ) := by
  have h1 : starRingEnd ℂ (ang θ) = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [ang, ← Complex.exp_conj]
    congr 1
    simp
  rw [map_pow, h1, ang, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

theorem integral_conj_ang_pow_mul (n m : ℕ) :
    ∫ θ in (-π)..π, starRingEnd ℂ (ang θ ^ n) * ang θ ^ m =
      if n = m then ((2 * π : ℝ) : ℂ) else 0 := by
  simp only [conj_ang_pow_mul]
  by_cases h : n = m
  · rw [ite_eq_left h]
    have e : ∀ θ : ℝ, Complex.exp (((m : ℂ) - n) * Complex.I * θ) = 1 := fun θ => by
      rw [h]
      simp
    simp only [e, intervalIntegral.integral_const]
    rw [Complex.real_smul]
    push_cast
    ring
  · rw [ite_eq_right h]
    have hc : ((m : ℂ) - n) * Complex.I ≠ 0 := by
      refine mul_ne_zero (sub_ne_zero.2 ?_) Complex.I_ne_zero
      exact_mod_cast Ne.symm h
    rw [integral_exp_mul_complex hc]
    have hexp : Complex.exp (((m : ℂ) - n) * Complex.I * (π : ℂ)) =
        Complex.exp (((m : ℂ) - n) * Complex.I * ((-π : ℝ) : ℂ)) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨(m : ℤ) - n, ?_⟩
      push_cast
      ring
    rw [hexp, sub_self, zero_div]

theorem integral_Ioo_eq_interval' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ}
    (hab : a ≤ b) (f : ℝ → F) : ∫ x in Ioo a b, f x = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]

theorem lintegral_Ioo_eq_ofReal_interval {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ θ, 0 ≤ f θ) :
    ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (f θ) = ENNReal.ofReal (∫ θ in (-π)..π, f θ) := by
  have hle : -π ≤ π := by linarith [Real.pi_pos]
  have hint : IntegrableOn f (Ioo (-π) π) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1
      (hf.intervalIntegrable _ _)).mono_set Ioo_subset_Ioc_self
  rw [← integral_Ioo_eq_interval' hle, ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall hnn)]

theorem summable_sq_of_summable {x : ℕ → ℝ} (hx0 : ∀ n, 0 ≤ x n) (hx : Summable x) :
    Summable fun n => x n ^ 2 := by
  have hbd : ∀ n, x n ≤ ∑' k, x k := fun n => by
    have := sum_le_hasSum {n} (fun i _ => hx0 i) hx.hasSum
    simpa using this
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) (hx.mul_left (∑' k, x k))
  rw [sq]
  exact mul_le_mul_of_nonneg_right (hbd n) (hx0 n)

section Angular

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_self_eq_ofReal_norm_sq (x : E) : inner ℂ x x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  have h : ((‖x‖ : ℝ) : ℂ) ^ 2 = inner ℂ x x := (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x).symm
  rw [Complex.ofReal_pow]
  exact h.symm

theorem integral_norm_sq_finite_sum (b : ℕ → E) (N : ℕ) :
    ∫ θ in (-π)..π, ‖∑ n ∈ Finset.range N, ang θ ^ n • b n‖ ^ 2 =
      2 * π * ∑ n ∈ Finset.range N, ‖b n‖ ^ 2 := by
  have key : ∀ θ : ℝ, ((‖∑ n ∈ Finset.range N, ang θ ^ n • b n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        (starRingEnd ℂ (ang θ ^ n) * ang θ ^ m) * inner ℂ (b n) (b m) := by
    intro θ
    rw [← inner_self_eq_ofReal_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [inner_smul_left, inner_smul_right]
    ring
  have hcont : ∀ n m : ℕ, Continuous fun θ : ℝ =>
      (starRingEnd ℂ (ang θ ^ n) * ang θ ^ m) * inner ℂ (b n) (b m) := fun n m =>
    ((Complex.continuous_conj.comp (continuous_ang.pow n)).mul (continuous_ang.pow m)).mul
      continuous_const
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  calc ∫ θ in (-π)..π, ((‖∑ n ∈ Finset.range N, ang θ ^ n • b n‖ ^ 2 : ℝ) : ℂ)
      = ∫ θ in (-π)..π, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (starRingEnd ℂ (ang θ ^ n) * ang θ ^ m) * inner ℂ (b n) (b m) :=
        intervalIntegral.integral_congr fun θ _ => key θ
    _ = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          ∫ θ in (-π)..π, (starRingEnd ℂ (ang θ ^ n) * ang θ ^ m) * inner ℂ (b n) (b m) := by
        rw [intervalIntegral.integral_finsetSum (fun n _ =>
          (continuous_finsetSum _ fun m _ => hcont n m).intervalIntegrable _ _)]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [intervalIntegral.integral_finsetSum (fun m _ => (hcont n m).intervalIntegrable _ _)]
    _ = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
          (if n = m then ((2 * π : ℝ) : ℂ) else 0) * inner ℂ (b n) (b m) := by
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
        rw [intervalIntegral.integral_mul_const, integral_conj_ang_pow_mul]
    _ = ∑ n ∈ Finset.range N, ((2 * π * ‖b n‖ ^ 2 : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq, ite_eq_left hn]
        rw [inner_self_eq_ofReal_norm_sq]
        exact (Complex.ofReal_mul _ _).symm
    _ = ((2 * π * ∑ n ∈ Finset.range N, ‖b n‖ ^ 2 : ℝ) : ℂ) := by
        rw [← Complex.ofReal_sum, ← Finset.mul_sum]

theorem integral_norm_sq_tsum [CompleteSpace E] {b : ℕ → E} (hb : Summable fun n => ‖b n‖) :
    ∫ θ in (-π)..π, ‖∑' n, ang θ ^ n • b n‖ ^ 2 = 2 * π * ∑' n, ‖b n‖ ^ 2 := by
  have hterm : ∀ (θ : ℝ) (n : ℕ), ‖ang θ ^ n • b n‖ = ‖b n‖ := fun θ n => by
    rw [norm_smul, norm_pow, norm_ang, one_pow, one_mul]
  have hsum : ∀ θ : ℝ, Summable fun n => ang θ ^ n • b n := fun θ => by
    refine Summable.of_norm ?_
    exact hb.congr fun n => (hterm θ n).symm
  have hts : ∀ θ : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, ang θ ^ n • b n) atTop
      (𝓝 (∑' n, ang θ ^ n • b n)) := fun θ => (hsum θ).hasSum.tendsto_sum_nat
  have hnorm_le : ∀ (θ : ℝ) (N : ℕ), ‖∑ n ∈ Finset.range N, ang θ ^ n • b n‖ ≤ ∑' n, ‖b n‖ := by
    intro θ N
    calc ‖∑ n ∈ Finset.range N, ang θ ^ n • b n‖
        ≤ ∑ n ∈ Finset.range N, ‖ang θ ^ n • b n‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.range N, ‖b n‖ := Finset.sum_congr rfl fun n _ => hterm θ n
      _ ≤ ∑' n, ‖b n‖ := sum_le_hasSum _ (fun n _ => norm_nonneg _) hb.hasSum
  have hmeas : ∀ N : ℕ, AEStronglyMeasurable
      (fun θ : ℝ => ‖∑ n ∈ Finset.range N, ang θ ^ n • b n‖ ^ 2)
      (volume.restrict (Set.uIoc (-π) π)) :=
    fun N => ((continuous_finsetSum _ fun n _ =>
      (continuous_ang.pow n).smul continuous_const).norm.pow 2).aestronglyMeasurable
  have hlim : Tendsto (fun N : ℕ => ∫ θ in (-π)..π, ‖∑ n ∈ Finset.range N, ang θ ^ n • b n‖ ^ 2)
      atTop (𝓝 (∫ θ in (-π)..π, ‖∑' n, ang θ ^ n • b n‖ ^ 2)) :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (∑' n, ‖b n‖) ^ 2)
      (Filter.Eventually.of_forall hmeas)
      (Filter.Eventually.of_forall fun N => Filter.Eventually.of_forall fun θ _ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hnorm_le θ N) 2)
      ((continuous_const : Continuous fun _ : ℝ => (∑' n, ‖b n‖) ^ 2).intervalIntegrable _ _)
      (Filter.Eventually.of_forall fun θ _ => ((hts θ).norm).pow 2)
  have hlim' : Tendsto (fun N : ℕ => 2 * π * ∑ n ∈ Finset.range N, ‖b n‖ ^ 2) atTop
      (𝓝 (∫ θ in (-π)..π, ‖∑' n, ang θ ^ n • b n‖ ^ 2)) :=
    hlim.congr fun N => integral_norm_sq_finite_sum b N
  have hsq : Summable fun n => ‖b n‖ ^ 2 := summable_sq_of_summable (fun n => norm_nonneg _) hb
  exact tendsto_nhds_unique hlim' (hsq.hasSum.tendsto_sum_nat.const_mul (2 * π))

end Angular


section Circle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem norm_ang_smul_pow (θ r : ℝ) (hr : 0 ≤ r) (n : ℕ) (x : E) :
    ‖ang θ ^ n • ((r : ℂ) ^ n • x)‖ = ‖x‖ * r ^ n := by
  rw [norm_smul, norm_smul, norm_pow, norm_pow, norm_ang, Complex.norm_real,
    Real.norm_of_nonneg hr]
  ring

theorem summable_circle_norm {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1)) {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1) (θ : ℝ) :
    Summable fun n => ‖ang θ ^ n • ((r : ℂ) ^ n • taylorCoeff H n)‖ := by
  refine (summable_norm_taylorCoeff hH hr0.le hr).congr fun n => ?_
  rw [norm_ang_smul_pow θ r hr0.le]

theorem circle_hasSum {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1)) {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1) (θ : ℝ) :
    HasSum (fun n => ang θ ^ n • ((r : ℂ) ^ n • taylorCoeff H n))
      (H (Complex.polarCoord.symm (r, θ))) := by
  have hnorm : ‖(r : ℂ) * ang θ‖ < 1 := by
    rw [norm_mul, Complex.norm_real, norm_ang, Real.norm_of_nonneg hr0.le, mul_one]
    exact hr
  have h := hasSum_taylorCoeff hH hnorm
  have e : (fun n : ℕ => ang θ ^ n • ((r : ℂ) ^ n • taylorCoeff H n)) =
      fun n => ((r : ℂ) * ang θ) ^ n • taylorCoeff H n := by
    funext n
    rw [smul_smul, mul_pow, mul_comm]
  rw [e, polarCoord_symm_eq]
  exact h

omit [CompleteSpace E] in
theorem continuous_circle {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1)) {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1) : Continuous fun θ : ℝ => H (Complex.polarCoord.symm (r, θ)) := by
  have hc : Continuous fun θ : ℝ => Complex.polarCoord.symm (r, θ) := by
    have e : (fun θ : ℝ => Complex.polarCoord.symm (r, θ)) = fun θ => (r : ℂ) * ang θ :=
      funext (polarCoord_symm_eq r)
    rw [e]
    exact continuous_const.mul continuous_ang
  exact hH.continuousOn.comp_continuous hc (polarCoord_symm_mem_ball hr0 hr)

/-- The mean value property on the circle `|ζ| = r` in the angular parametrisation. -/
theorem integral_circle_eq {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1)) {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1) :
    ∫ θ in (-π)..π, H (Complex.polarCoord.symm (r, θ)) = (2 * π) • H 0 := by
  have hcl : DiffContOnCl ℂ H (Metric.ball 0 |r|) := by
    refine DifferentiableOn.diffContOnCl (hH.mono ?_)
    refine Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball ?_)
    rw [abs_of_pos hr0]
    exact hr
  have hav := hcl.circleAverage
  rw [Real.circleAverage] at hav
  have hfun : ∀ θ : ℝ, H (Complex.polarCoord.symm (r, θ)) = H (circleMap 0 r θ) := fun θ => by
    rw [polarCoord_symm_eq]
    simp [circleMap, ang]
  simp_rw [hfun]
  have hper : Function.Periodic (fun θ => H (circleMap 0 r θ)) (2 * π) :=
    (periodic_circleMap 0 r).comp H
  have hshift : ∫ θ in (-π)..π, H (circleMap 0 r θ) =
      ∫ θ in (0 : ℝ)..2 * π, H (circleMap 0 r θ) := by
    have := hper.intervalIntegral_add_eq (-π) 0
    rw [show -π + 2 * π = π by ring, zero_add] at this
    exact this
  rw [hshift, ← hav, smul_inv_smul₀ (by positivity)]

end Circle

section Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem integral_norm_sq_circle {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1)) {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1) :
    ∫ θ in (-π)..π, ‖H (Complex.polarCoord.symm (r, θ))‖ ^ 2 =
      2 * π * ∑' n, (‖taylorCoeff H n‖ * r ^ n) ^ 2 := by
  have hb : Summable fun n => ‖(r : ℂ) ^ n • taylorCoeff H n‖ := by
    refine (summable_norm_taylorCoeff hH hr0.le hr).congr fun n => ?_
    rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le, mul_comm]
  have hfun : ∀ θ : ℝ, H (Complex.polarCoord.symm (r, θ)) =
      ∑' n, ang θ ^ n • ((r : ℂ) ^ n • taylorCoeff H n) := fun θ =>
    (circle_hasSum hH hr0 hr θ).tsum_eq.symm
  simp_rw [hfun]
  rw [integral_norm_sq_tsum hb]
  congr 1
  refine tsum_congr fun n => ?_
  rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le, mul_comm]

/-- **Weighted Parseval identity** on the unit disc:
`∫_D ‖H ζ‖² (1 - |ζ|²)^a dA = ∑ ‖c n‖² ∫_D |ζ|^(2n) (1 - |ζ|²)^a dA`. -/
theorem lintegral_norm_sq_eq_tsum {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    (a : ℝ) (ha : -1 < a) :
    ∫⁻ ζ in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (‖H ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ a) =
      ∑' n, ENNReal.ofReal (‖taylorCoeff H n‖ ^ 2 * discMoment (2 * n) a) := by
  have hcont : ContinuousOn
      (fun ζ : ℂ => ENNReal.ofReal (‖H ζ‖ ^ 2 * (1 - ‖ζ‖ ^ 2) ^ a)) (Metric.ball 0 1) := by
    refine ENNReal.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.mul (hH.continuousOn.norm.pow 2) ?_
    refine ContinuousOn.rpow_const (continuous_const.sub (continuous_norm.pow 2)).continuousOn ?_
    intro ζ hζ
    have h := mem_ball_zero_iff.1 hζ
    have h1 : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
    exact Or.inl h1.ne'
  rw [lintegral_ball_polar hcont]
  have hterm : ∀ r ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal r * ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal (‖H (Complex.polarCoord.symm (r, θ))‖ ^ 2 *
        (1 - ‖Complex.polarCoord.symm (r, θ)‖ ^ 2) ^ a) =
      ∑' n, ENNReal.ofReal (2 * π * ‖taylorCoeff H n‖ ^ 2) *
        ENNReal.ofReal (r ^ (2 * n + 1) * (1 - r ^ 2) ^ a) := by
    intro r hr
    have hr0 : 0 < r := hr.1
    simp only [norm_polarCoord_symm_of_pos hr0]
    have hcts : Continuous fun θ : ℝ => ‖H (Complex.polarCoord.symm (r, θ))‖ ^ 2 :=
      (continuous_circle hH hr0 hr.2).norm.pow 2
    have e1 : ∀ θ : ℝ, ENNReal.ofReal (‖H (Complex.polarCoord.symm (r, θ))‖ ^ 2 *
        (1 - r ^ 2) ^ a) = ENNReal.ofReal (‖H (Complex.polarCoord.symm (r, θ))‖ ^ 2) *
          ENNReal.ofReal ((1 - r ^ 2) ^ a) := fun θ => ENNReal.ofReal_mul (sq_nonneg _)
    simp_rw [e1]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      lintegral_Ioo_eq_ofReal_interval hcts (fun θ => sq_nonneg _),
      integral_norm_sq_circle hH hr0 hr.2]
    have hsq : Summable fun n => (‖taylorCoeff H n‖ * r ^ n) ^ 2 :=
      summable_sq_of_summable (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr0.le n))
        (summable_norm_taylorCoeff hH hr0.le hr.2)
    have e2 : ENNReal.ofReal (2 * π * ∑' n, (‖taylorCoeff H n‖ * r ^ n) ^ 2) =
        ∑' n, ENNReal.ofReal (2 * π * (‖taylorCoeff H n‖ * r ^ n) ^ 2) := by
      have hnn : ∀ n : ℕ, 0 ≤ 2 * π * (‖taylorCoeff H n‖ * r ^ n) ^ 2 := fun n => by positivity
      rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg hnn (hsq.mul_left _)]
    rw [e2, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * π * (‖taylorCoeff H n‖ * r ^ n) ^ 2),
      ← ENNReal.ofReal_mul hr0.le,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * π * ‖taylorCoeff H n‖ ^ 2)]
    congr 1
    ring
  refine (setLIntegral_congr_fun measurableSet_Ioo hterm).trans ?_
  have hm : ∀ n : ℕ, Measurable fun r : ℝ => r ^ (2 * n + 1) * (1 - r ^ 2) ^ a := fun n => by
    fun_prop
  have hae : ∀ n : ℕ, AEMeasurable (fun r : ℝ => ENNReal.ofReal (2 * π * ‖taylorCoeff H n‖ ^ 2) *
      ENNReal.ofReal (r ^ (2 * n + 1) * (1 - r ^ 2) ^ a)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    fun n => (measurable_const.mul (ENNReal.measurable_ofReal.comp (hm n))).aemeasurable
  rw [lintegral_tsum hae]
  refine tsum_congr fun n => ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_rad_eq (2 * n) ha,
    discMoment_eq (2 * n) a ha,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π * ‖taylorCoeff H n‖ ^ 2)]
  congr 1
  ring

end Weighted

section L1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Weighted `L¹` bound** on the unit disc:
`∫_D ‖H ζ‖ (1 - |ζ|²)^a dA ≤ ∑ ‖c n‖ ∫_D |ζ|^n (1 - |ζ|²)^a dA`. -/
theorem lintegral_norm_le_tsum {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1))
    (a : ℝ) (ha : -1 < a) :
    ∫⁻ ζ in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (‖H ζ‖ * (1 - ‖ζ‖ ^ 2) ^ a) ≤
      ∑' n, ENNReal.ofReal (‖taylorCoeff H n‖ * discMoment n a) := by
  have hcont : ContinuousOn
      (fun ζ : ℂ => ENNReal.ofReal (‖H ζ‖ * (1 - ‖ζ‖ ^ 2) ^ a)) (Metric.ball 0 1) := by
    refine ENNReal.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.mul hH.continuousOn.norm ?_
    refine ContinuousOn.rpow_const (continuous_const.sub (continuous_norm.pow 2)).continuousOn ?_
    intro ζ hζ
    have h := mem_ball_zero_iff.1 hζ
    have h1 : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
    exact Or.inl h1.ne'
  rw [lintegral_ball_polar hcont]
  have hterm : ∀ r ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal r * ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal (‖H (Complex.polarCoord.symm (r, θ))‖ *
        (1 - ‖Complex.polarCoord.symm (r, θ)‖ ^ 2) ^ a) ≤
      ∑' n, ENNReal.ofReal (2 * π * ‖taylorCoeff H n‖) *
        ENNReal.ofReal (r ^ (n + 1) * (1 - r ^ 2) ^ a) := by
    intro r hr
    have hr0 : 0 < r := hr.1
    have hw : 0 ≤ (1 - r ^ 2) ^ a := Real.rpow_nonneg (by nlinarith [hr.1, hr.2]) _
    simp only [norm_polarCoord_symm_of_pos hr0]
    have hx : ∀ n : ℕ, 0 ≤ ‖taylorCoeff H n‖ * r ^ n := fun n =>
      mul_nonneg (norm_nonneg _) (pow_nonneg hr0.le n)
    have hb0 := summable_norm_taylorCoeff hH hr0.le hr.2
    have hT : 0 ≤ ∑' n, ‖taylorCoeff H n‖ * r ^ n := tsum_nonneg hx
    have hle : ∀ θ : ℝ, ‖H (Complex.polarCoord.symm (r, θ))‖ ≤
        ∑' n, ‖taylorCoeff H n‖ * r ^ n := fun θ => by
      rw [← (circle_hasSum hH hr0 hr.2 θ).tsum_eq]
      calc ‖∑' n, ang θ ^ n • ((r : ℂ) ^ n • taylorCoeff H n)‖
          ≤ ∑' n, ‖ang θ ^ n • ((r : ℂ) ^ n • taylorCoeff H n)‖ :=
            norm_tsum_le_tsum_norm (summable_circle_norm hH hr0 hr.2 θ)
        _ = ∑' n, ‖taylorCoeff H n‖ * r ^ n :=
            tsum_congr fun n => norm_ang_smul_pow θ r hr0.le n _
    have hinner : ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal
          (‖H (Complex.polarCoord.symm (r, θ))‖ * (1 - r ^ 2) ^ a) ≤
        ENNReal.ofReal ((∑' n, ‖taylorCoeff H n‖ * r ^ n) * (1 - r ^ 2) ^ a) *
          ENNReal.ofReal (2 * π) := by
      calc _ ≤ ∫⁻ θ in Ioo (-π) π,
            ENNReal.ofReal ((∑' n, ‖taylorCoeff H n‖ * r ^ n) * (1 - r ^ 2) ^ a) :=
            lintegral_mono fun θ => ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (hle θ) hw)
        _ = _ := by
            rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo,
              show π - -π = 2 * π by ring]
    calc _ ≤ ENNReal.ofReal r * (ENNReal.ofReal ((∑' n, ‖taylorCoeff H n‖ * r ^ n) *
          (1 - r ^ 2) ^ a) * ENNReal.ofReal (2 * π)) := mul_le_mul' le_rfl hinner
      _ = _ := by
          rw [ENNReal.ofReal_mul hT, ENNReal.ofReal_tsum_of_nonneg hx hb0,
            ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun n => ?_
          rw [← ENNReal.ofReal_mul (hx n), ← ENNReal.ofReal_mul (mul_nonneg (hx n) hw),
            ← ENNReal.ofReal_mul hr0.le,
            ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * π * ‖taylorCoeff H n‖)]
          congr 1
          ring
  refine (setLIntegral_mono' measurableSet_Ioo hterm).trans (le_of_eq ?_)
  have hm : ∀ n : ℕ, Measurable fun r : ℝ => r ^ (n + 1) * (1 - r ^ 2) ^ a := fun n => by
    fun_prop
  have hae : ∀ n : ℕ, AEMeasurable (fun r : ℝ => ENNReal.ofReal (2 * π * ‖taylorCoeff H n‖) *
      ENNReal.ofReal (r ^ (n + 1) * (1 - r ^ 2) ^ a)) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    fun n => (measurable_const.mul (ENNReal.measurable_ofReal.comp (hm n))).aemeasurable
  rw [lintegral_tsum hae]
  refine tsum_congr fun n => ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_rad_eq n ha,
    discMoment_eq n a ha,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * π * ‖taylorCoeff H n‖)]
  congr 1
  ring

end L1

section MeanValue

/-- Polar decomposition of the Bochner integral of an integrable continuous function over the
unit disc. -/
theorem integral_ball_polar {g : ℂ → ℂ} (hg : ContinuousOn g (Metric.ball 0 1))
    (hint : IntegrableOn g (Metric.ball 0 1)) :
    ∫ ζ in Metric.ball (0 : ℂ) 1, g ζ =
      ∫ r in Ioo (0 : ℝ) 1, r • ∫ θ in Ioo (-π) π, g (Complex.polarCoord.symm (r, θ)) := by
  classical
  have hs : MeasurableSet (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball.measurableSet
  have hmeas : Measurable ((Metric.ball (0 : ℂ) 1).indicator g) := by
    have e : (Metric.ball (0 : ℂ) 1).indicator g =
        (Metric.ball (0 : ℂ) 1).piecewise g (fun _ => 0) := by
      funext x
      by_cases hx : x ∈ Metric.ball (0 : ℂ) 1 <;>
        simp only [Set.indicator_apply, Set.piecewise, hx, ↓reduceIte]
    rw [e]
    exact hg.measurable_piecewise continuousOn_const hs
  have htarget : (volume : Measure (ℝ × ℝ)).restrict polarCoord.target =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π)) := by
    rw [polarCoord_target, Measure.prod_restrict, Measure.volume_eq_prod]
  have h2 := Complex.integral_comp_polarCoord_symm ((Metric.ball (0 : ℂ) 1).indicator g)
  have hint2 : Integrable (fun p : ℝ × ℝ => p.1 •
      (Metric.ball (0 : ℂ) 1).indicator g (Complex.polarCoord.symm p))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
    rw [← htarget]
    refine ⟨(measurable_fst.smul (hmeas.comp measurable_polarCoord_symm)).aestronglyMeasurable,
      ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hl := Complex.lintegral_comp_polarCoord_symm
      (fun ζ => ENNReal.ofReal ‖(Metric.ball (0 : ℂ) 1).indicator g ζ‖)
    simp only [smul_eq_mul] at hl
    have hcongr : ∫⁻ p in polarCoord.target, ENNReal.ofReal
          ‖p.1 • (Metric.ball (0 : ℂ) 1).indicator g (Complex.polarCoord.symm p)‖ =
        ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 *
          ENNReal.ofReal ‖(Metric.ball (0 : ℂ) 1).indicator g (Complex.polarCoord.symm p)‖ := by
      refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)
      rw [polarCoord_target] at hp
      have hp0 : 0 < p.1 := hp.1
      show ENNReal.ofReal ‖p.1 • (Metric.ball (0 : ℂ) 1).indicator g (Complex.polarCoord.symm p)‖ =
        ENNReal.ofReal p.1 *
          ENNReal.ofReal ‖(Metric.ball (0 : ℂ) 1).indicator g (Complex.polarCoord.symm p)‖
      rw [norm_smul, Real.norm_of_nonneg hp0.le, ENNReal.ofReal_mul hp0.le]
    refine lt_of_eq_of_lt hcongr (lt_of_eq_of_lt hl ?_)
    have hind : ∀ ζ : ℂ, ENNReal.ofReal ‖(Metric.ball (0 : ℂ) 1).indicator g ζ‖ =
        (Metric.ball (0 : ℂ) 1).indicator (fun ζ => ENNReal.ofReal ‖g ζ‖) ζ := fun ζ => by
      by_cases hζ : ζ ∈ Metric.ball (0 : ℂ) 1
      · rw [Set.indicator_apply, Set.indicator_apply, ite_eq_left hζ, ite_eq_left hζ]
      · rw [Set.indicator_apply, Set.indicator_apply, ite_eq_right hζ, ite_eq_right hζ, norm_zero,
          ENNReal.ofReal_zero]
    simp_rw [hind]
    rw [lintegral_indicator hs]
    exact (hasFiniteIntegral_iff_norm g).1 (Integrable.hasFiniteIntegral hint)
  rw [← integral_indicator hs, ← h2, htarget, integral_prod _ hint2]
  have h3 : ∀ r ∈ Ioi (0 : ℝ),
      (∫ θ in Ioo (-π) π, r • (Metric.ball (0 : ℂ) 1).indicator g
        (Complex.polarCoord.symm (r, θ))) =
      (Iio (1 : ℝ)).indicator (fun r => r • ∫ θ in Ioo (-π) π,
        g (Complex.polarCoord.symm (r, θ))) r := by
    intro r hr
    have hr0 : (0 : ℝ) < r := hr
    by_cases h1 : r < 1
    · have hmem : ∀ θ : ℝ, Complex.polarCoord.symm (r, θ) ∈ Metric.ball (0 : ℂ) 1 :=
        polarCoord_symm_mem_ball hr0 h1
      have hind : ∀ θ : ℝ, (Metric.ball (0 : ℂ) 1).indicator g (Complex.polarCoord.symm (r, θ)) =
          g (Complex.polarCoord.symm (r, θ)) := fun θ => Set.indicator_of_mem (hmem θ) g
      rw [Set.indicator_of_mem (show r ∈ Iio (1 : ℝ) from h1)]
      simp only [hind]
      exact integral_smul r _
    · have hmem : ∀ θ : ℝ, Complex.polarCoord.symm (r, θ) ∉ Metric.ball (0 : ℂ) 1 :=
        fun θ hθ => by
          rw [mem_ball_zero_iff, norm_polarCoord_symm_of_pos hr0] at hθ
          exact h1 hθ
      have hind : ∀ θ : ℝ, (Metric.ball (0 : ℂ) 1).indicator g (Complex.polarCoord.symm (r, θ)) =
          0 := fun θ => by
        rw [Set.indicator_apply, ite_eq_right (hmem θ)]
      have hnot : r ∉ Iio (1 : ℝ) := h1
      rw [Set.indicator_apply, ite_eq_right hnot]
      simp only [hind, smul_zero, integral_zero]
  calc _ = ∫ r in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator (fun r => r • ∫ θ in Ioo (-π) π,
        g (Complex.polarCoord.symm (r, θ))) r := setIntegral_congr_fun measurableSet_Ioi h3
    _ = _ := by
        rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          Iio_inter_Ioi]

/-- The weighted mean value property for scalar-valued holomorphic functions. -/
theorem integral_weight_smul_eq_complex {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1)) (a : ℝ) (ha : -1 < a)
    (hint : IntegrableOn (fun ζ : ℂ => (1 - ‖ζ‖ ^ 2) ^ a • h ζ) (Metric.ball 0 1)) :
    ∫ ζ in Metric.ball (0 : ℂ) 1, (1 - ‖ζ‖ ^ 2) ^ a • h ζ = (π / (a + 1)) • h 0 := by
  have hle : -π ≤ π := by linarith [Real.pi_pos]
  have ha1 : a + 1 ≠ 0 := (show (0 : ℝ) < a + 1 by linarith).ne'
  have hw : ContinuousOn (fun ζ : ℂ => (1 - ‖ζ‖ ^ 2) ^ a) (Metric.ball 0 1) := by
    refine ContinuousOn.rpow_const (continuous_const.sub (continuous_norm.pow 2)).continuousOn ?_
    intro ζ hζ
    have h1 := mem_ball_zero_iff.1 hζ
    have h2 : 0 < 1 - ‖ζ‖ ^ 2 := by nlinarith [norm_nonneg ζ]
    exact Or.inl h2.ne'
  have hcont : ContinuousOn (fun ζ : ℂ => (1 - ‖ζ‖ ^ 2) ^ a • h ζ) (Metric.ball 0 1) :=
    hw.smul hh.continuousOn
  rw [integral_ball_polar hcont hint]
  have hr : ∀ r ∈ Ioo (0 : ℝ) 1,
      (r • ∫ θ in Ioo (-π) π, (1 - ‖Complex.polarCoord.symm (r, θ)‖ ^ 2) ^ a •
        h (Complex.polarCoord.symm (r, θ))) = (2 * π * (r * (1 - r ^ 2) ^ a)) • h 0 := by
    intro r hr
    have hr0 : 0 < r := hr.1
    simp only [norm_polarCoord_symm_of_pos hr0]
    rw [integral_smul, integral_Ioo_eq_interval' hle, integral_circle_eq hh hr0 hr.2,
      smul_smul, smul_smul]
    congr 1
    ring
  refine (setIntegral_congr_fun measurableSet_Ioo hr).trans ?_
  rw [integral_smul_const, integral_const_mul, integral_Ioo_eq_interval' zero_le_one,
    integral_rad0 ha]
  congr 1
  field_simp

/-- **Weighted mean value property** on the unit disc: if `H` is holomorphic on the disc and
`(1 - |ζ|²)^a H` is integrable, then `∫_D (1 - |ζ|²)^a H dA = (π / (a + 1)) H 0`. -/
theorem integral_weight_smul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {H : ℂ → E} (hH : DifferentiableOn ℂ H (Metric.ball 0 1)) (a : ℝ)
    (ha : -1 < a)
    (hint : IntegrableOn (fun ζ : ℂ => (1 - ‖ζ‖ ^ 2) ^ a • H ζ) (Metric.ball 0 1)) :
    ∫ ζ in Metric.ball (0 : ℂ) 1, (1 - ‖ζ‖ ^ 2) ^ a • H ζ = (π / (a + 1)) • H 0 := by
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ => ?_
  have e : ∀ ζ : ℂ, ℓ ((1 - ‖ζ‖ ^ 2) ^ a • H ζ) = (1 - ‖ζ‖ ^ 2) ^ a • ℓ (H ζ) := fun ζ =>
    ContinuousLinearMap.map_smul_of_tower ℓ _ _
  have h1 : IntegrableOn (fun ζ : ℂ => ℓ ((1 - ‖ζ‖ ^ 2) ^ a • H ζ)) (Metric.ball 0 1) :=
    ContinuousLinearMap.integrable_comp ℓ hint
  have hint' : IntegrableOn (fun ζ : ℂ => (1 - ‖ζ‖ ^ 2) ^ a • ℓ (H ζ)) (Metric.ball 0 1) :=
    h1.congr_fun (fun ζ _ => e ζ) Metric.isOpen_ball.measurableSet
  have hℓH : DifferentiableOn ℂ (fun ζ => ℓ (H ζ)) (Metric.ball 0 1) :=
    (ContinuousLinearMap.differentiable ℓ).comp_differentiableOn hH
  have key := integral_weight_smul_eq_complex hℓH a ha hint'
  rw [← ContinuousLinearMap.integral_comp_comm ℓ hint]
  simp only [e]
  rw [key, ContinuousLinearMap.map_smul_of_tower ℓ]

end MeanValue

end TernaryPeriodPolynomials.Regularity

end
