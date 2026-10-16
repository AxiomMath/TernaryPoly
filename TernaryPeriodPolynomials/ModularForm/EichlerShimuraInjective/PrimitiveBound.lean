module

public import Mathlib

@[expose] public section


/-!
# Boundedness of primitives of exponentially decaying functions

`prim_bound`: a primitive of `h(z) z^j` with `‖h‖ ≤ C e^{-c Im z}` is bounded on `Im z ≥ A`, `|Re z| ≤ 1/2`.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open Filter Topology MeasureTheory intervalIntegral Set

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

theorem poly_exp_le (j : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ j * Real.exp (-c * t) ≤ M * Real.exp (-(c / 2) * t) := by
  refine ⟨(2 / c) ^ j * j.factorial * Real.exp (c / 2), by positivity, fun t ht => ?_⟩
  have hx : 0 ≤ c * (1 + t) / 2 := by positivity
  have h := Real.pow_div_factorial_le_exp (c * (1 + t) / 2) hx j
  have hfac : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  rw [div_le_iff₀ hfac] at h
  have h2 : (1 + t) ^ j = (2 / c) ^ j * (c * (1 + t) / 2) ^ j := by
    rw [← mul_pow]; congr 1; field_simp
  have h3 : Real.exp (c * (1 + t) / 2) = Real.exp (c / 2) * Real.exp ((c / 2) * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (-c * t) = Real.exp (-(c / 2) * t) * Real.exp (-((c / 2) * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2, h4]
  calc (2 / c) ^ j * (c * (1 + t) / 2) ^ j * (Real.exp (-(c / 2) * t) * Real.exp (-((c / 2) * t)))
      ≤ (2 / c) ^ j * (Real.exp (c * (1 + t) / 2) * j.factorial) *
          (Real.exp (-(c / 2) * t) * Real.exp (-((c / 2) * t))) := by gcongr
    _ = (2 / c) ^ j * j.factorial * Real.exp (c / 2) * Real.exp (-(c / 2) * t) *
          (Real.exp ((c / 2) * t) * Real.exp (-((c / 2) * t))) := by rw [h3]; ring
    _ = _ := by
      rw [← Real.exp_add]; simp

theorem prim_bound {h G : ℂ → ℂ} (hh : DifferentiableOn ℂ h {z | 0 < z.im}) (j : ℕ)
    (hG : ∀ z : ℂ, 0 < z.im → HasDerivAt G (h z * z ^ j) z)
    {C c A : ℝ} (hc : 0 < c) (hA : 0 < A) (hdec : ∀ z : ℂ, A ≤ z.im → ‖h z‖ ≤ C * Real.exp (-c * z.im)) :
    ∃ K : ℝ, ∀ x : ℝ, |x| ≤ 1 / 2 → ∀ T : ℝ, A ≤ T → ‖G ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤ K := by
  obtain ⟨M, hM0, hM⟩ := poly_exp_le j hc
  have hC : 0 ≤ C := by
    have := hdec (Complex.I * (A : ℂ)) (by simp)
    have h0 := norm_nonneg (h (Complex.I * (A : ℂ)))
    by_contra hneg
    push Not at hneg
    have : C * Real.exp (-c * (Complex.I * (A : ℂ)).im) < 0 := mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
    linarith
  -- continuity of G on the upper half plane
  have hGc : ContinuousOn G {z : ℂ | 0 < z.im} := fun z hz => (hG z hz).continuousAt.continuousWithinAt
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2), ‖G ((x : ℂ) + (A : ℂ) * Complex.I)‖ ≤ K0 := by
    have hcm : ContinuousOn (fun x : ℝ => G ((x : ℂ) + (A : ℂ) * Complex.I)) (Icc (-1 / 2 : ℝ) (1 / 2)) := by
      refine hGc.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (A : ℂ) * Complex.I).continuousOn
        (fun x _ => ?_)
      simpa using hA
    exact isCompact_Icc.exists_bound_of_continuousOn hcm
  refine ⟨K0 + 2 * C * M / c, fun x hx T hT => ?_⟩
  have hx' : x ∈ Icc (-1 / 2 : ℝ) (1 / 2) := ⟨by linarith [(abs_le.mp hx).1], (abs_le.mp hx).2⟩
  set Φ : ℝ → ℂ := fun t => G ((x : ℂ) + (t : ℂ) * Complex.I) with hΦ
  have hΦd : ∀ t : ℝ, 0 < t → HasDerivAt Φ (Complex.I * (h ((x : ℂ) + (t : ℂ) * Complex.I) *
      ((x : ℂ) + (t : ℂ) * Complex.I) ^ j)) t := by
    intro t ht
    have hz : 0 < ((x : ℂ) + (t : ℂ) * Complex.I).im := by simpa using ht
    have hdir : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) Complex.I t := by
      simpa using (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).const_add (x : ℂ)
    have h1 := (hG _ hz).scomp t hdir
    rw [smul_eq_mul] at h1
    exact h1
  have hAT : A ≤ T := hT
  -- derivative bound
  have hbd : ∀ t : ℝ, A ≤ t → ‖Complex.I * (h ((x : ℂ) + (t : ℂ) * Complex.I) *
      ((x : ℂ) + (t : ℂ) * Complex.I) ^ j)‖ ≤ (C * M) * Real.exp (-(c / 2) * t) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hA ht
    have hz : A ≤ ((x : ℂ) + (t : ℂ) * Complex.I).im := by simpa using ht
    have h1 := hdec _ hz
    have hnorm : ‖(x : ℂ) + (t : ℂ) * Complex.I‖ ≤ 1 + t := by
      refine (norm_add_le _ _).trans ?_
      simp only [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
      linarith [(abs_le.mp hx).1, (abs_le.mp hx).2, abs_le.mpr (show -(1/2:ℝ) ≤ x ∧ x ≤ 1/2 from ⟨(abs_le.mp hx).1, (abs_le.mp hx).2⟩)]
    rw [norm_mul, Complex.norm_I, one_mul, norm_mul, norm_pow]
    have h2 : ‖((x : ℂ) + (t : ℂ) * Complex.I) ^ j‖ ≤ (1 + t) ^ j := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hnorm j
    have him : ((x : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [him] at h1
    calc ‖h ((x : ℂ) + (t : ℂ) * Complex.I)‖ * ‖(x : ℂ) + (t : ℂ) * Complex.I‖ ^ j
        ≤ (C * Real.exp (-c * t)) * (1 + t) ^ j := by
          apply mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) hnorm j) (by positivity)
            (le_trans (norm_nonneg _) h1)
      _ = C * ((1 + t) ^ j * Real.exp (-c * t)) := by ring
      _ ≤ C * (M * Real.exp (-(c / 2) * t)) := mul_le_mul_of_nonneg_left (hM t ht0.le) hC
      _ = (C * M) * Real.exp (-(c / 2) * t) := by ring
  have hcont : ContinuousOn (fun t : ℝ => Complex.I * (h ((x : ℂ) + (t : ℂ) * Complex.I) *
      ((x : ℂ) + (t : ℂ) * Complex.I) ^ j)) (uIcc A T) := by
    have hcm : Continuous fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I := by fun_prop
    have hhc : ContinuousOn h {z : ℂ | 0 < z.im} := hh.continuousOn
    have h1 : ContinuousOn (fun t : ℝ => h ((x : ℂ) + (t : ℂ) * Complex.I)) (uIcc A T) :=
      hhc.comp hcm.continuousOn (fun t ht => by
        rw [uIcc_of_le hAT] at ht
        have : 0 < t := lt_of_lt_of_le hA ht.1
        simpa using this)
    exact continuousOn_const.mul (h1.mul (hcm.pow j).continuousOn)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := A) (b := T) (f := Φ)
    (f' := fun t => Complex.I * (h ((x : ℂ) + (t : ℂ) * Complex.I) * ((x : ℂ) + (t : ℂ) * Complex.I) ^ j))
    (fun t ht => by
      rw [uIcc_of_le hAT] at ht
      exact hΦd t (lt_of_lt_of_le hA ht.1)) (hcont.intervalIntegrable)
  have hexp : ∫ t in A..T, (C * M) * Real.exp (-(c / 2) * t) ≤ 2 * C * M / c := by
    have hd : ∀ t ∈ uIcc A T, HasDerivAt (fun t : ℝ => -(2 / c) * (C * M) * Real.exp (-(c / 2) * t))
        ((C * M) * Real.exp (-(c / 2) * t)) t := by
      intro t _
      have := ((hasDerivAt_id t).const_mul (-(c / 2))).exp.const_mul (-(2 / c) * (C * M))
      refine this.congr_deriv ?_
      simp only [id, mul_one]
      field_simp
    have hint : IntervalIntegrable (fun t : ℝ => (C * M) * Real.exp (-(c / 2) * t)) volume A T :=
      (by fun_prop : Continuous fun t : ℝ => (C * M) * Real.exp (-(c / 2) * t)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    have h1 : 0 < Real.exp (-(c / 2) * A) := Real.exp_pos _
    have h2 : 0 < Real.exp (-(c / 2) * T) := Real.exp_pos _
    have h3 : Real.exp (-(c / 2) * A) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr; nlinarith
    have hCM : 0 ≤ C * M := mul_nonneg hC hM0
    have hu : 0 ≤ (2 / c) * (C * M) := by positivity
    have e : 2 * C * M / c = (2 / c) * (C * M) := by ring
    have e2 : ∀ r : ℝ, -(2 / c) * (C * M) * r = -((2 / c) * (C * M) * r) := fun r => by ring
    rw [e, e2, e2]
    nlinarith [mul_nonneg hu h2.le, mul_le_mul_of_nonneg_left h3 hu]
  have hint2 : IntervalIntegrable (fun t : ℝ => (C * M) * Real.exp (-(c / 2) * t)) volume A T :=
    (by fun_prop : Continuous fun t : ℝ => (C * M) * Real.exp (-(c / 2) * t)).intervalIntegrable _ _
  have hn := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hAT
    (Filter.Eventually.of_forall (fun t ht => hbd t ht.1.le)) hint2
  have hTA : ‖Φ T‖ ≤ ‖Φ A‖ + ‖∫ t in A..T, Complex.I * (h ((x : ℂ) + (t : ℂ) * Complex.I) *
      ((x : ℂ) + (t : ℂ) * Complex.I) ^ j)‖ := by
    rw [hFTC]
    calc ‖Φ T‖ = ‖(Φ T - Φ A) + Φ A‖ := by rw [sub_add_cancel]
      _ ≤ ‖Φ T - Φ A‖ + ‖Φ A‖ := norm_add_le _ _
      _ = _ := by rw [add_comm]
  have hA' := hK0 x hx'
  show ‖Φ T‖ ≤ _
  have : ‖Φ A‖ ≤ K0 := hA'
  linarith

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
