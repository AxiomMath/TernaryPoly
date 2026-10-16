module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Form.IdentityAngular
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.MeanValueIntegral

@[expose] public section


/-!
# The base-point form identity, coefficient by coefficient

`norm_sq_entryDiscFn_le`: `‖F(w)‖² ≤ M (4/(1-|w|²))^{n+3}` for the disc function of `h` under the cusp decay
`‖h z‖² (Im z)^{n+3} ≤ M`.  `coeff_norm_sq_le`: hence every polynomial coefficient of the seed's frame coefficient at
`L_{s,t}` satisfies `‖g_m‖² ≤ A r^{-(n+3)}` (using `‖ξ‖² = (r-1)/(r+1)`, so `4/(1-|ξ|⁴) = (r+1)²/r ≤ 4r`), and
`exists_radial_bound_coeff` gives `‖g_m‖ ≤ D r⁻³` on `ℝ²` for `n ≥ 3`.  With the continuity of `g_m` this yields
integrability (`integrable_of_radial_bound`, `polar_integrableOn_of_radial_bound`) and
`base_integral_coeff`: `∫_{ℝ²} g_m = c_∞ h(i) multinomial(m) xiPoly m 0 · (A∧B)(V+Vᵀ, W+Wᵀ)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open Complex MvPolynomial MeasureTheory Set TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
open TernaryPeriodPolynomials.Argument.Statements.RealEntryCoefficient

theorem norm_xiOf_sq (s t : ℝ) :
    ‖xiOf s t‖ ^ 2 = (entryRadius (s, t) - 1) / (entryRadius (s, t) + 1) := by
  have hr := entryRadius_pos' s t
  have hr2 : entryRadius (s, t) ^ 2 = 1 + s ^ 2 + t ^ 2 := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + s ^ 2 + t ^ 2 by positivity)
    unfold entryRadius; exact this
  unfold xiOf
  rw [norm_div, div_pow]
  have hn : ‖(t : ℂ) + I * s‖ ^ 2 = t ^ 2 + s ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hden : ‖(entryRadius (s, t) : ℂ) + 1‖ = entryRadius (s, t) + 1 := by
    have : (entryRadius (s, t) : ℂ) + 1 = ((entryRadius (s, t) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [hn, hden]
  have hr1 : entryRadius (s, t) + 1 ≠ 0 := by linarith
  field_simp
  nlinarith [hr2]

/-- Cayley transform: the imaginary part of `i(1+w)/(1-w)` is `(1-|w|²)/|1-w|²`. -/
theorem cayley_im (w : ℂ) (hw : 1 - w ≠ 0) :
    (Complex.I * (1 + w) / (1 - w)).im = (1 - ‖w‖ ^ 2) / ‖1 - w‖ ^ 2 := by
  rw [Complex.div_im]
  simp [Complex.sq_norm, Complex.normSq_apply]
  have : (1 - w.re) * (1 - w.re) + w.im * w.im ≠ 0 := by
    intro h0
    apply hw
    have h1 : 1 - w.re = 0 := by nlinarith [sq_nonneg (1 - w.re), sq_nonneg w.im]
    have h2 : w.im = 0 := by nlinarith [sq_nonneg (1 - w.re), sq_nonneg w.im]
    apply Complex.ext <;> simp [h1, h2]
  field_simp
  ring


/-- **Decay of the disc function**: `‖F(w)‖² ≤ M (4/(1-|w|²))^{n+3}` if `‖h z‖² (Im z)^{n+3} ≤ M`. -/
theorem norm_sq_entryDiscFn_le (n : ℕ) (h : ℂ → ℂ) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) (w : ℂ) (hw : ‖w‖ < 1) :
    ‖entryDiscFn n h w‖ ^ 2 ≤ M * (4 / (1 - ‖w‖ ^ 2)) ^ (n + 3) := by
  have hne : (1 - w) ≠ 0 := by
    intro h0
    have : w = 1 := by linear_combination -h0
    rw [this, norm_one] at hw
    exact lt_irrefl _ hw
  have hy := cayley_im w hne
  have hypos : 0 < (Complex.I * (1 + w) / (1 - w)).im := cayley_im_pos w hw
  have hden : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have hN : 0 < ‖1 - w‖ := norm_pos_iff.mpr hne
  have hhM := hM _ hypos
  unfold entryDiscFn
  rw [norm_mul, mul_pow, norm_pow, ← pow_mul, mul_comm (n + 3) 2, pow_mul, norm_div, norm_mul]
  simp only [Complex.norm_I, mul_one, Complex.norm_ofNat]
  have hsplit : (2 / ‖1 - w‖) ^ 2 = (4 / (1 - ‖w‖ ^ 2)) * (Complex.I * (1 + w) / (1 - w)).im := by
    rw [hy]; field_simp; ring
  rw [hsplit, mul_pow]
  calc (4 / (1 - ‖w‖ ^ 2)) ^ (n + 3) * (Complex.I * (1 + w) / (1 - w)).im ^ (n + 3) *
        ‖h (Complex.I * (1 + w) / (1 - w))‖ ^ 2
      = (4 / (1 - ‖w‖ ^ 2)) ^ (n + 3) *
          (‖h (Complex.I * (1 + w) / (1 - w))‖ ^ 2 * (Complex.I * (1 + w) / (1 - w)).im ^ (n + 3)) := by ring
    _ ≤ (4 / (1 - ‖w‖ ^ 2)) ^ (n + 3) * M := by gcongr
    _ = M * (4 / (1 - ‖w‖ ^ 2)) ^ (n + 3) := by ring


theorem norm_xiPoly_le (m : Fin 3 →₀ ℕ) (ξ : ℂ) (hξ : ‖ξ‖ ≤ 1) :
    ‖xiPoly m ξ‖ ≤ 2 ^ (m 0 + m 1 + m 2) := by
  unfold xiPoly
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, pow_add, pow_add]
  have h1 : ‖-2 * Complex.I * ξ‖ ≤ 2 := by
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_I]; nlinarith [norm_nonneg ξ]
  have h2 : ‖-(1 + ξ ^ 2)‖ ≤ 2 := by
    rw [norm_neg]
    calc ‖1 + ξ ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖ξ ^ 2‖ := norm_add_le _ _
      _ ≤ 2 := by
        rw [norm_one, norm_pow]
        nlinarith [norm_nonneg ξ]
  have h3 : ‖Complex.I * (1 - ξ ^ 2)‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_I, one_mul]
    calc ‖1 - ξ ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖ξ ^ 2‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_one, norm_pow]
        nlinarith [norm_nonneg ξ]
  gcongr

theorem exists_wedgePoly_bound (p p' : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ C : ℝ, ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ‖wedgePoly p p' ξ‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (wedgePoly_differentiable p p').continuous.continuousOn
  exact ⟨C, fun ξ hξ => hC ξ (by simpa using hξ)⟩


theorem entryRadius_ge_one' (s t : ℝ) : 1 ≤ entryRadius (s, t) := by
  unfold entryRadius
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg s, sq_nonneg t])

/-- **Pointwise decay of a coefficient of the seed's frame coefficient**:
`‖coeff_m ω̃_h(L_{s,t})(V,W)‖² ≤ A · r^{-(n+3)}` away from the origin. -/
theorem coeff_norm_sq_le (n : ℕ) (h : ℂ → ℂ) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) (m : Fin 3 →₀ ℕ)
    (hm : m.sum (fun _ k => k) = n) (V W : Matrix (Fin 3) (Fin 3) ℝ) (C : ℝ)
    (hC : ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ‖wedgePoly (V + V.transpose) (W + W.transpose) ξ‖ ≤ C)
    (s t : ℝ) (hst : (s, t) ≠ (0, 0)) :
    ‖(frameCoefficient (seedForm n h) (entryFrame s t) V W).coeff m‖ ^ 2 ≤
      (((m.multinomial : ℝ) / 2 ^ (n + 4)) ^ 2 * M * 4 ^ (n + 3) * (2 ^ (m 0 + m 1 + m 2)) ^ 2 * C ^ 2) *
        ((entryRadius (s, t)) ^ (n + 3))⁻¹ := by
  have hr := entryRadius_pos' s t
  have hr1 := entryRadius_ge_one' s t
  set r := entryRadius (s, t) with hr_def
  have hξn : ‖xiOf s t‖ < 1 := norm_xiOf_lt_one s t
  have hM0 : 0 ≤ M := by
    have := hM Complex.I (by simp)
    simp at this
    nlinarith [sq_nonneg ‖h Complex.I‖]
  rw [coeff_frameCoefficient_xi n h m hm V W s t hst]
  have hnormeq : ∀ K F P W : ℂ, ‖K * (F * (P * W))‖ ^ 2 =
      ‖K‖ ^ 2 * ‖F‖ ^ 2 * (‖P‖ ^ 2 * ‖W‖ ^ 2) := by
    intros; simp only [norm_mul, mul_pow]; ring
  rw [hnormeq]
  have hK : ‖(m.multinomial : ℂ) * (Complex.I / 2) * ((2 * Complex.I) ^ (n + 3))⁻¹ *
      ((r : ℂ) ^ (n + 3))⁻¹‖ = ((m.multinomial : ℝ) / 2 ^ (n + 4)) * ((r ^ (n + 3))⁻¹) := by
    simp only [norm_mul, norm_inv, norm_pow, Complex.norm_natCast, norm_div, Complex.norm_I,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hr.le]
    rw [pow_succ 2 (n + 3)]
    field_simp
  have hF := norm_sq_entryDiscFn_le n h M hM (xiOf s t ^ 2) (by
    rw [norm_pow]; nlinarith [norm_nonneg (xiOf s t)])
  have hPoly := norm_xiPoly_le m (xiOf s t) hξn.le
  have hW := hC (xiOf s t) hξn.le
  have hnorm2 : ‖xiOf s t ^ 2‖ = (r - 1) / (r + 1) := by
    rw [norm_pow]; exact norm_xiOf_sq s t
  rw [hnorm2] at hF
  have hden : 1 - ((r - 1) / (r + 1)) ^ 2 = 4 * r / (r + 1) ^ 2 := by
    field_simp; ring
  rw [hden] at hF
  have hfrac : 4 / (4 * r / (r + 1) ^ 2) = (r + 1) ^ 2 / r := by field_simp
  rw [hfrac] at hF
  have h4r : (r + 1) ^ 2 / r ≤ 4 * r := by
    rw [div_le_iff₀ hr]; nlinarith
  have hF' : ‖entryDiscFn n h (xiOf s t ^ 2)‖ ^ 2 ≤ M * (4 * r) ^ (n + 3) :=
    hF.trans (by gcongr)
  rw [hK]
  have hP2 : ‖xiPoly m (xiOf s t)‖ ^ 2 ≤ ((2 : ℝ) ^ (m 0 + m 1 + m 2)) ^ 2 := by
    gcongr
  have hW2 : ‖wedgePoly (V + V.transpose) (W + W.transpose) (xiOf s t)‖ ^ 2 ≤ C ^ 2 := by
    have := norm_nonneg (wedgePoly (V + V.transpose) (W + W.transpose) (xiOf s t))
    gcongr
  have hrn : 0 < r ^ (n + 3) := by positivity
  calc ((m.multinomial : ℝ) / 2 ^ (n + 4) * (r ^ (n + 3))⁻¹) ^ 2 *
        ‖entryDiscFn n h (xiOf s t ^ 2)‖ ^ 2 *
        (‖xiPoly m (xiOf s t)‖ ^ 2 *
          ‖wedgePoly (V + V.transpose) (W + W.transpose) (xiOf s t)‖ ^ 2)
      ≤ ((m.multinomial : ℝ) / 2 ^ (n + 4) * (r ^ (n + 3))⁻¹) ^ 2 * (M * (4 * r) ^ (n + 3)) *
        (((2 : ℝ) ^ (m 0 + m 1 + m 2)) ^ 2 * C ^ 2) := by gcongr
    _ = (((m.multinomial : ℝ) / 2 ^ (n + 4)) ^ 2 * M * 4 ^ (n + 3) * (2 ^ (m 0 + m 1 + m 2)) ^ 2 *
          C ^ 2) * ((r ^ (n + 3))⁻¹) := by
        rw [mul_pow, mul_pow]
        field_simp
    

theorem entryCoefficientA_continuous :
    Continuous (fun st : ℝ × ℝ => entryCoefficientA st) := by
  unfold entryCoefficientA
  have h1 : ∀ st : ℝ × ℝ, ((1 + st.1 ^ 2 : ℝ) : ℂ) ≠ 0 := fun st => by
    have : (0 : ℝ) < 1 + st.1 ^ 2 := by positivity
    exact_mod_cast this.ne'
  refine Continuous.div ?_ (by fun_prop) h1
  have hr : Continuous (fun st : ℝ × ℝ => ((st.2 / entryRadius st : ℝ) : ℂ)) := by
    refine Complex.continuous_ofReal.comp ?_
    exact continuous_snd.div entryRadius_continuous (fun st => (entryRadius_pos' st.1 st.2).ne')
  exact (Complex.continuous_ofReal.comp continuous_fst).sub (continuous_const.mul hr)

theorem wedgeSym_dirSym_continuous (p p' : Matrix (Fin 3) (Fin 3) ℝ) :
    Continuous (fun st : ℝ × ℝ => wedgeSym (entryRadius st : ℂ) st.1 st.2 (entryTau st)
      (dirSym p st.1 st.2 (entryTau st)) (dirSym p' st.1 st.2 (entryTau st))) := by
  have hr : Continuous (fun st : ℝ × ℝ => (entryRadius st : ℂ)) :=
    Complex.continuous_ofReal.comp entryRadius_continuous
  have hrne : ∀ st : ℝ × ℝ, (entryRadius st : ℂ) ≠ 0 := fun st => by
    exact_mod_cast (entryRadius_pos' st.1 st.2).ne'
  have hτ : Continuous (fun st : ℝ × ℝ => entryTau st) := entryTau_continuous
  have hs : Continuous (fun st : ℝ × ℝ => (st.1 : ℂ)) := Complex.continuous_ofReal.comp continuous_fst
  have ht : Continuous (fun st : ℝ × ℝ => (st.2 : ℂ)) := Complex.continuous_ofReal.comp continuous_snd
  unfold wedgeSym dirSym
  simp only
  refine Continuous.mul (by fun_prop) ?_
  refine Continuous.sub (Continuous.sub ?_ ?_) ?_
  · exact Continuous.div (by fun_prop) (by fun_prop) (fun st => pow_ne_zero 2 (hrne st))
  · exact Continuous.div (by fun_prop) (by fun_prop) (fun st => pow_ne_zero 4 (hrne st))
  · exact Continuous.div (by fun_prop) (by fun_prop) (fun st => pow_ne_zero 4 (hrne st))


/-- Integrability on `ℝ²` of a continuous function bounded by `D r⁻³`. -/
theorem integrable_of_radial_bound (f : ℝ × ℝ → ℂ) (hf : Continuous f) (D : ℝ)
    (hD : ∀ st : ℝ × ℝ, ‖f st‖ ≤ D * (entryRadius st)⁻¹ ^ 3) : Integrable f := by
  have hfr : (Module.finrank ℝ (ℝ × ℝ) : ℝ) < 3 := by
    rw [Module.finrank_prod, Module.finrank_self]
    norm_num
  have hdom : Integrable (fun x : ℝ × ℝ => 2 * Real.sqrt 2 * (1 + ‖x‖) ^ (-(3 : ℝ))) :=
    (integrable_one_add_norm hfr).const_mul (2 * Real.sqrt 2)
  refine (hdom.const_mul D).mono' hf.aestronglyMeasurable ?_
  filter_upwards with st
  obtain ⟨s, t⟩ := st
  have hD0 : 0 ≤ D := by
    have := hD (0, 0)
    have h0 : 0 ≤ ‖f (0, 0)‖ := norm_nonneg _
    have hr := entryRadius_pos' 0 0
    by_contra hneg
    push Not at hneg
    have : D * (entryRadius (0, 0))⁻¹ ^ 3 < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    linarith
  calc ‖f (s, t)‖ ≤ D * (entryRadius (s, t))⁻¹ ^ 3 := hD (s, t)
    _ ≤ D * (2 * Real.sqrt 2 * (1 + ‖((s, t) : ℝ × ℝ)‖) ^ (-(3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (entryRadius_inv_cube_le' s t) hD0

/-- Integrability of the polar form of a continuous function bounded by `D r⁻³`. -/
theorem polar_integrableOn_of_radial_bound (f : ℝ × ℝ → ℂ) (hf : Continuous f) (D : ℝ)
    (hD : ∀ st : ℝ × ℝ, ‖f st‖ ≤ D * (entryRadius st)⁻¹ ^ 3) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • f (p.1 * Real.sin p.2, p.1 * Real.cos p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) volume := by
  refine Integrable.mono' (radial_dominant_integrableOn_prod.const_mul D) ?_ ?_
  · exact (continuous_fst.smul (hf.comp
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1 * Real.sin p.2, p.1 * Real.cos p.2)))))
      |>.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem
        (by measurability : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi))]
      with p hp
    have hρ : 0 < p.1 := hp.1
    have hnorm := hD (p.1 * Real.sin p.2, p.1 * Real.cos p.2)
    rw [entryRadius_polar p.1 p.2 (Real.sqrt (1 + p.1 ^ 2)) (Real.sq_sqrt (by positivity))
      (Real.sqrt_pos.mpr (by positivity))] at hnorm
    have hρ' : ‖p.1‖ = p.1 := by rw [Real.norm_eq_abs, abs_of_pos hρ]
    have hD0 : 0 ≤ D := by
      have h0 : 0 ≤ ‖f (p.1 * Real.sin p.2, p.1 * Real.cos p.2)‖ := norm_nonneg _
      by_contra hneg
      push Not at hneg
      have : D * (Real.sqrt (1 + p.1 ^ 2))⁻¹ ^ 3 < 0 :=
        mul_neg_of_neg_of_pos hneg (by positivity)
      linarith
    rw [norm_smul, hρ']
    calc p.1 * ‖f (p.1 * Real.sin p.2, p.1 * Real.cos p.2)‖
        ≤ p.1 * (D * (Real.sqrt (1 + p.1 ^ 2))⁻¹ ^ 3) := mul_le_mul_of_nonneg_left hnorm hρ.le
      _ = D * (p.1 * (Real.sqrt (1 + p.1 ^ 2))⁻¹ ^ 3) := by ring
      _ ≤ D * (2 * Real.sqrt 2 * (1 + p.1) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (radial_scaled_dominant_bound p.1 hρ.le) hD0


theorem continuous_coeff_frameCoefficient (n : ℕ) (h : ℂ → ℂ)
    (hh : ContinuousOn h {z : ℂ | 0 < z.im}) (m : Fin 3 →₀ ℕ) (V W : Matrix (Fin 3) (Fin 3) ℝ) :
    Continuous (fun st : ℝ × ℝ =>
      (frameCoefficient (seedForm n h) (entryFrame st.1 st.2) V W).coeff m) := by
  have hfun : (fun st : ℝ × ℝ =>
      (frameCoefficient (seedForm n h) (entryFrame st.1 st.2) V W).coeff m) =
      fun st => h (entryTau st) *
        wedgeSym (entryRadius st : ℂ) st.1 st.2 (entryTau st)
          (dirSym (V + V.transpose) st.1 st.2 (entryTau st))
          (dirSym (W + W.transpose) st.1 st.2 (entryTau st)) *
        (if m.sum (fun _ k => k) = n then
          (m.multinomial : ℂ) * (entryCoefficientA st ^ (m 0) * entryCoefficient st ^ (m 1) *
            (Complex.I / (entryRadius st : ℂ)) ^ (m 2)) else 0) := by
    funext st
    rw [seed_frameCoefficient_entryFrame_sym, MvPolynomial.coeff_C_mul, coeff_linForm_pow]
  rw [hfun]
  have hr : Continuous (fun st : ℝ × ℝ => (entryRadius st : ℂ)) :=
    Complex.continuous_ofReal.comp entryRadius_continuous
  have hrne : ∀ st : ℝ × ℝ, (entryRadius st : ℂ) ≠ 0 := fun st => by
    exact_mod_cast (entryRadius_pos' st.1 st.2).ne'
  have hhτ : Continuous (fun st : ℝ × ℝ => h (entryTau st)) :=
    hh.comp_continuous entryTau_continuous (fun st => entryTau_im_pos st)
  refine (hhτ.mul (wedgeSym_dirSym_continuous _ _)).mul ?_
  split_ifs
  · refine continuous_const.mul ((entryCoefficientA_continuous.pow _).mul
      (entryCoefficient_continuous.pow _) |>.mul ?_)
    exact (continuous_const.div hr hrne).pow _
  · exact continuous_const

/-- The radial decay `‖coeff_m ω̃_h(L_{s,t})(V,W)‖ ≤ D r⁻³` on all of `ℝ²` (`n ≥ 3`). -/
theorem exists_radial_bound_coeff (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ)
    (hh : ContinuousOn h {z : ℂ | 0 < z.im}) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) (m : Fin 3 →₀ ℕ)
    (hm : m.sum (fun _ k => k) = n) (V W : Matrix (Fin 3) (Fin 3) ℝ) :
    ∃ D : ℝ, ∀ st : ℝ × ℝ,
      ‖(frameCoefficient (seedForm n h) (entryFrame st.1 st.2) V W).coeff m‖ ≤
        D * (entryRadius st)⁻¹ ^ 3 := by
  obtain ⟨C, hC⟩ := exists_wedgePoly_bound (V + V.transpose) (W + W.transpose)
  set A : ℝ := ((m.multinomial : ℝ) / 2 ^ (n + 4)) ^ 2 * M * 4 ^ (n + 3) *
    (2 ^ (m 0 + m 1 + m 2)) ^ 2 * C ^ 2 with hA
  have hM0 : 0 ≤ M := by
    have := hM Complex.I (by simp)
    simp at this
    nlinarith [sq_nonneg ‖h Complex.I‖]
  have hA0 : 0 ≤ A := by positivity
  refine ⟨Real.sqrt A, ?_⟩
  have hclosed : IsClosed {st : ℝ × ℝ |
      ‖(frameCoefficient (seedForm n h) (entryFrame st.1 st.2) V W).coeff m‖ ≤
        Real.sqrt A * (entryRadius st)⁻¹ ^ 3} := by
    refine isClosed_le ?_ ?_
    · exact (continuous_coeff_frameCoefficient n h hh m V W).norm
    · exact continuous_const.mul ((entryRadius_continuous.inv₀ (fun st => (entryRadius_pos' st.1 st.2).ne')).pow 3)
  have hsub : {st : ℝ × ℝ | st ≠ (0, 0)} ⊆ {st : ℝ × ℝ |
      ‖(frameCoefficient (seedForm n h) (entryFrame st.1 st.2) V W).coeff m‖ ≤
        Real.sqrt A * (entryRadius st)⁻¹ ^ 3} := by
    intro st hst
    obtain ⟨s, t⟩ := st
    have hsq := coeff_norm_sq_le n h M hM m hm V W C hC s t hst
    have hr := entryRadius_pos' s t
    have hr1 := entryRadius_ge_one' s t
    have h6 : (entryRadius (s, t) ^ 6)⁻¹ ≥ ((entryRadius (s, t)) ^ (n + 3))⁻¹ := by
      apply inv_anti₀ (by positivity)
      exact pow_le_pow_right₀ hr1 (by omega)
    have hle : ‖(frameCoefficient (seedForm n h) (entryFrame s t) V W).coeff m‖ ^ 2 ≤
        (Real.sqrt A * (entryRadius (s, t))⁻¹ ^ 3) ^ 2 := by
      calc _ ≤ A * ((entryRadius (s, t)) ^ (n + 3))⁻¹ := hsq
        _ ≤ A * (entryRadius (s, t) ^ 6)⁻¹ := by gcongr
        _ = (Real.sqrt A * (entryRadius (s, t))⁻¹ ^ 3) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hA0, ← pow_mul, inv_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hle
  have hdense : Dense {st : ℝ × ℝ | st ≠ (0, 0)} := dense_compl_singleton ((0 : ℝ), (0 : ℝ))
  intro st
  have := hclosed.closure_subset_iff.mpr hsub
  rw [hdense.closure_eq] at this
  exact this (Set.mem_univ st)


/-- **The base-point form identity, one coefficient.** For `h` holomorphic on the upper half-plane with the
cusp decay `‖h z‖² (Im z)^{n+3} ≤ M`, `n ≥ 3`, every coefficient `m` of degree `n` of the seed's frame
coefficient `ω̃_h(L_{s,t})(V,W)` is integrable over `ℝ²`, with integral
`c_∞ · h(i) · multinomial(m) · xiPoly m 0 · (A∧B)(V+Vᵀ, W+Wᵀ)`, `c_∞ = -2πi/(n+1)`. -/
theorem base_integral_coeff (n : ℕ) (hn : 3 ≤ n) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im}) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) (m : Fin 3 →₀ ℕ)
    (hm : m.sum (fun _ k => k) = n) (V W : Matrix (Fin 3) (Fin 3) ℝ) :
    Integrable (fun st : ℝ × ℝ =>
      (frameCoefficient (seedForm n h) (entryFrame st.1 st.2) V W).coeff m) ∧
    ∫ st : ℝ × ℝ,
        (frameCoefficient (seedForm n h) (entryFrame st.1 st.2) V W).coeff m =
      (-2 * Real.pi * Complex.I / ((n : ℂ) + 1)) * h Complex.I *
        ((m.multinomial : ℂ) * xiPoly m 0) * linePair (V + V.transpose) (W + W.transpose) := by
  have hcont := continuous_coeff_frameCoefficient n h hh.continuousOn m V W
  obtain ⟨D, hD⟩ := exists_radial_bound_coeff n hn h hh.continuousOn M hM m hm V W
  refine ⟨integrable_of_radial_bound _ hcont D hD, ?_⟩
  rw [integral_eq_iterated_of_polar_integrableOn _
    (polar_integrableOn_of_radial_bound _ hcont D hD)]
  exact iterated_integral_coeff n h hh m hm V W

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
