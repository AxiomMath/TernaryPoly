module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.MeanValuePolar
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Zero
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Integrability
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.PolarIntegrability
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.MeanValueInner
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.FubiniSplit
public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Clause3

@[expose] public section


/-!
# The real-entry integral of a holomorphic function: decay, integrability, polar Fubini

Under the cusp-form decay `‖h z‖² (Im z)^{n+3} ≤ M` (for `n ≥ 3`) the integrand `r⁻³ h(τ) bⁿ` of the
real entry is dominated by `√M r⁻³` (`entryIntegrandOf_norm_le`), hence integrable on `ℝ²`
(`entryIntegrandOf_integrable`) and in polar coordinates, and the polar change of variables plus
Fubini reduce its integral to the angular integrals of `MeanValueInner`
(`integral_entryIntegrandOf`: `∫ r⁻³ h bⁿ = (∫ r⁻³ h₀ bⁿ) · (2i)^{n+3} h(i)`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

open TernaryPeriodPolynomials.Argument MeasureTheory Set

theorem entryTau_im (st : ℝ × ℝ) : (entryTau st).im = entryRadius st / (1 + st.1 ^ 2) := by
  unfold entryTau
  rw [Complex.div_ofReal_im]
  simp

theorem entryCoefficient_sq_norm (st : ℝ × ℝ) :
    ‖entryCoefficient st‖ ^ 2 =
      (1 + (st.1 * st.2 / entryRadius st) ^ 2) / (1 + st.1 ^ 2) ^ 2 := by
  unfold entryCoefficient
  have hA : (0 : ℝ) < 1 + st.1 ^ 2 := by positivity
  rw [norm_div, div_pow, norm_neg, Complex.sq_norm, Complex.norm_real, Real.norm_of_nonneg hA.le]
  simp [Complex.normSq_apply]
  ring

theorem entryCoefficient_sq_norm_mul_le (st : ℝ × ℝ) :
    ‖entryCoefficient st‖ ^ 2 * (1 + st.1 ^ 2) ≤ 1 := by
  have hr : 0 < entryRadius st := by
    have := entryRadius_pos st.1 st.2
    simpa using this
  have hr2 : entryRadius st ^ 2 = 1 + st.1 ^ 2 + st.2 ^ 2 := by
    have := entryRadius_sq st.1 st.2
    simpa using this
  have hA : (0 : ℝ) < 1 + st.1 ^ 2 := by positivity
  rw [entryCoefficient_sq_norm]
  have hx : (st.1 * st.2 / entryRadius st) ^ 2 ≤ st.1 ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity), mul_pow]
    nlinarith [sq_nonneg st.1, sq_nonneg st.2]
  rw [div_mul_eq_mul_div, div_le_one (by positivity)]
  nlinarith


theorem norm_entryIntegrandOf (h : ℂ → ℂ) (n : ℕ) (st : ℝ × ℝ) :
    ‖entryIntegrandOf h n st‖ =
      (entryRadius st)⁻¹ ^ 3 * ‖h (entryTau st)‖ * ‖entryCoefficient st‖ ^ n := by
  have hr : 0 < entryRadius st := by simpa using entryRadius_pos st.1 st.2
  unfold entryIntegrandOf
  rw [norm_mul, norm_mul, norm_pow, norm_zpow, Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast, inv_pow]

/-- **Squared decay bound.** If `‖h z‖² (Im z)^{n+3} ≤ M` on the upper half-plane (the growth of a
cusp form of weight `n+3`), then `‖r⁻³ h(τ) bⁿ‖² r^{n+3} ≤ M`. -/
theorem entryIntegrandOf_sq_bound (h : ℂ → ℂ) (n : ℕ) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) (st : ℝ × ℝ) :
    ‖entryIntegrandOf h n st‖ ^ 2 * entryRadius st ^ (n + 3) ≤ M := by
  have hr : 0 < entryRadius st := by simpa using entryRadius_pos st.1 st.2
  have hr2 : entryRadius st ^ 2 = 1 + st.1 ^ 2 + st.2 ^ 2 := by
    have := entryRadius_sq st.1 st.2
    simpa using this
  set r := entryRadius st with hrdef
  set A : ℝ := 1 + st.1 ^ 2 with hAdef
  have hA : 0 < A := by positivity
  have hAr : A ≤ r ^ 2 := by rw [hr2]; nlinarith [sq_nonneg st.2]
  have hy : (entryTau st).im = r / A := entryTau_im st
  have hM0 : 0 ≤ M := by
    have := hM Complex.I (by simp)
    simp only [Complex.I_im, one_pow, mul_one] at this
    exact le_trans (sq_nonneg _) this
  have h1 := hM (entryTau st) (by rw [hy]; positivity)
  rw [hy, div_pow] at h1
  have h2 : ‖h (entryTau st)‖ ^ 2 * r ^ (n + 3) ≤ M * A ^ (n + 3) := by
    have hApos : 0 < A ^ (n + 3) := by positivity
    rw [mul_div_assoc', div_le_iff₀ hApos] at h1
    exact h1
  have hb := entryCoefficient_sq_norm_mul_le st
  set u := ‖h (entryTau st)‖ ^ 2 with hu
  set v := ‖entryCoefficient st‖ ^ 2 with hv
  have hv0 : 0 ≤ v := sq_nonneg _
  have hu0 : 0 ≤ u := sq_nonneg _
  have hvn : v ^ n * A ^ n ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by positivity) (by simpa [mul_comm] using hb)
  have hnorm : ‖entryIntegrandOf h n st‖ ^ 2 = (r⁻¹) ^ 6 * u * v ^ n := by
    rw [norm_entryIntegrandOf]
    simp only [hu, hv]
    ring
  rw [hnorm]
  have hr6 : 0 < r ^ 6 := by positivity
  have hAcube : A ^ 3 ≤ r ^ 6 := by
    calc A ^ 3 ≤ (r ^ 2) ^ 3 := pow_le_pow_left₀ hA.le hAr 3
      _ = r ^ 6 := by ring
  calc (r⁻¹) ^ 6 * u * v ^ n * r ^ (n + 3)
      = (r⁻¹) ^ 6 * (u * r ^ (n + 3)) * v ^ n := by ring
    _ ≤ (r⁻¹) ^ 6 * (M * A ^ (n + 3)) * v ^ n := by gcongr
    _ = (r⁻¹) ^ 6 * M * A ^ 3 * (v ^ n * A ^ n) := by ring
    _ ≤ (r⁻¹) ^ 6 * M * A ^ 3 * 1 := by gcongr
    _ ≤ (r⁻¹) ^ 6 * M * r ^ 6 := by
        rw [mul_one]
        gcongr
    _ = M := by
        rw [inv_pow]; field_simp


theorem entryRadius_ge_one (st : ℝ × ℝ) : 1 ≤ entryRadius st := by
  have hr : 0 < entryRadius st := by simpa using entryRadius_pos st.1 st.2
  have hr2 : entryRadius st ^ 2 = 1 + st.1 ^ 2 + st.2 ^ 2 := by
    have := entryRadius_sq st.1 st.2
    simpa using this
  nlinarith [sq_nonneg st.1, sq_nonneg st.2]

/-- **Pointwise bound** `‖r⁻³ h(τ) bⁿ‖ ≤ √M r⁻³` for `n ≥ 3` under the squared decay hypothesis. -/
theorem entryIntegrandOf_norm_le (h : ℂ → ℂ) (n : ℕ) (hn : 3 ≤ n) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) (st : ℝ × ℝ) :
    ‖entryIntegrandOf h n st‖ ≤ Real.sqrt M * (entryRadius st)⁻¹ ^ 3 := by
  have hr : 0 < entryRadius st := by simpa using entryRadius_pos st.1 st.2
  have hr1 := entryRadius_ge_one st
  have hsq := entryIntegrandOf_sq_bound h n M hM st
  have h6 : entryRadius st ^ 6 ≤ entryRadius st ^ (n + 3) :=
    pow_le_pow_right₀ hr1 (by omega)
  have hle : (‖entryIntegrandOf h n st‖ * entryRadius st ^ 3) ^ 2 ≤ M := by
    calc (‖entryIntegrandOf h n st‖ * entryRadius st ^ 3) ^ 2
        = ‖entryIntegrandOf h n st‖ ^ 2 * entryRadius st ^ 6 := by ring
      _ ≤ ‖entryIntegrandOf h n st‖ ^ 2 * entryRadius st ^ (n + 3) := by gcongr
      _ ≤ M := hsq
  have h1 : ‖entryIntegrandOf h n st‖ * entryRadius st ^ 3 ≤ Real.sqrt M :=
    (le_abs_self _).trans (Real.abs_le_sqrt hle)
  have hr3 : 0 < entryRadius st ^ 3 := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hr3]
  exact h1


theorem entryTau_im_pos (st : ℝ × ℝ) : 0 < (entryTau st).im := by
  rw [entryTau_im]
  have hr : 0 < entryRadius st := by simpa using entryRadius_pos st.1 st.2
  positivity

theorem entryIntegrandOf_continuous (h : ℂ → ℂ) (hh : ContinuousOn h {z : ℂ | 0 < z.im})
    (n : ℕ) : Continuous (entryIntegrandOf h n) := by
  unfold entryIntegrandOf
  have h1 : Continuous (fun st : ℝ × ℝ => (entryRadius st : ℂ) ^ (-3 : ℤ)) :=
    Continuous.zpow₀ (Complex.continuous_ofReal.comp entryRadius_continuous) (-3)
      (fun st => Or.inl (by
        show (entryRadius st : ℂ) ≠ 0
        exact_mod_cast entryRadius_ne_zero st))
  have h2 : Continuous (fun st : ℝ × ℝ => h (entryTau st)) :=
    hh.comp_continuous entryTau_continuous (fun st => entryTau_im_pos st)
  exact (h1.mul h2).mul (entryCoefficient_continuous.pow n)

/-- **Integrability on `ℝ²`** of the real-entry integrand of a continuous `h` with the decay
`‖h z‖² (Im z)^{n+3} ≤ M` of a cusp form of weight `n+3`, for `n ≥ 3`. -/
theorem entryIntegrandOf_integrable (h : ℂ → ℂ) (hh : ContinuousOn h {z : ℂ | 0 < z.im})
    (n : ℕ) (hn : 3 ≤ n) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) :
    Integrable (entryIntegrandOf h n) := by
  have hfr : (Module.finrank ℝ (ℝ × ℝ) : ℝ) < 3 := by
    rw [Module.finrank_prod, Module.finrank_self]
    norm_num
  have hdom : Integrable (fun x : ℝ × ℝ => 2 * Real.sqrt 2 * (1 + ‖x‖) ^ (-(3 : ℝ))) :=
    (integrable_one_add_norm hfr).const_mul (2 * Real.sqrt 2)
  refine (hdom.const_mul (Real.sqrt M)).mono' (entryIntegrandOf_continuous h hh n).aestronglyMeasurable ?_
  filter_upwards with st
  obtain ⟨s, t⟩ := st
  calc ‖entryIntegrandOf h n (s, t)‖
      ≤ Real.sqrt M * (entryRadius (s, t))⁻¹ ^ 3 := entryIntegrandOf_norm_le h n hn M hM (s, t)
    _ ≤ Real.sqrt M * (2 * Real.sqrt 2 * (1 + ‖((s, t) : ℝ × ℝ)‖) ^ (-(3 : ℝ))) :=
        mul_le_mul_of_nonneg_left (entryRadius_inv_cube_le' s t) (Real.sqrt_nonneg M)

/-- Integrability of the polar-rewritten integrand on `Ioi 0 ×ˢ Ioo (-π) π`. -/
theorem entryIntegrandOf_polar_integrableOn (h : ℂ → ℂ) (hh : ContinuousOn h {z : ℂ | 0 < z.im})
    (n : ℕ) (hn : 3 ≤ n) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) :
    IntegrableOn
      (fun p : ℝ × ℝ => p.1 • entryIntegrandOf h n (p.1 * Real.sin p.2, p.1 * Real.cos p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) volume := by
  refine Integrable.mono' (radial_dominant_integrableOn_prod.const_mul (Real.sqrt M)) ?_ ?_
  · exact (continuous_fst.smul ((entryIntegrandOf_continuous h hh n).comp
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1 * Real.sin p.2, p.1 * Real.cos p.2)))))
      |>.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem
        (by measurability : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi))]
      with p hp
    have hρ : 0 < p.1 := hp.1
    have hnorm := entryIntegrandOf_norm_le h n hn M hM (p.1 * Real.sin p.2, p.1 * Real.cos p.2)
    rw [entryRadius_polar p.1 p.2 (Real.sqrt (1 + p.1 ^ 2)) (Real.sq_sqrt (by positivity))
      (Real.sqrt_pos.mpr (by positivity))] at hnorm
    have hρ' : ‖p.1‖ = p.1 := by rw [Real.norm_eq_abs, abs_of_pos hρ]
    rw [norm_smul, hρ']
    calc p.1 * ‖entryIntegrandOf h n (p.1 * Real.sin p.2, p.1 * Real.cos p.2)‖
        ≤ p.1 * (Real.sqrt M * (Real.sqrt (1 + p.1 ^ 2))⁻¹ ^ 3) :=
          mul_le_mul_of_nonneg_left hnorm hρ.le
      _ = Real.sqrt M * (p.1 * (Real.sqrt (1 + p.1 ^ 2))⁻¹ ^ 3) := by ring
      _ ≤ Real.sqrt M * (2 * Real.sqrt 2 * (1 + p.1) ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (radial_scaled_dominant_bound p.1 hρ.le) (Real.sqrt_nonneg M)

/-- Polar change of variables and Fubini for a general integrand `f` (the polar form is
integrable). -/
theorem integral_eq_iterated_of_polar_integrableOn (f : ℝ × ℝ → ℂ)
    (hf : IntegrableOn (fun p : ℝ × ℝ => p.1 • f (p.1 * Real.sin p.2, p.1 * Real.cos p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) volume) :
    (∫ z : ℝ × ℝ, f z) = ∫ ρ in Set.Ioi (0 : ℝ), ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        ρ • f (ρ * Real.sin θ, ρ * Real.cos θ) := by
  have h1 : (∫ z : ℝ × ℝ, f z) = ∫ z : ℝ × ℝ, f z.swap :=
    (MeasureTheory.integral_prod_swap f).symm
  have h2 : (∫ z : ℝ × ℝ, f z.swap) =
      ∫ p in polarCoord.target, p.1 • f (p.1 * Real.sin p.2, p.1 * Real.cos p.2) := by
    rw [← integral_comp_polarCoord_symm (fun z : ℝ × ℝ => f z.swap)]
    congr 1
  rw [h1, h2, polarCoord_target]
  exact MeasureTheory.setIntegral_prod _ hf

/-- **The real entry of a holomorphic function.** For `h` holomorphic on the upper half-plane with
the cusp-form decay `‖h z‖² (Im z)^{n+3} ≤ M`, `n ≥ 3`:
`∫_{ℝ²} r⁻³ h(τ) bⁿ ds dt = (∫_{ℝ²} r⁻³ (τ+i)^{-(n+3)} bⁿ ds dt) · (2i)^{n+3} h(i)`. -/
theorem integral_entryIntegrandOf (h : ℂ → ℂ) (hh : DifferentiableOn ℂ h {z : ℂ | 0 < z.im})
    (n : ℕ) (hn : 3 ≤ n) (M : ℝ)
    (hM : ∀ z : ℂ, 0 < z.im → ‖h z‖ ^ 2 * z.im ^ (n + 3) ≤ M) :
    ∫ st : ℝ × ℝ, entryIntegrandOf h n st =
      (∫ st : ℝ × ℝ, entryIntegrand n st) * ((2 * Complex.I) ^ (n + 3) * h Complex.I) := by
  rw [integral_eq_iterated_of_polar_integrableOn _
      (entryIntegrandOf_polar_integrableOn h hh.continuousOn n hn M hM),
    entryIntegrand_integral_eq_iterated n, ← MeasureTheory.integral_mul_const]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun ρ hρ => ?_)
  exact inner_integral_scaling h hh n ρ hρ

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
