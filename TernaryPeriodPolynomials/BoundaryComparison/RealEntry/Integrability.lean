module

public import TernaryPeriodPolynomials.BoundaryComparison.RealEntry.Zero
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.Topology.Algebra.IsUniformGroup.Order

@[expose] public section


/-! Clause (ii) of `real_constant_term_entry`: `Integrable (entryIntegrand n)` on `ℝ × ℝ`. -/


open MeasureTheory

namespace TernaryPeriodPolynomials.Argument

/-- Factor 1 of the pointwise bound: `(entryRadius (s,t) : ℂ) ^ (-3:ℤ)` has norm exactly
`(entryRadius (s,t))⁻¹ ^ 3`. -/
theorem entryIntegrand_norm_factor1 (s t : ℝ) :
    ‖(entryRadius (s, t) : ℂ) ^ (-3 : ℤ)‖ = (entryRadius (s, t))⁻¹ ^ 3 := by
  rw [Complex.norm_zpow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (entryRadius_pos s t)]
  norm_num [zpow_neg]

/-- Factor 2: `‖entryTau (s,t) + I‖ ≥ 1`. -/
theorem entryTau_add_I_norm_ge_one (s t : ℝ) :
    1 ≤ ‖entryTau (s, t) + Complex.I‖ := by
  have hC : (0 : ℝ) < 1 + s ^ 2 := by positivity
  set z := entryTau (s, t) + Complex.I with hz_def
  have him : z.im = entryRadius (s, t) / (1 + s ^ 2) + 1 := by
    rw [hz_def]
    unfold entryTau
    simp [Complex.div_im, Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
      Complex.I_im, Complex.I_re, Complex.ofReal_im, Complex.ofReal_re, Complex.normSq_apply,
      pow_two]
    field_simp
  have hbound : z.im ≤ ‖z‖ := Complex.im_le_norm _
  rw [him] at hbound
  have hpos : (0 : ℝ) < entryRadius (s, t) / (1 + s ^ 2) := div_pos (entryRadius_pos s t) hC
  linarith

/-- Factor 3: `‖entryCoefficient (s,t)‖ ≤ 1`. -/
theorem entryCoefficient_norm_le_one (s t : ℝ) :
    ‖entryCoefficient (s, t)‖ ≤ 1 := by
  have hCpos : (0 : ℝ) < 1 + s ^ 2 := by positivity
  have hr2 := entryRadius_sq s t
  have hrpos := entryRadius_pos s t
  unfold entryCoefficient
  set y := s * t / entryRadius (s, t) with hy_def
  have hnum_eq : ‖(1 : ℂ) + Complex.I * (y : ℂ)‖ ^ 2 = 1 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, mul_comm Complex.I (y : ℂ)]
    simpa using Complex.normSq_add_mul_I 1 y
  have hy2 : y ^ 2 = s ^ 2 * t ^ 2 / entryRadius (s, t) ^ 2 := by
    rw [hy_def, div_pow, mul_pow]
  have hr2pos : (0 : ℝ) < entryRadius (s, t) ^ 2 := by positivity
  have h1y2 : 1 + y ^ 2 = (1 + s ^ 2) * (1 + t ^ 2) / entryRadius (s, t) ^ 2 := by
    rw [hy2, hr2]; field_simp; ring
  have hle : (1 + s ^ 2) * (1 + t ^ 2) / entryRadius (s, t) ^ 2 ≤ (1 + s ^ 2) ^ 2 := by
    rw [div_le_iff₀ hr2pos, hr2]
    nlinarith [sq_nonneg s, sq_nonneg t, sq_nonneg (s * t)]
  have hnorm_sq_le : ‖(1 : ℂ) + Complex.I * (y : ℂ)‖ ^ 2 ≤ (1 + s ^ 2) ^ 2 := by
    rw [hnum_eq, h1y2]; exact hle
  have hnorm_le : ‖(1 : ℂ) + Complex.I * (y : ℂ)‖ ≤ 1 + s ^ 2 := by
    have h2 : (0 : ℝ) ≤ 1 + s ^ 2 := by positivity
    have hh := abs_le_of_sq_le_sq hnorm_sq_le h2
    rwa [abs_of_nonneg (norm_nonneg _)] at hh
  rw [Complex.norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCpos, norm_neg]
  rw [div_le_one hCpos]
  exact hnorm_le

/-- Step A assembled: the pointwise bound `‖entryIntegrand n (s,t)‖ ≤ (entryRadius (s,t))⁻¹ ^ 3`. -/
theorem entryIntegrand_norm_le (n : ℕ) (s t : ℝ) :
    ‖entryIntegrand n (s, t)‖ ≤ (entryRadius (s, t))⁻¹ ^ 3 := by
  unfold entryIntegrand
  rw [norm_mul, norm_mul, entryIntegrand_norm_factor1]
  have hmid : ‖(entryTau (s, t) + Complex.I) ^ (-((n : ℤ) + 3))‖ ≤ 1 := by
    rw [Complex.norm_zpow]
    exact zpow_le_one_of_nonpos₀ (entryTau_add_I_norm_ge_one s t) (by omega)
  have hcoef : ‖entryCoefficient (s, t) ^ n‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (entryCoefficient_norm_le_one s t)
  have hA : (0 : ℝ) ≤ (entryRadius (s, t))⁻¹ ^ 3 :=
    (pow_pos (inv_pos.mpr (entryRadius_pos s t)) 3).le
  have step1 :
      (entryRadius (s, t))⁻¹ ^ 3 * ‖(entryTau (s, t) + Complex.I) ^ (-((n : ℤ) + 3))‖ ≤
        (entryRadius (s, t))⁻¹ ^ 3 * 1 :=
    mul_le_mul_of_nonneg_left hmid hA
  have step2 :
      (entryRadius (s, t))⁻¹ ^ 3 * ‖(entryTau (s, t) + Complex.I) ^ (-((n : ℤ) + 3))‖ *
          ‖entryCoefficient (s, t) ^ n‖ ≤
        (entryRadius (s, t))⁻¹ ^ 3 * 1 * 1 :=
    mul_le_mul step1 hcoef (norm_nonneg _) (mul_nonneg hA zero_le_one)
  calc
    (entryRadius (s, t))⁻¹ ^ 3 * ‖(entryTau (s, t) + Complex.I) ^ (-((n : ℤ) + 3))‖ *
          ‖entryCoefficient (s, t) ^ n‖ ≤
        (entryRadius (s, t))⁻¹ ^ 3 * 1 * 1 := step2
    _ = (entryRadius (s, t))⁻¹ ^ 3 := by ring

theorem entryRadius_continuous : Continuous entryRadius := by
  unfold entryRadius
  exact Real.continuous_sqrt.comp (by fun_prop)

theorem entryRadius_ne_zero (st : ℝ × ℝ) : entryRadius st ≠ 0 :=
  (entryRadius_pos st.1 st.2).ne'

theorem entryTau_add_I_ne_zero (st : ℝ × ℝ) : entryTau st + Complex.I ≠ 0 :=
  norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (entryTau_add_I_norm_ge_one st.1 st.2))

theorem entryTau_continuous : Continuous entryTau := by
  unfold entryTau
  have hnum : Continuous (fun st : ℝ × ℝ =>
      (((-(st.1 * st.2) : ℝ) : ℂ) + Complex.I * (entryRadius st : ℂ))) :=
    (Complex.continuous_ofReal.comp (by fun_prop)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp entryRadius_continuous))
  have hden : Continuous (fun st : ℝ × ℝ => ((1 + st.1 ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (by fun_prop)
  have hdenne : ∀ st : ℝ × ℝ, ((1 + st.1 ^ 2 : ℝ) : ℂ) ≠ 0 := fun st => by
    exact_mod_cast (show (1 + st.1 ^ 2 : ℝ) ≠ 0 by positivity)
  exact hnum.div₀ hden hdenne

theorem entryCoefficient_continuous : Continuous entryCoefficient := by
  unfold entryCoefficient
  have hinner : Continuous (fun st : ℝ × ℝ => (st.1 * st.2 / entryRadius st : ℝ)) :=
    Continuous.div₀ (by fun_prop) entryRadius_continuous entryRadius_ne_zero
  have hnum : Continuous (fun st : ℝ × ℝ =>
      -(1 + Complex.I * ((st.1 * st.2 / entryRadius st : ℝ) : ℂ))) :=
    (continuous_const.add (continuous_const.mul (Complex.continuous_ofReal.comp hinner))).neg
  have hden : Continuous (fun st : ℝ × ℝ => ((1 + st.1 ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (by fun_prop)
  have hdenne : ∀ st : ℝ × ℝ, ((1 + st.1 ^ 2 : ℝ) : ℂ) ≠ 0 := fun st => by
    exact_mod_cast (show (1 + st.1 ^ 2 : ℝ) ≠ 0 by positivity)
  exact hnum.div₀ hden hdenne

theorem entryIntegrand_continuous (n : ℕ) : Continuous (entryIntegrand n) := by
  unfold entryIntegrand
  have h1 : Continuous (fun st : ℝ × ℝ => (entryRadius st : ℂ) ^ (-3 : ℤ)) :=
    Continuous.zpow₀ (Complex.continuous_ofReal.comp entryRadius_continuous) (-3)
      (fun st => Or.inl (by
        show (entryRadius st : ℂ) ≠ 0
        exact_mod_cast entryRadius_ne_zero st))
  have h2 : Continuous (fun st : ℝ × ℝ => (entryTau st + Complex.I) ^ (-((n : ℤ) + 3))) :=
    Continuous.zpow₀ (entryTau_continuous.add continuous_const) (-((n : ℤ) + 3))
      (fun st => Or.inl (entryTau_add_I_ne_zero st))
  have h3 : Continuous (fun st : ℝ × ℝ => entryCoefficient st ^ n) :=
    entryCoefficient_continuous.pow n
  exact (h1.mul h2).mul h3

/-- Step B: geometric domination `(entryRadius (s,t))⁻¹ ^ 3 ≤ 2√2 (1 + max |s| |t|)^{-3}`. -/
theorem entryRadius_inv_cube_le (s t : ℝ) :
    (entryRadius (s, t))⁻¹ ^ 3 ≤ 2 * Real.sqrt 2 * (1 + max |s| |t|) ^ (-(3 : ℝ)) := by
  have hr2 : (entryRadius (s, t)) ^ 2 = 1 + s ^ 2 + t ^ 2 := entryRadius_sq s t
  have hrpos : 0 < entryRadius (s, t) := entryRadius_pos s t
  set r := entryRadius (s, t)
  set m := max |s| |t| with hm_def
  have hmnn : 0 ≤ m := le_trans (abs_nonneg s) (le_max_left _ _)
  have hsq : (1 + m) ^ 2 ≤ 2 * r ^ 2 := by
    rw [hr2, hm_def]
    rcases le_total |s| |t| with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg (|t| - 1), sq_nonneg s, sq_abs t]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg (|s| - 1), sq_nonneg t, sq_abs s]
  have hsq2 : (1 + m) ^ 2 ≤ (Real.sqrt 2 * r) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  have hlin : 1 + m ≤ Real.sqrt 2 * r := by
    have h2 : (0 : ℝ) ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg 2) hrpos.le
    have hh := abs_le_of_sq_le_sq hsq2 h2
    rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 + m)] at hh
  have hcube : (1 + m) ^ 3 ≤ (Real.sqrt 2 * r) ^ 3 :=
    pow_le_pow_left₀ (by linarith) hlin 3
  have h3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  have hcube2 : (1 + m) ^ 3 ≤ 2 * Real.sqrt 2 * r ^ 3 := by
    calc (1 + m) ^ 3 ≤ (Real.sqrt 2 * r) ^ 3 := hcube
      _ = 2 * Real.sqrt 2 * r ^ 3 := by rw [mul_pow, h3]
  have hr3pos : 0 < r ^ 3 := pow_pos hrpos 3
  have hm3pos : 0 < (1 + m) ^ 3 := pow_pos (by linarith : (0:ℝ) < 1 + m) 3
  rw [Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 + m),
    show (3:ℝ) = ((3:ℕ):ℝ) from by norm_num, Real.rpow_natCast,
    inv_pow, inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hr3pos hm3pos]
  linarith [hcube2]

/-- Bridge: Step B's bound restated using the product-space (sup) norm. -/
theorem entryRadius_inv_cube_le' (s t : ℝ) :
    (entryRadius (s, t))⁻¹ ^ 3 ≤
      2 * Real.sqrt 2 * (1 + ‖((s, t) : ℝ × ℝ)‖) ^ (-(3 : ℝ)) := by
  have hnorm : ‖((s, t) : ℝ × ℝ)‖ = max |s| |t| := by
    simp [Prod.norm_def, Real.norm_eq_abs]
  rw [hnorm]
  exact entryRadius_inv_cube_le s t

/-- Clause (ii) of `real_constant_term_entry`: `Integrable (entryIntegrand n)` on `ℝ × ℝ`
(Lebesgue/volume measure). -/
theorem real_constant_term_entry_clause2 (n : ℕ) :
    Integrable (entryIntegrand n) := by
  have hfr : (Module.finrank ℝ (ℝ × ℝ) : ℝ) < 3 := by
    rw [Module.finrank_prod, Module.finrank_self]
    norm_num
  have hdom : Integrable (fun x : ℝ × ℝ => 2 * Real.sqrt 2 * (1 + ‖x‖) ^ (-(3 : ℝ))) :=
    (integrable_one_add_norm hfr).const_mul (2 * Real.sqrt 2)
  refine hdom.mono' (entryIntegrand_continuous n).aestronglyMeasurable ?_
  filter_upwards with st
  obtain ⟨s, t⟩ := st
  calc ‖entryIntegrand n (s, t)‖
      ≤ (entryRadius (s, t))⁻¹ ^ 3 := entryIntegrand_norm_le n s t
    _ ≤ 2 * Real.sqrt 2 * (1 + ‖((s, t) : ℝ × ℝ)‖) ^ (-(3 : ℝ)) := entryRadius_inv_cube_le' s t

end TernaryPeriodPolynomials.Argument
