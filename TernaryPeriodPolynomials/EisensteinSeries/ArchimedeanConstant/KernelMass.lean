module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineArchimedeanKernel
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.ENNReal
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn

@[expose] public section


/-!
# The total mass of the standard good-line real kernel

`standardGoodLineRealKernel s u = (1 + |u|²)^(-3/4 - s/2)`. For `Re s > 1/2` its integral over
`ℝ²` is `π / (s/2 - 1/4)`. This explicit meromorphic function of `s` takes the nonzero value `-π`
at the cohomological point `s = -3/2`. It is the scalar normalization of the archimedean
intertwining integral in the spherical good-cusp detection argument.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open MeasureTheory Set Filter Topology Real GeneralEisenstein
open TernaryPeriodPolynomials.SphericalDetection

noncomputable section

namespace TernaryPeriodPolynomials.ArchimedeanConstant

/-- The radial profile `r ↦ r (1 + r²)^c` with a complex exponent. -/
def radialProfile (c : ℂ) (r : ℝ) : ℂ := (r : ℂ) * Complex.exp (c * (Real.log (1 + r ^ 2) : ℂ))

/-- Its antiderivative. -/
def radialPrimitive (c : ℂ) (r : ℝ) : ℂ :=
  Complex.exp ((c + 1) * (Real.log (1 + r ^ 2) : ℂ)) / (2 * (c + 1))

theorem one_add_sq_pos (r : ℝ) : 0 < 1 + r ^ 2 := by positivity

theorem radialPrimitive_hasDerivAt (c : ℂ) (hc : c + 1 ≠ 0) (r : ℝ) :
    HasDerivAt (radialPrimitive c) (radialProfile c r) r := by
  have hpos := one_add_sq_pos r
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x ^ 2)) (2 * r / (1 + r ^ 2)) r := by
    have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).const_add 1
    exact h1.log hpos.ne'
  have hlogC : HasDerivAt (fun x : ℝ => ((Real.log (1 + x ^ 2) : ℝ) : ℂ))
      (((2 * r / (1 + r ^ 2) : ℝ) : ℂ)) r := hlog.ofReal_comp
  have hexp := ((hlogC.const_mul (c + 1)).cexp).div_const (2 * (c + 1))
  unfold radialPrimitive radialProfile
  refine hexp.congr_deriv ?_
  have hexp_split : Complex.exp ((c + 1) * (Real.log (1 + r ^ 2) : ℂ)) =
      Complex.exp (c * (Real.log (1 + r ^ 2) : ℂ)) * ((1 + r ^ 2 : ℝ) : ℂ) := by
    rw [add_mul, one_mul, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hpos]
  rw [hexp_split]
  push_cast
  have hne : (1 + (r : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

theorem norm_exp_mul_log (c : ℂ) (r : ℝ) :
    ‖Complex.exp (c * (Real.log (1 + r ^ 2) : ℂ))‖ = (1 + r ^ 2) ^ c.re := by
  rw [Complex.norm_exp, Real.rpow_def_of_pos (one_add_sq_pos r)]
  congr 1
  simp [Complex.mul_re]
  ring

theorem radialPrimitive_tendsto (c : ℂ) (hc : (c + 1).re < 0) :
    Tendsto (radialPrimitive c) atTop (𝓝 0) := by
  unfold radialPrimitive
  rw [show (0 : ℂ) = 0 / (2 * (c + 1)) by simp]
  apply Tendsto.div_const
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hform : (fun r : ℝ => ‖Complex.exp ((c + 1) * (Real.log (1 + r ^ 2) : ℂ))‖) =
      fun r => (1 + r ^ 2) ^ (c + 1).re := by
    funext r; exact norm_exp_mul_log (c + 1) r
  rw [hform]
  have h1 : Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by norm_num))
  exact (tendsto_rpow_neg_atTop (by linarith : 0 < -(c + 1).re)).comp h1 |>.congr
    (fun r => by simp)

theorem radialProfile_integrable (c : ℂ) (hc : c.re < -1) :
    IntegrableOn (radialProfile c) (Ioi 0) := by
  have hbase : Integrable (fun r : ℝ => (1 + ‖r‖ ^ 2) ^ (-(-2 * c.re - 1) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (E := ℝ) (by simp; linarith)
  refine (hbase.mono' ?_ ?_).integrableOn
  · unfold radialProfile
    fun_prop
  · filter_upwards with r
    rw [radialProfile, norm_mul, norm_exp_mul_log, Complex.norm_real, Real.norm_eq_abs]
    have hpos := one_add_sq_pos r
    have habs : |r| ≤ (1 + r ^ 2) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.abs_le_sqrt (by nlinarith)
    rw [sq_abs]
    calc |r| * (1 + r ^ 2) ^ c.re ≤ (1 + r ^ 2) ^ (1 / 2 : ℝ) * (1 + r ^ 2) ^ c.re :=
          mul_le_mul_of_nonneg_right habs (Real.rpow_nonneg hpos.le _)
      _ = (1 + r ^ 2) ^ (-(-2 * c.re - 1) / 2) := by
          rw [← Real.rpow_add hpos]; congr 1; ring

/-- The radial integral `∫₀^∞ r (1 + r²)^c dr = -1 / (2 (c + 1))` for `Re c < -1`. -/
theorem integral_radialProfile (c : ℂ) (hc : c.re < -1) :
    ∫ r in Ioi 0, radialProfile c r = -1 / (2 * (c + 1)) := by
  have hc1 : c + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hre : (c + 1).re < 0 := by simp; linarith
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun r _ => radialPrimitive_hasDerivAt c hc1 r)
    (radialProfile_integrable c hc) (radialPrimitive_tendsto c hre)]
  simp [radialPrimitive]
  field_simp

/-- In polar coordinates the kernel is the radial profile. -/
theorem kernel_polar (s : ℂ) (p : ℝ × ℝ) :
    p.1 • Helpers.standardGoodLineRealKernel s (polarCoord.symm p) =
      radialProfile (-(3 : ℂ) / 4 - s / 2) p.1 := by
  have hsum : 1 + (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = 1 + p.1 ^ 2 := by
    have := Real.sin_sq_add_cos_sq p.2
    linear_combination p.1 ^ 2 * this
  rw [polarCoord_symm_apply, Helpers.standardGoodLineRealKernel, radialProfile, hsum,
    Complex.real_smul]

/-- The total mass `∫_{ℝ²} (1 + |u|²)^(-3/4 - s/2) du = π / (s/2 - 1/4)` for `Re s > 1/2`. -/
theorem integral_standardGoodLineRealKernel (s : ℂ) (hs : 1 / 2 < s.re) :
    ∫ u : ℝ × ℝ, Helpers.standardGoodLineRealKernel s u = Real.pi / (s / 2 - 1 / 4) := by
  set c : ℂ := -(3 : ℂ) / 4 - s / 2 with hc
  have hcre : c.re < -1 := by
    rw [hc]; simp; linarith
  rw [← integral_comp_polarCoord_symm]
  have hcongr : ∫ p in polarCoord.target,
      p.1 • Helpers.standardGoodLineRealKernel s (polarCoord.symm p) =
      ∫ p in polarCoord.target, radialProfile c p.1 * (1 : ℂ) := by
    refine setIntegral_congr_fun polarCoord.open_target.measurableSet (fun p _ => ?_)
    rw [kernel_polar, mul_one]
  have hprod := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (radialProfile c) (fun _ : ℝ => (1 : ℂ)) (Ioi 0) (Ioo (-π) π)
  rw [hcongr, polarCoord_target, Measure.volume_eq_prod, hprod, integral_radialProfile c hcre]
  have hlen : (∫ _y in Ioo (-π) π, (1 : ℂ)) = ((2 * π : ℝ) : ℂ) := by
    rw [integral_const, measureReal_restrict_apply_univ, Real.volume_real_Ioo,
      max_eq_left (by linarith [Real.pi_pos]), Complex.real_smul, mul_one]
    push_cast; ring
  rw [hlen]
  have hne : s / 2 - 1 / 4 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hc1 : c + 1 = -(s / 2 - 1 / 4) := by rw [hc]; ring
  rw [hc1]
  push_cast
  field_simp

/-- At the cohomological point the continued mass is `-π ≠ 0`. -/
theorem kernelMass_cohomological :
    Real.pi / (cohomologicalPoint / 2 - 1 / 4 : ℂ) = -Real.pi := by
  norm_num [cohomologicalPoint]
  ring

end TernaryPeriodPolynomials.ArchimedeanConstant
