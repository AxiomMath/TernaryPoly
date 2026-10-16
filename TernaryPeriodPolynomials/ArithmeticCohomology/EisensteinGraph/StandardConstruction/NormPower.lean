module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Norms
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.NormPower

theorem normPower_mul_units (first second : Adelesˣ) (exponent : ℂ) :
    normPower (first * second) exponent = normPower first exponent * normPower second exponent := by
  have firstPositive : (0 : ℝ) < (adeleNorm first : ℝ) := adeleNorm_pos first
  have secondPositive : (0 : ℝ) < (adeleNorm second : ℝ) := adeleNorm_pos second
  simp only [normPower, map_mul, NNReal.coe_mul,
    Real.log_mul (ne_of_gt firstPositive) (ne_of_gt secondPositive),
    Complex.ofReal_add, mul_add, Complex.exp_add]

theorem normPower_norm (unit : Adelesˣ) (exponent : ℂ) :
    ‖normPower unit exponent‖ = (adeleNorm unit : ℝ) ^ exponent.re := by
  have positive : (0 : ℝ) < (adeleNorm unit : ℝ) := adeleNorm_pos unit
  rw [normPower, Complex.norm_exp, Real.rpow_def_of_pos positive]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_comm]

theorem normPower_add (unit : Adelesˣ) (first second : ℂ) :
    normPower unit (first + second) = normPower unit first * normPower unit second := by
  simp only [normPower, add_mul, Complex.exp_add]

theorem normPower_two (unit : Adelesˣ) :
    normPower unit 2 = ((adeleNorm unit : ℝ) : ℂ) ^ 2 := by
  have positive : (0 : ℝ) < (adeleNorm unit : ℝ) := adeleNorm_pos unit
  unfold normPower
  rw [show (2 : ℂ) = (2 : ℕ) by norm_num, Complex.exp_nat_mul,
    ← Complex.ofReal_exp, Real.exp_log positive]

theorem normPower_analytic (unit : Adelesˣ) (point : ℂ) :
    AnalyticAt ℂ (normPower unit) point := by
  exact (analyticAt_id.mul analyticAt_const).cexp

theorem rankOne_exponent (parameter : ℂ) :
    2 * inductionExponent .line parameter =
      -2 * inductionExponent .plane parameter + 2 := by
  simp only [inductionExponent]
  ring

theorem rankOne_factor (unit : Adelesˣ) (parameter : ℂ) :
    normPower unit (2 * inductionExponent .line parameter) =
      normPower unit (-2 * inductionExponent .plane parameter) *
        ((adeleNorm unit : ℝ) : ℂ) ^ 2 := by
  rw [rankOne_exponent, normPower_add, normPower_two]

theorem lineRankOne_analytic (unit : Adelesˣ) (point : ℂ) :
    AnalyticAt ℂ (fun parameter =>
      normPower unit (2 * inductionExponent .line parameter)) point := by
  unfold normPower inductionExponent
  exact ((analyticAt_const.mul (analyticAt_const.sub
    analyticAt_id.div_const)).mul analyticAt_const).cexp

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.NormPower
