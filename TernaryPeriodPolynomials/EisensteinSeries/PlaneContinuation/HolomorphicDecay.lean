module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.HighestWeightHolomorphic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.HighestWeightHolomorphic TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm
open Filter

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.HolomorphicDecay

theorem normalization_norm (weight : ℤ) (argument : ℂ) (positive : 0 < argument.im) :
    ‖normalization weight argument‖ = argument.im ^ (-(weight : ℝ) / 2) := by
  rw [normalization, Complex.norm_exp, Real.rpow_def_of_pos positive]
  congr 1
  simp only [Complex.mul_re, Complex.div_ofNat_re, Complex.neg_re, Complex.intCast_re,
    Complex.ofReal_re, Complex.div_ofNat_im, Complex.neg_im, Complex.intCast_im,
    Complex.ofReal_im, neg_zero, zero_div, mul_zero, sub_zero]
  ring

theorem function_norm_bound (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (weight : ℤ) (argument : ℂ) (positive : 0 < argument.im) :
    ‖function data point vector weight argument‖ ≤
      argument.im ^ (-(weight : ℝ) / 2) * cuspSupNorm vector := by
  rw [function, norm_mul, normalization_norm weight argument positive, raw_eq data point vector argument positive]
  exact mul_le_mul_of_nonneg_left (realize_le_cuspSupNorm vector _)
    (Real.rpow_nonneg positive.le _)

theorem normalization_nonzero (weight : ℤ) (argument : ℂ) : normalization weight argument ≠ 0 :=
  Complex.exp_ne_zero _

theorem function_eq_zero_iff (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (weight : ℤ) (argument : ℂ) :
    function data point vector weight argument = 0 ↔ raw data point vector argument = 0 := by
  rw [function, mul_eq_zero]
  exact or_iff_right (normalization_nonzero weight argument)

theorem isZeroAtImInfty (data : CuspidalRepresentation) (point : BinaryAdelicGL)
    (vector : data.smooth) (weight : ℤ) (weightPositive : 0 < weight) :
    UpperHalfPlane.IsZeroAtImInfty (fun argument : UpperHalfPlane => function data point vector weight argument) := by
  have imaginaryTendsto : Tendsto UpperHalfPlane.im UpperHalfPlane.atImInfty atTop := tendsto_comap
  have exponentPositive : 0 < (weight : ℝ) / 2 := by positivity
  have limit := ((tendsto_rpow_neg_atTop exponentPositive).comp imaginaryTendsto).mul_const (cuspSupNorm vector)
  apply squeeze_zero_norm' (Filter.Eventually.of_forall (fun argument : UpperHalfPlane =>
    function_norm_bound data point vector weight argument argument.im_pos))
  simp only [Function.comp_apply, zero_mul] at limit
  rw [neg_div]
  exact limit

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.HolomorphicDecay
