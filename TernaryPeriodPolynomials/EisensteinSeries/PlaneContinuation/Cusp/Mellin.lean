module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.MellinProfile
public import Mathlib.Analysis.MellinTransform

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspMellinProfile TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.StageTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentDerivative
open Filter Asymptotics MeasureTheory
open scoped Topology Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspMellin

theorem profile_bound {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : IntegralBinaryGL) (right : BinaryRealGL) (height : ℝ) (positive : 0 < height) (order : ℕ) :
    ‖profile data.cusp vector point right height‖ ≤
      (3 ^ order * cuspSupNorm ((directionalOperator data.cusp (conjugation right generator)) ^ order $ vector)) *
        (height ^ order)⁻¹ := by
  rw [profile_eq data.cusp vector point right height positive]
  have bound := CompactCuspDecay.norm_le_chart_right data vector fixed point
    (Complex.I * height) (by simpa using positive) right order
  have numerical : (3 / height) ^ order *
      cuspSupNorm ((directionalOperator data.cusp (conjugation right generator)) ^ order $ vector) =
      (3 ^ order * cuspSupNorm ((directionalOperator data.cusp (conjugation right generator)) ^ order $ vector)) *
        (height ^ order)⁻¹ := by
    rw [div_pow, div_eq_mul_inv]
    ring
  simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, zero_add, numerical, heightUnit] using bound

theorem profile_inverse_bound {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : IntegralBinaryGL) (right : BinaryRealGL) (height : ℝ) (positive : 0 < height) (order : ℕ) :
    ‖profile data.cusp vector point right height‖ ≤
      (3 ^ order * cuspSupNorm
        ((directionalOperator data.cusp (conjugation (reflection * right) generator)) ^ order $ vector)) *
          height ^ order := by
  rw [profile_inversion data vector point right height positive]
  simpa only [inv_pow, inv_inv] using
    profile_bound data vector fixed (reflection * point) (reflection * right) height⁻¹ (inv_pos.mpr positive) order

theorem decay_atTop {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : IntegralBinaryGL) (right : BinaryRealGL) (order : ℕ) :
    profile data.cusp vector point right =O[atTop] (fun height : ℝ => height ^ (-(order : ℝ))) := by
  refine isBigO_iff.mpr ⟨3 ^ order * cuspSupNorm
    ((directionalOperator data.cusp (conjugation right generator)) ^ order $ vector), ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with height positive
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg positive.le _),
    Real.rpow_neg positive.le, Real.rpow_natCast]
  exact profile_bound data vector fixed point right height positive order

theorem decay_atZero {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : IntegralBinaryGL) (right : BinaryRealGL) (order : ℕ) :
    profile data.cusp vector point right =O[𝓝[>] 0] (fun height : ℝ => height ^ (order : ℝ)) := by
  refine isBigO_iff.mpr ⟨3 ^ order * cuspSupNorm
    ((directionalOperator data.cusp (conjugation (reflection * right) generator)) ^ order $ vector), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with height positive
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt positive) _), Real.rpow_natCast]
  exact profile_inverse_bound data vector fixed point right height positive order

theorem convergent {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : IntegralBinaryGL) (right : BinaryRealGL) (parameter : ℂ) :
    MellinConvergent (profile data.cusp vector point right) parameter := by
  obtain ⟨order, greater⟩ := exists_nat_gt |parameter.re|
  apply mellinConvergent_of_isBigO_rpow
    ((profile_continuousOn data.cusp vector point right).locallyIntegrableOn measurableSet_Ioi)
    (decay_atTop data vector fixed point right order) ((le_abs_self _).trans_lt greater)
    (b := -(order : ℝ))
  · simpa only [neg_neg] using decay_atZero data vector fixed point right order
  · linarith [neg_abs_le parameter.re]

theorem differentiable {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : IntegralBinaryGL) (right : BinaryRealGL) :
    Differentiable ℂ (mellin (profile data.cusp vector point right)) := by
  intro parameter
  obtain ⟨order, greater⟩ := exists_nat_gt |parameter.re|
  apply mellin_differentiableAt_of_isBigO_rpow
    ((profile_continuousOn data.cusp vector point right).locallyIntegrableOn measurableSet_Ioi)
    (decay_atTop data vector fixed point right order) ((le_abs_self _).trans_lt greater)
    (b := -(order : ℝ))
  · simpa only [neg_neg] using decay_atZero data vector fixed point right order
  · linarith [neg_abs_le parameter.re]

theorem analytic {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : IntegralBinaryGL) (right : BinaryRealGL) (parameter : ℂ) :
    AnalyticAt ℂ (mellin (profile data.cusp vector point right)) parameter :=
  (differentiable data vector fixed point right).analyticAt parameter

theorem functional_equation {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (point : IntegralBinaryGL) (right : BinaryRealGL) (parameter : ℂ) :
    mellin (profile data.cusp vector point right) parameter =
      mellin (profile data.cusp vector (reflection * point) (reflection * right)) (-parameter) := by
  rw [← mellin_comp_inv]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with height positive
  rw [profile_inversion data vector point right height positive]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspMellin
