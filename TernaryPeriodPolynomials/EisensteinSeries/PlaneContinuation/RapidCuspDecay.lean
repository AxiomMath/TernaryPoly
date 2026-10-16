module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.UnipotentDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentPeriodicity TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentDerivative
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RapidCuspDecay

theorem norm_le_of_derivative_bound {degree : ℕ} (data : InducingData degree)
    (vector : data.cusp.smooth) (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : IntegralBinaryGL) (realPoint : BinaryRealGL) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (derivativeBound : ∀ parameter, ‖realFunction data.cusp
      (directionalOperator data.cusp (realPoint⁻¹.val * generator * realPoint.val) vector)
      point realPoint parameter‖ ≤ bound) (parameter : ℝ) :
    ‖realFunction data.cusp vector point realPoint parameter‖ ≤ 3 * bound :=
  MeanZeroBound.norm_le_of_deriv_bound _ _ bound nonnegative
    (realFunction_hasDerivAt data vector point realPoint) derivativeBound parameter
    (RealCuspidality.integral_period_zero data.cusp vector fixed point realPoint parameter)

theorem norm_le_iterate {degree : ℕ} (data : InducingData degree)
    (vector : data.cusp.smooth) (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : IntegralBinaryGL) (realPoint : BinaryRealGL) (order : ℕ) (parameter : ℝ) :
    ‖realFunction data.cusp vector point realPoint parameter‖ ≤
      3 ^ order * cuspSupNorm
        ((directionalOperator data.cusp (realPoint⁻¹.val * generator * realPoint.val)) ^ order $ vector) := by
  induction order generalizing vector parameter with
  | zero =>
      simpa only [pow_zero, Module.End.one_apply, one_mul, realFunction] using
        realize_le_cuspSupNorm vector
          (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding point) *
            atInfinity (binaryUnipotent parameter * realPoint))
  | succ order inductionHypothesis =>
      have bound := norm_le_of_derivative_bound data vector fixed point realPoint
        (3 ^ order * cuspSupNorm
          ((directionalOperator data.cusp (realPoint⁻¹.val * generator * realPoint.val)) ^ order $
            directionalOperator data.cusp (realPoint⁻¹.val * generator * realPoint.val) vector))
        (mul_nonneg (pow_nonneg (by norm_num) _) (cuspSupNorm_nonneg _))
        (fun parameter => inductionHypothesis _
          (directionalOperator_preserves_fixed data.cusp finiteCongruence _ vector fixed) parameter)
        parameter
      simpa only [pow_succ, Module.End.mul_apply, mul_assoc, mul_comm (3 : ℝ),
        mul_left_comm (3 : ℝ)] using bound

theorem chart_conjugate (argument : ℂ) (positive : 0 < argument.im) :
    (UpperTriangularChart.unit argument positive)⁻¹.val * generator *
        (UpperTriangularChart.unit argument positive).val = argument.im⁻¹ • generator := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [UpperTriangularChart.unit, UpperTriangularChart.matrix, generator,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem norm_le_chart {degree : ℕ} (data : InducingData degree)
    (vector : data.cusp.smooth) (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : IntegralBinaryGL) (argument : ℂ) (positive : 0 < argument.im) (order : ℕ) :
    ‖data.cusp.realize vector (atFinite (Matrix.GeneralLinearGroup.map integralEmbedding point) *
      atInfinity (UpperTriangularChart.unit argument positive))‖ ≤
        (3 / argument.im) ^ order * cuspSupNorm
          ((directionalOperator data.cusp generator) ^ order $ vector) := by
  have bound := norm_le_iterate data vector fixed point (UpperTriangularChart.unit argument positive) order 0
  rw [chart_conjugate, LieDifferentiation.directionalOperator_real_smul] at bound
  simpa only [realFunction, unipotent_zero, one_mul, smul_pow, LinearMap.smul_apply,
    cuspSupNorm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive),
    div_eq_mul_inv, mul_pow, mul_assoc] using bound

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RapidCuspDecay
