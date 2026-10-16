module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.DirectionalBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentPeriodicity TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentDerivative
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.StageTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.RapidCuspDecay
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactCuspDecay

theorem chart_right_conjugate (argument : ℂ) (positive : 0 < argument.im) (right : BinaryRealGL) :
    (unit argument positive * right)⁻¹.val * generator * (unit argument positive * right).val =
      argument.im⁻¹ • conjugation right generator := by
  calc
    _ = conjugation right ((unit argument positive)⁻¹.val * generator * (unit argument positive).val) := by
      simp only [_root_.mul_inv_rev, Units.val_mul, conjugation_apply, mul_assoc]
    _ = _ := by rw [chart_conjugate, map_smul]

theorem norm_le_chart_right {degree : ℕ} (data : InducingData degree)
    (vector : data.cusp.smooth) (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (point : IntegralBinaryGL) (argument : ℂ) (positive : 0 < argument.im)
    (right : BinaryRealGL) (order : ℕ) :
    ‖data.cusp.realize vector (atFinite (GeneralLinearGroup.map integralEmbedding point) *
      atInfinity (unit argument positive * right))‖ ≤
        (3 / argument.im) ^ order * cuspSupNorm
          ((directionalOperator data.cusp (conjugation right generator)) ^ order $ vector) := by
  have bound := norm_le_iterate data vector fixed point (unit argument positive * right) order 0
  rw [chart_right_conjugate, LieDifferentiation.directionalOperator_real_smul] at bound
  simpa only [realFunction, unipotent_zero, one_mul, smul_pow, LinearMap.smul_apply,
    cuspSupNorm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive),
    div_eq_mul_inv, mul_pow, mul_assoc] using bound

theorem uniform_on_compact {degree : ℕ} (data : InducingData degree)
    (vector : data.cusp.smooth) (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (compactSet : Set BinaryRealGL) (compactness : IsCompact compactSet) (order : ℕ) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ right ∈ compactSet, ∀ point : IntegralBinaryGL,
      ∀ argument : ℂ, ∀ positive : 0 < argument.im,
      ‖data.cusp.realize vector (atFinite (GeneralLinearGroup.map integralEmbedding point) *
        atInfinity (unit argument positive * right))‖ ≤ (3 / argument.im) ^ order * bound := by
  have continuity : Continuous (fun right : BinaryRealGL => boundedRealization data.cusp
      ((directionalOperator data.cusp (conjugation right generator)) ^ order $ vector)) :=
    (DirectionalBounds.iterates_continuous data.cusp vector order).comp
      (conjugation_continuous.clm_apply continuous_const)
  obtain ⟨bound, boundProperty⟩ := compactness.exists_bound_of_continuousOn continuity.continuousOn
  refine ⟨max bound 0, le_max_right _ _, ?_⟩
  intro right membership point argument positive
  exact (norm_le_chart_right data vector fixed point argument positive right order).trans
    (mul_le_mul_of_nonneg_left ((boundProperty right membership).trans (le_max_left _ _))
      (pow_nonneg (div_nonneg (by norm_num) positive.le) _))

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CompactCuspDecay
