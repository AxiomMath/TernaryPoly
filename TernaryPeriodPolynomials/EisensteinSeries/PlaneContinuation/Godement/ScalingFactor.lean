module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Schwartz.Regularization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementRealScaling

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementScalingFactor

theorem determinant_norm (scale : ℝˣ) :
    (adeleNorm (GeneralLinearGroup.det (scalar scale)) : ℝ) = scale.val ^ 2 := by
  rw [GodementRealScaling.scalar, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.det_atInfinity, GeneralLinearGroup.det_scalar, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Norm.adeleNorm_real]
  change |scale.val ^ 2| = scale.val ^ 2
  exact abs_of_nonneg (sq_nonneg _)

theorem multiplier_differentiable {degree : ℕ} (data : InducingData degree) (scale : ℝˣ) :
    Differentiable ℂ (multiplier data scale) := by
  have equality : (fun parameter => GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det (scalar scale))) =
      fun parameter => GodementIntegral.innerCharacter data 0 (GeneralLinearGroup.det (scalar scale)) *
        Complex.exp (parameter * (Real.log (adeleNorm (GeneralLinearGroup.det (scalar scale)) : ℝ) : ℂ)) :=
    funext (fun parameter => LargeThetaIntegral.character_factor data parameter _)
  have differentiable : Differentiable ℂ
      (fun parameter => GodementIntegral.innerCharacter data parameter (GeneralLinearGroup.det (scalar scale))) := by
    rw [equality]
    fun_prop
  apply differentiable.inv
  intro parameter
  apply norm_pos_iff.mp
  rw [WeightedAbsoluteTheta.inner_norm]
  exact Real.exp_pos _

theorem multiplier_norm {degree : ℕ} (data : InducingData degree) (parameter : ℂ) :
    ‖multiplier data SchwartzRegularization.scale parameter‖ =
      Real.exp (-2 * WeightedAbsoluteTheta.exponent degree parameter * Real.log 2) := by
  rw [multiplier, norm_inv, WeightedAbsoluteTheta.inner_norm, determinant_norm]
  change (Real.exp (WeightedAbsoluteTheta.exponent degree parameter * Real.log ((2 : ℝ) ^ 2)))⁻¹ = _
  rw [Real.log_pow, ← Real.exp_neg]
  congr 1
  ring

theorem multiplier_norm_bound {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) :
    ‖multiplier data SchwartzRegularization.scale parameter‖ < 1 / 64 := by
  have exponentBound := (RawGodementIntegrability.halfPlane_iff degree parameter).mpr halfPlane
  have positive : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have expIdentity : Real.exp (-6 * Real.log 2) = 1 / 64 := by
    have sixth : Real.exp (6 * Real.log 2) = (64 : ℝ) := by
      calc
        _ = Real.exp (Real.log 2) ^ 6 := Real.exp_nat_mul (Real.log 2) 6
        _ = 64 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
    rw [neg_mul, Real.exp_neg, sixth]
    norm_num
  rw [multiplier_norm, ← expIdentity]
  apply Real.exp_lt_exp.mpr
  nlinarith

def regularizationFactor {degree : ℕ} (data : InducingData degree) (parameter : ℂ) : ℂ :=
  (1 - multiplier data SchwartzRegularization.scale parameter) *
    (1 - 64 * multiplier data SchwartzRegularization.scale parameter)

theorem factor_differentiable {degree : ℕ} (data : InducingData degree) : Differentiable ℂ (regularizationFactor data) := by
  have differentiable := multiplier_differentiable data SchwartzRegularization.scale
  unfold regularizationFactor
  fun_prop

theorem factor_nonzero {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (halfPlane : (1 - (degree : ℝ)) / 2 < parameter.re) : regularizationFactor data parameter ≠ 0 := by
  have bound := multiplier_norm_bound data parameter halfPlane
  apply mul_ne_zero
  · intro equality
    have normEquality := congrArg norm (sub_eq_zero.mp equality)
    rw [norm_one] at normEquality
    linarith
  · intro equality
    have normEquality := congrArg norm (sub_eq_zero.mp equality)
    norm_num [norm_mul] at normEquality
    linarith

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementScalingFactor
