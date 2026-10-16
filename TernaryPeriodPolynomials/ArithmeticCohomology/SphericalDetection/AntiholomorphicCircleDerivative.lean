module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.DiskMean

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance antiholomorphicCircleMeasurable : MeasurableSpace Circle := borel Circle
local instance antiholomorphicCircleBorel : BorelSpace Circle := ⟨rfl⟩

theorem realLinear_complex_decomposition (linear : ℂ →L[ℝ] ℂ) (point : ℂ) :
    linear point = ((linear 1 - Complex.I * linear Complex.I) / 2) * point +
      ((linear 1 + Complex.I * linear Complex.I) / 2) * (starRingEnd ℂ) point := by
  have split : linear point = point.re • linear 1 + point.im • linear Complex.I := by
    conv_lhs => rw [← Complex.re_add_im point]
    rw [map_add]
    congr 1
    · simpa only [Complex.real_smul, mul_one] using linear.map_smul point.re 1
    · simpa only [Complex.real_smul] using linear.map_smul point.im Complex.I
  rw [split]
  apply Complex.ext <;>
    simp [Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring

theorem circle_integral_antilinear_part (linear : ℂ →L[ℝ] ℂ) :
    (∫ angle : Circle, (angle : ℂ) ^ (-2 : ℤ) * linear ((angle : ℂ) ^ (-2 : ℤ))
      ∂binaryRotationMeasure) = (linear 1 + Complex.I * linear Complex.I) / 2 := by
  let first := (linear 1 - Complex.I * linear Complex.I) / 2
  let second := (linear 1 + Complex.I * linear Complex.I) / 2
  have formula (angle : Circle) :
      (angle : ℂ) ^ (-2 : ℤ) * linear ((angle : ℂ) ^ (-2 : ℤ)) =
        first * (angle : ℂ) ^ (-4 : ℤ) + second := by
    rw [realLinear_complex_decomposition]
    have square : (angle : ℂ) ^ (-2 : ℤ) * (angle : ℂ) ^ (-2 : ℤ) = (angle : ℂ) ^ (-4 : ℤ) := by
      rw [← zpow_add₀ (Circle.coe_ne_zero angle)]
      norm_num
    have conjugate : (angle : ℂ) ^ (-2 : ℤ) * (starRingEnd ℂ) ((angle : ℂ) ^ (-2 : ℤ)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_zpow, Circle.norm_coe, one_zpow]
      norm_num
    change _ = first * (angle : ℂ) ^ (-4 : ℤ) + second
    linear_combination first * square + second * conjugate
  simp only [formula]
  have integrable : Integrable (fun angle : Circle => first * (angle : ℂ) ^ (-4 : ℤ)) binaryRotationMeasure :=
    (continuous_const.mul (circleCharacter_continuous _)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_add integrable (integrable_const _), integral_const_mul, circleCharacter_integral]
  simp only [show (-4 : ℤ) ≠ 0 by decide, ite_false, mul_zero, zero_add,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rfl

theorem antiholomorphic_circleMean_hasDerivAt (function : ℂ → ℂ)
    (regular : ContDiffOn ℝ 1 function (Metric.ball 0 1)) :
    HasDerivAt (fun parameter : ℝ => ∫ angle : Circle,
      (angle : ℂ) ^ (-2 : ℤ) * function (parameter • (angle : ℂ) ^ (-2 : ℤ)) ∂binaryRotationMeasure)
      ((fderiv ℝ function 0 1 + Complex.I * fderiv ℝ function 0 Complex.I) / 2) 0 := by
  let location : ℝ × Circle → ℂ := fun point => point.1 • (point.2 : ℂ) ^ (-2 : ℤ)
  have phase_continuous : Continuous (fun point : ℝ × Circle => (point.2 : ℂ) ^ (-2 : ℤ)) :=
    (circleCharacter_continuous _).comp continuous_snd
  have location_continuous : Continuous location := continuous_fst.smul phase_continuous
  have location_inside : Set.MapsTo location (Metric.ball (0 : ℝ) 1 ×ˢ Set.univ) (Metric.ball (0 : ℂ) 1) := by
    intro point member
    simpa only [location, Metric.mem_ball, dist_zero_right, norm_smul, norm_zpow,
      Circle.norm_coe, one_zpow, mul_one] using member.1
  have derivative_continuous := regular.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
  have values_continuous := phase_continuous.continuousOn.mul
    (regular.continuousOn.comp location_continuous.continuousOn location_inside)
  have derivatives_continuous := phase_continuous.continuousOn.mul
    ((derivative_continuous.comp location_continuous.continuousOn location_inside).clm_apply
      phase_continuous.continuousOn)
  have derivative := hasDerivAt_integral_compact_parameter binaryRotationMeasure
    (fun parameter angle => (angle : ℂ) ^ (-2 : ℤ) * function (parameter • (angle : ℂ) ^ (-2 : ℤ)))
    (fun parameter angle => (angle : ℂ) ^ (-2 : ℤ) *
      fderiv ℝ function (parameter • (angle : ℂ) ^ (-2 : ℤ)) ((angle : ℂ) ^ (-2 : ℤ)))
    (Metric.ball 0 1) Metric.isOpen_ball values_continuous derivatives_continuous (by
      intro parameter member angle
      have argument_inside := location_inside (show (parameter, angle) ∈ Metric.ball (0 : ℝ) 1 ×ˢ Set.univ
        from ⟨member, Set.mem_univ _⟩)
      have at_argument := (regular.differentiableOn (by norm_num)).differentiableAt
        (Metric.isOpen_ball.mem_nhds argument_inside)
      simpa only [Function.comp_apply, location, id_eq, one_smul] using
        (at_argument.hasFDerivAt.comp_hasDerivAt parameter
          ((hasDerivAt_id parameter).smul_const ((angle : ℂ) ^ (-2 : ℤ)))).const_mul ((angle : ℂ) ^ (-2 : ℤ)))
    0 (by simp)
  simpa only [zero_smul, circle_integral_antilinear_part] using derivative

theorem differentiableAt_complex_of_antiholomorphic_circleMean_zero (function : ℂ → ℂ)
    (regular : ContDiffOn ℝ 1 function (Metric.ball 0 1))
    (mean_zero : ∀ᶠ point : ℂ in nhds 0,
      (∫ angle : Circle, (angle : ℂ) ^ (-2 : ℤ) * function ((angle : ℂ) ^ (-2 : ℤ) * point)
        ∂binaryRotationMeasure) = 0) :
    DifferentiableAt ℂ function 0 := by
  have real_mean_zero : (fun parameter : ℝ => ∫ angle : Circle, (angle : ℂ) ^ (-2 : ℤ) *
      function (parameter • (angle : ℂ) ^ (-2 : ℤ)) ∂binaryRotationMeasure) =ᶠ[nhds 0] 0 := by
    have restriction : Filter.Tendsto (fun parameter : ℝ => (parameter : ℂ)) (nhds 0) (nhds 0) :=
      Complex.continuous_ofReal.tendsto 0
    have restricted := restriction.eventually mean_zero
    filter_upwards [restricted] with parameter vanishes
    simpa only [Complex.real_smul, mul_comm (parameter : ℂ), Pi.zero_apply] using vanishes
  have derivative := antiholomorphic_circleMean_hasDerivAt function regular
  have zero_derivative := derivative.unique
    ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq real_mean_zero)
  have cauchy_riemann : fderiv ℝ function 0 1 + Complex.I * fderiv ℝ function 0 Complex.I = 0 :=
    (div_eq_zero_iff).mp zero_derivative |>.resolve_right (by norm_num)
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  refine ⟨(regular.differentiableOn (by norm_num)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simp)), ?_⟩
  have rotated := congrArg (fun value : ℂ => Complex.I * value) cauchy_riemann
  simp only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul, mul_zero] at rotated
  linear_combination -rotated

end TernaryPeriodPolynomials.SphericalDetection.Helpers
