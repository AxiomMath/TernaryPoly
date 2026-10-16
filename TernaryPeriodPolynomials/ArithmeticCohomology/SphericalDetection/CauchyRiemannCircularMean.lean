module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.Rotations
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CompactDerivativeIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.CircleIntegral

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance CauchyRiemannCircularMean_measurableSpaceCircle : MeasurableSpace Circle := borel Circle
local instance CauchyRiemannCircularMean_borelSpaceCircle : BorelSpace Circle := ⟨rfl⟩

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def antiholomorphicDerivative (function : ℂ → E) (point : ℂ) : E :=
  fderiv ℝ function point 1 + Complex.I • fderiv ℝ function point Complex.I

def circularMean (function : ℂ → E) (center : ℂ) (radius : ℝ) : E :=
  ∫ angle : Circle, function (center + radius • (angle : ℂ)) ∂binaryRotationMeasure

theorem circularMean_zero (function : ℂ → E) (center : ℂ) : circularMean function center 0 = function center := by
  simp [circularMean]

omit [CompleteSpace E] in
theorem realLinear_cauchyRiemann_direction (linear : ℂ →L[ℝ] E) (direction : ℂ) :
    linear direction + Complex.I • linear (Complex.I * direction) =
      (starRingEnd ℂ) direction • (linear 1 + Complex.I • linear Complex.I) := by
  have split (value : ℂ) : linear value = value.re • linear 1 + value.im • linear Complex.I := by
    conv_lhs => rw [← Complex.re_add_im value]
    rw [map_add]
    congr 1
    · simpa only [Complex.real_smul, mul_one] using linear.map_smul value.re 1
    · simpa only [Complex.real_smul] using linear.map_smul value.im Complex.I
  have conjugate : (starRingEnd ℂ) direction = (direction.re : ℂ) - (direction.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [split direction, split (Complex.I * direction)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, zero_add, RCLike.real_smul_eq_coe_smul (K := ℂ), conjugate]
  simp only [smul_add, sub_smul, smul_smul, sub_mul, mul_assoc, Complex.I_mul_I, mul_neg_one]
  module

theorem circularMean_radial_hasDerivAt (function : ℂ → E) (regular : ContDiff ℝ 1 function)
    (center : ℂ) (radius : ℝ) :
    HasDerivAt (circularMean function center)
      (∫ angle : Circle, fderiv ℝ function (center + radius • (angle : ℂ)) (angle : ℂ) ∂binaryRotationMeasure) radius := by
  have point_continuous : Continuous (fun pair : ℝ × Circle => center + pair.1 • (pair.2 : ℂ)) := by fun_prop
  have derivative_continuous : Continuous (fderiv ℝ function) :=
    (contDiff_succ_iff_fderiv (n := 0) |>.mp regular).2.2.continuous
  apply hasDerivAt_integral_compact_parameter binaryRotationMeasure
    (fun radius angle => function (center + radius • (angle : ℂ)))
    (fun radius angle => fderiv ℝ function (center + radius • (angle : ℂ)) (angle : ℂ)) Set.univ isOpen_univ
  · exact (regular.continuous.comp point_continuous).continuousOn
  · exact ((derivative_continuous.comp point_continuous).clm_apply (by fun_prop)).continuousOn
  · intro parameter _ angle
    apply (regular.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt parameter
    simpa only [id_eq, one_smul] using (((hasDerivAt_id parameter).smul_const (angle : ℂ)).const_add center)
  · trivial

theorem circlePhase_hasDerivAt (parameter : ℝ) :
    HasDerivAt (fun parameter => (Circle.exp parameter : ℂ))
      ((Circle.exp parameter : ℂ) * Complex.I) parameter := by
  convert hasDerivAt_circleMap 0 1 parameter using 1
  · funext argument
    simp [circleMap, Circle.coe_exp]
  · simp [circleMap, Circle.coe_exp]

theorem circularMean_angular_integral_zero (function : ℂ → E) (regular : ContDiff ℝ 1 function)
    (center : ℂ) (radius : ℝ) (nonzero : radius ≠ 0) :
    (∫ angle : Circle, fderiv ℝ function (center + radius • (angle : ℂ))
      (Complex.I * (angle : ℂ)) ∂binaryRotationMeasure) = 0 := by
  let values : ℝ → Circle → E := fun parameter angle =>
    function (center + radius • ((Circle.exp parameter : ℂ) * (angle : ℂ)))
  let derivatives : ℝ → Circle → E := fun parameter angle =>
    fderiv ℝ function (center + radius • ((Circle.exp parameter : ℂ) * (angle : ℂ)))
      (radius • (((Circle.exp parameter : ℂ) * Complex.I) * (angle : ℂ)))
  have point_continuous : Continuous (fun pair : ℝ × Circle =>
      center + radius • ((Circle.exp pair.1 : ℂ) * (pair.2 : ℂ))) := by fun_prop
  have derivative_continuous : Continuous (fderiv ℝ function) :=
    (contDiff_succ_iff_fderiv (n := 0) |>.mp regular).2.2.continuous
  have derivative := hasDerivAt_integral_compact_parameter binaryRotationMeasure values derivatives Set.univ isOpen_univ
    ((regular.continuous.comp point_continuous).continuousOn)
    (((derivative_continuous.comp point_continuous).clm_apply (by fun_prop)).continuousOn)
    (fun parameter _ angle => (regular.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt parameter
      ((((circlePhase_hasDerivAt parameter).mul_const (angle : ℂ)).const_smul radius).const_add center))
    0 (Set.mem_univ _)
  have constant : (fun parameter => ∫ angle, values parameter angle ∂binaryRotationMeasure) =
      (fun _ : ℝ => circularMean function center radius) := by
    funext parameter
    exact integral_mul_left_eq_self (fun angle : Circle => function (center + radius • (angle : ℂ))) (Circle.exp parameter)
  rw [constant] at derivative
  have zero := derivative.unique (hasDerivAt_const 0 (circularMean function center radius))
  simp only [derivatives, Circle.coe_exp, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
    map_smul, integral_smul] at zero
  exact (smul_eq_zero.mp zero).resolve_left nonzero

theorem circularMean_hasDerivAt_of_cauchyRiemann (function : ℂ → E) (regular : ContDiff ℝ 1 function)
    (center : ℂ) (radius : ℝ) (nonzero : radius ≠ 0) :
    HasDerivAt (circularMean function center)
      (∫ angle : Circle, (starRingEnd ℂ) (angle : ℂ) • antiholomorphicDerivative function
        (center + radius • (angle : ℂ)) ∂binaryRotationMeasure) radius := by
  have derivative_continuous : Continuous (fderiv ℝ function) :=
    (contDiff_succ_iff_fderiv (n := 0) |>.mp regular).2.2.continuous
  have first : Integrable (fun angle : Circle =>
      fderiv ℝ function (center + radius • (angle : ℂ)) (angle : ℂ)) binaryRotationMeasure :=
    ((derivative_continuous.comp (by fun_prop)).clm_apply (by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have second : Integrable (fun angle : Circle =>
      Complex.I • fderiv ℝ function (center + radius • (angle : ℂ)) (Complex.I * (angle : ℂ))) binaryRotationMeasure :=
    (continuous_const.smul ((derivative_continuous.comp (by fun_prop)).clm_apply (by fun_prop))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have identity : (∫ angle : Circle, (starRingEnd ℂ) (angle : ℂ) • antiholomorphicDerivative function
        (center + radius • (angle : ℂ)) ∂binaryRotationMeasure) =
      ∫ angle : Circle, fderiv ℝ function (center + radius • (angle : ℂ)) (angle : ℂ) ∂binaryRotationMeasure := by
    simp_rw [antiholomorphicDerivative, ← realLinear_cauchyRiemann_direction]
    rw [integral_add first second, integral_smul, circularMean_angular_integral_zero function regular center radius nonzero,
      smul_zero, add_zero]
  rw [identity]
  exact circularMean_radial_hasDerivAt function regular center radius

omit [CompleteSpace E] in
theorem antiholomorphicDerivative_continuous (function : ℂ → E) (regular : ContDiff ℝ 1 function) :
    Continuous (antiholomorphicDerivative function) := by
  have derivative_continuous : Continuous (fderiv ℝ function) :=
    (contDiff_succ_iff_fderiv (n := 0) |>.mp regular).2.2.continuous
  exact (derivative_continuous.clm_apply continuous_const).add
    (continuous_const.smul (derivative_continuous.clm_apply continuous_const))

omit [CompleteSpace E] in
theorem circularMean_correction_continuous (function : ℂ → E) (regular : ContDiff ℝ 1 function) (center : ℂ) :
    Continuous (fun radius : ℝ => ∫ angle : Circle, (starRingEnd ℂ) (angle : ℂ) •
      antiholomorphicDerivative function (center + radius • (angle : ℂ)) ∂binaryRotationMeasure) := by
  have integrand : Continuous (fun pair : ℝ × Circle => (starRingEnd ℂ) (pair.2 : ℂ) •
      antiholomorphicDerivative function (center + pair.1 • (pair.2 : ℂ))) :=
    (show Continuous (fun pair : ℝ × Circle => (starRingEnd ℂ) (pair.2 : ℂ)) by fun_prop).smul
      ((antiholomorphicDerivative_continuous function regular).comp (by fun_prop))
  simpa only [Measure.restrict_univ] using
    continuous_parametric_integral_of_continuous (μ := binaryRotationMeasure) integrand isCompact_univ

theorem circularMean_sub_eq_integral (function : ℂ → E) (regular : ContDiff ℝ 1 function)
    (center : ℂ) (radius : ℝ) (nonnegative : 0 ≤ radius) :
    circularMean function center radius - function center =
      ∫ radial in 0..radius, ∫ angle : Circle, (starRingEnd ℂ) (angle : ℂ) •
        antiholomorphicDerivative function (center + radial • (angle : ℂ)) ∂binaryRotationMeasure := by
  have mean_continuous : Continuous (circularMean function center) :=
    Differentiable.continuous (fun parameter =>
      (circularMean_radial_hasDerivAt function regular center parameter).differentiableAt)
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le nonnegative mean_continuous.continuousOn
    (fun parameter member => circularMean_hasDerivAt_of_cauchyRiemann function regular center parameter (ne_of_gt member.1))
    ((circularMean_correction_continuous function regular center).intervalIntegrable 0 radius)
  rw [circularMean_zero] at identity
  exact identity.symm

omit [CompleteSpace E] in
theorem antiholomorphicDerivative_affine (function : ℂ → E) (center direction point : ℂ)
    (regular : DifferentiableAt ℝ function (center + direction * point)) :
    antiholomorphicDerivative (fun argument => function (center + direction * argument)) point =
      (starRingEnd ℂ) direction • antiholomorphicDerivative function (center + direction * point) := by
  let linear : ℂ →L[ℝ] ℂ := ((direction • (ContinuousLinearMap.id ℂ ℂ)).restrictScalars ℝ)
  have affine : HasFDerivAt (fun argument : ℂ => center + direction * argument) linear point := by
    exact linear.hasFDerivAt.const_add center
  have derivative := (regular.hasFDerivAt.comp point affine).fderiv
  simp only [Function.comp_def] at derivative
  unfold antiholomorphicDerivative
  rw [derivative]
  change fderiv ℝ function (center + direction * point) (direction * 1) +
    Complex.I • fderiv ℝ function (center + direction * point) (direction * Complex.I) = _
  rw [mul_one, mul_comm direction Complex.I]
  exact realLinear_cauchyRiemann_direction _ direction

theorem circularMean_affine_sub_eq_integral (function : ℂ → E) (regular : ContDiff ℝ 1 function)
    (center direction : ℂ) :
    (∫ angle : Circle, function (center + direction * (angle : ℂ)) ∂binaryRotationMeasure) - function center =
      ∫ radial in (0 : ℝ)..1, ∫ angle : Circle,
        (starRingEnd ℂ) (direction * (angle : ℂ)) •
          antiholomorphicDerivative function (center + radial • (direction * (angle : ℂ))) ∂binaryRotationMeasure := by
  have affine_regular : ContDiff ℝ 1 (fun argument => function (center + direction * argument)) :=
    regular.comp (by fun_prop)
  have identity := circularMean_sub_eq_integral _ affine_regular 0 1 (by norm_num)
  simp only [circularMean, zero_add, one_smul, mul_zero, add_zero] at identity
  rw [identity]
  apply intervalIntegral.integral_congr
  intro radial _
  apply integral_congr_ae
  filter_upwards [] with angle
  rw [antiholomorphicDerivative_affine function center direction _ (regular.differentiable (by norm_num) _), smul_smul]
  congr 1
  · rw [map_mul, mul_comm]
  · congr 1
    simp only [Complex.real_smul]
    ring

end TernaryPeriodPolynomials.SphericalDetection.Helpers
