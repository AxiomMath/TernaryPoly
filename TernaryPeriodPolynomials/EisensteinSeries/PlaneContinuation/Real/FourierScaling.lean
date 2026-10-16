module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.AdelicPoisson

@[expose] public section


open MeasureTheory TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFourierScaling

def dilation (scale : ℝˣ) : RealSpace ≃L[ℝ] RealSpace := ContinuousLinearEquiv.smulLeft scale

def factor (scale : ℝˣ) : ℝ := |(scale.val ^ 6)⁻¹|

def dilate (function : SchwartzMap RealSpace ℂ) (scale : ℝˣ) : SchwartzMap RealSpace ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (dilation scale) function

theorem dilate_apply (function : SchwartzMap RealSpace ℂ) (scale : ℝˣ) (value : RealSpace) :
    dilate function scale value = function (scale.val • value) := rfl

theorem integral_scale (scale : ℝˣ) (function : RealSpace → ℂ) :
    (∫ value, function (scale.val • value)) = factor scale • ∫ value, function value := by
  have embedding : MeasurableEmbedding (fun value : RealSpace => scale.val • value) :=
    (dilation scale).toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have equality := embedding.integral_map (μ := volume) function
  rw [Measure.map_addHaar_smul volume scale.ne_zero, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _)] at equality
  have dimension : Module.finrank ℝ RealSpace = 6 := by simp [RealSpace, Coordinate]
  rw [dimension] at equality
  exact equality.symm

theorem scaled_inner (scale : ℝˣ) (value frequency : RealSpace) :
    inner ℝ (scale.val • value) (scale.inv • frequency) = inner ℝ value frequency := by
  rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, scale.val_inv, one_mul]

theorem fourier_integral (function : SchwartzMap RealSpace ℂ) (frequency : RealSpace) :
    FourierTransform.fourier function frequency =
      ∫ value, (Real.fourierChar (-inner ℝ value frequency) : ℂ) * function value := by
  have equality := congrFun (SchwartzMap.fourier_coe function) frequency
  rw [Real.fourier_eq] at equality
  exact equality

theorem fourier_dilate (function : SchwartzMap RealSpace ℂ) (scale : ℝˣ) (frequency : RealSpace) :
    FourierTransform.fourier (dilate function scale) frequency =
      factor scale • FourierTransform.fourier function (scale.inv • frequency) := by
  rw [fourier_integral, fourier_integral]
  have equality := integral_scale scale
    (fun value => (Real.fourierChar (-inner ℝ value (scale.inv • frequency)) : ℂ) * function value)
  rw [← equality]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro value
  dsimp only
  rw [scaled_inner, dilate_apply]

theorem factor_positive (scale : ℝˣ) : 0 < factor scale := by
  exact abs_pos.mpr (inv_ne_zero (pow_ne_zero _ scale.ne_zero))

theorem factor_of_positive (scale : ℝˣ) (positive : 0 < scale.val) : factor scale = scale.val⁻¹ ^ 6 := by
  rw [factor, abs_of_pos (inv_pos.mpr (pow_pos positive _)), inv_pow]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFourierScaling
