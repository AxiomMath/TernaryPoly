module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Compact.ChartOperators

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDecay TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDistortion TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFourierLinear
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspThetaDecay
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformCuspThetaDecay

theorem weighted_cusp {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (rightSet : Set BinaryRealGL) (compact : IsCompact rightSet) (order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ right ∈ rightSet, ∀ (finitePoint : IntegralBinaryGL)
      (argument : ℂ) (positive : 0 < argument.im),
        argument.im ^ order * ‖cuspValue data vector finitePoint right argument positive‖ ≤ constant := by
  obtain ⟨constant, nonnegative, bounded⟩ := CompactCuspDecay.uniform_on_compact data vector fixed rightSet compact order
  refine ⟨3 ^ order * constant, mul_nonneg (pow_nonneg (by norm_num) _) nonnegative, ?_⟩
  intro right membership finitePoint argument positive
  have bound := mul_le_mul_of_nonneg_left (bounded right membership finitePoint argument positive) (pow_nonneg positive.le order)
  have cancellation : argument.im ^ order * (3 / argument.im) ^ order = 3 ^ order := by
    rw [← mul_pow, mul_div_cancel₀ 3 positive.ne']
  simpa only [← mul_assoc, cancellation, cuspValue] using bound

theorem large {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (latticeScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (parameters : Set FiniteParameterThetaDecay.Parameter) (finiteCompact : IsCompact parameters)
    (point : GeneralLinearGroup (Fin 3) ℝ) (rightSet : Set BinaryRealGL) (rightCompact : IsCompact rightSet)
    (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter ∈ parameters, ∀ right ∈ rightSet,
      ∀ (finitePoint : IntegralBinaryGL) (argument : ℂ) (positive : 0 < argument.im),
        1 ≤ argument.im → |argument.re| ≤ 1 → ∀ scale : ℝ, 1 ≤ scale →
          scale ^ power * argument.im ^ cuspPower *
            ‖(theta (pullback realTest (realTransform point (unit argument positive * right)))
              (FiniteFourierUniform.test latticeScale offset parameter) scale -
              realTest 0 * FiniteFourierUniform.test latticeScale offset parameter 0) *
                cuspValue data vector finitePoint right argument positive‖ ≤ constant := by
  obtain ⟨thetaConstant, thetaNonnegative, thetaBounded⟩ :=
    UniformThetaDistortion.large_boxes realTest latticeScale offset parameters finiteCompact power
  obtain ⟨distortion, distortionNonnegative, operatorBounded⟩ := CompactChartOperators.bounds point rightSet rightCompact
  obtain ⟨cuspConstant, cuspNonnegative, cuspBounded⟩ := weighted_cusp data vector fixed rightSet rightCompact cuspPower
  let order := power + Module.finrank ℤ integerLattice + 1
  let thetaBound := thetaConstant * distortion ^ order
  have thetaBoundNonnegative : 0 ≤ thetaBound := mul_nonneg thetaNonnegative (pow_nonneg distortionNonnegative _)
  refine ⟨thetaBound * cuspConstant, mul_nonneg thetaBoundNonnegative cuspNonnegative, ?_⟩
  intro parameter parameterMem right rightMem finitePoint argument positive height horizontal scale scaleLower
  let transform := realTransform point (unit argument positive * right)
  let finiteTest := FiniteFourierUniform.test latticeScale offset parameter
  have thetaEstimate : scale ^ power * ‖theta (pullback realTest transform) finiteTest scale - realTest 0 * finiteTest 0‖ ≤ thetaBound :=
    (thetaBounded parameter parameterMem transform scale scaleLower).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (operatorBounded right rightMem argument positive height horizontal).2.1 order) thetaNonnegative)
  calc
    _ = (scale ^ power * ‖theta (pullback realTest transform) finiteTest scale - realTest 0 * finiteTest 0‖) *
        (argument.im ^ cuspPower * ‖cuspValue data vector finitePoint right argument positive‖) := by rw [norm_mul]; ring
    _ ≤ thetaBound * cuspConstant :=
      mul_le_mul thetaEstimate (cuspBounded right rightMem finitePoint argument positive)
        (mul_nonneg (pow_nonneg positive.le _) (norm_nonneg _)) thetaBoundNonnegative

theorem small {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (latticeScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (parameters : Set FiniteParameterThetaDecay.Parameter) (finiteCompact : IsCompact parameters)
    (point : GeneralLinearGroup (Fin 3) ℝ) (rightSet : Set BinaryRealGL) (rightCompact : IsCompact rightSet)
    (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter ∈ parameters, ∀ right ∈ rightSet,
      ∀ (finitePoint : IntegralBinaryGL) (argument : ℂ) (positive : 0 < argument.im),
        1 ≤ argument.im → |argument.re| ≤ 1 → ∀ scale : ℝ, 0 < scale → scale ≤ 1 →
          scale⁻¹ ^ power * argument.im ^ cuspPower *
            ‖(theta (pullback realTest (realTransform point (unit argument positive * right)))
              (FiniteFourierUniform.test latticeScale offset parameter) scale -
              ((scale⁻¹ ^ 6 * factor (realTransform point (unit argument positive * right)) : ℝ) : ℂ) *
                (FourierTransform.fourier realTest 0 *
                  FiniteRectangularFourier.transform (FiniteFourierUniform.test latticeScale offset parameter) 0)) *
                    cuspValue data vector finitePoint right argument positive‖ ≤ constant := by
  obtain ⟨thetaConstant, thetaNonnegative, thetaBounded⟩ :=
    UniformThetaDistortion.small_boxes realTest latticeScale offset parameters finiteCompact power
  obtain ⟨distortion, distortionNonnegative, operatorBounded⟩ := CompactChartOperators.bounds point rightSet rightCompact
  let order := power + 6 + Module.finrank ℤ integerLattice + 1
  obtain ⟨cuspConstant, cuspNonnegative, cuspBounded⟩ := weighted_cusp data vector fixed rightSet rightCompact (cuspPower + order)
  let thetaBound := thetaConstant * distortion * distortion ^ order
  have thetaBoundNonnegative : 0 ≤ thetaBound :=
    mul_nonneg (mul_nonneg thetaNonnegative distortionNonnegative) (pow_nonneg distortionNonnegative _)
  refine ⟨thetaBound * cuspConstant, mul_nonneg thetaBoundNonnegative cuspNonnegative, ?_⟩
  intro parameter parameterMem right rightMem finitePoint argument positive height horizontal scale scalePositive scaleUpper
  let transform := realTransform point (unit argument positive * right)
  let finiteTest := FiniteFourierUniform.test latticeScale offset parameter
  let remainder := theta (pullback realTest transform) finiteTest scale - ((scale⁻¹ ^ 6 * factor transform : ℝ) : ℂ) *
    (FourierTransform.fourier realTest 0 * FiniteRectangularFourier.transform finiteTest 0)
  have thetaEstimate : scale⁻¹ ^ power * ‖remainder‖ ≤ thetaBound * argument.im ^ order := by
    apply (thetaBounded parameter parameterMem transform scale scalePositive scaleUpper).trans
    calc
      _ ≤ (thetaConstant * distortion) * (distortion * argument.im) ^ order :=
        mul_le_mul (mul_le_mul_of_nonneg_left (operatorBounded right rightMem argument positive height horizontal).2.2 thetaNonnegative)
          (pow_le_pow_left₀ (norm_nonneg _) (operatorBounded right rightMem argument positive height horizontal).1 order)
          (pow_nonneg (norm_nonneg _) _) (mul_nonneg thetaNonnegative distortionNonnegative)
      _ = thetaBound * argument.im ^ order := by rw [mul_pow]; exact (mul_assoc _ _ _).symm
  calc
    _ = (scale⁻¹ ^ power * ‖remainder‖) *
        (argument.im ^ cuspPower * ‖cuspValue data vector finitePoint right argument positive‖) := by rw [norm_mul]; ring
    _ ≤ (thetaBound * argument.im ^ order) *
        (argument.im ^ cuspPower * ‖cuspValue data vector finitePoint right argument positive‖) :=
      mul_le_mul_of_nonneg_right thetaEstimate (mul_nonneg (pow_nonneg positive.le _) (norm_nonneg _))
    _ = thetaBound * (argument.im ^ (cuspPower + order) * ‖cuspValue data vector finitePoint right argument positive‖) := by
      rw [pow_add]; ring
    _ ≤ thetaBound * cuspConstant := mul_le_mul_of_nonneg_left (cuspBounded right rightMem finitePoint argument positive) thetaBoundNonnegative

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformCuspThetaDecay
