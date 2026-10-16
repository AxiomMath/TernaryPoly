module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.AbsoluteTheta

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspThetaDecay
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformAbsoluteTheta

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ChartAbsoluteDecay

theorem large {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameters : Set FiniteParameterThetaDecay.Parameter) (finiteCompact : IsCompact parameters)
    (point : GeneralLinearGroup (Fin 3) ℝ) (rightSet : Set BinaryRealGL) (rightCompact : IsCompact rightSet)
    (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter ∈ parameters, ∀ right ∈ rightSet,
      ∀ (finitePoint : IntegralBinaryGL) (argument : ℂ) (positive : 0 < argument.im),
        1 ≤ argument.im → |argument.re| ≤ 1 → ∀ scale : ℝ, 1 ≤ scale →
          scale ^ power * argument.im ^ cuspPower *
            (absoluteTail realTest finiteTest parameter (realTransform point (unit argument positive * right)).toContinuousLinearMap scale *
              ‖cuspValue data vector finitePoint right argument positive‖) ≤ constant := by
  obtain ⟨thetaConstant, thetaNonnegative, thetaBounded⟩ :=
    UniformAbsoluteTheta.uniform_large realTest finiteTest finiteContinuous finiteSupport parameters finiteCompact power
  obtain ⟨distortion, distortionNonnegative, operatorBounded⟩ := CompactChartOperators.bounds point rightSet rightCompact
  obtain ⟨cuspConstant, cuspNonnegative, cuspBounded⟩ := UniformCuspThetaDecay.weighted_cusp data vector fixed rightSet rightCompact cuspPower
  let order := power + Module.finrank ℤ integerLattice + 1
  let thetaBound := thetaConstant * distortion ^ order
  have thetaBoundNonnegative : 0 ≤ thetaBound := mul_nonneg thetaNonnegative (pow_nonneg distortionNonnegative _)
  refine ⟨thetaBound * cuspConstant, mul_nonneg thetaBoundNonnegative cuspNonnegative, ?_⟩
  intro parameter parameterMem right rightMem finitePoint argument positive height horizontal scale scaleLower
  let transform := realTransform point (unit argument positive * right)
  have thetaEstimate : scale ^ power * absoluteTail realTest finiteTest parameter transform.toContinuousLinearMap scale ≤ thetaBound :=
    (thetaBounded parameter parameterMem transform.toContinuousLinearMap _ (norm_nonneg _)
      (AdelicThetaDistortion.inverse_norm_bound transform) scale scaleLower).2.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (operatorBounded right rightMem argument positive height horizontal).2.1 order) thetaNonnegative)
  calc
    _ = (scale ^ power * absoluteTail realTest finiteTest parameter transform.toContinuousLinearMap scale) *
        (argument.im ^ cuspPower * ‖cuspValue data vector finitePoint right argument positive‖) := by ring
    _ ≤ thetaBound * cuspConstant :=
      mul_le_mul thetaEstimate (cuspBounded right rightMem finitePoint argument positive)
        (mul_nonneg (pow_nonneg positive.le _) (norm_nonneg _)) thetaBoundNonnegative

theorem small {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : Rectangular FiniteAdeles → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (parameters : Set FiniteParameterThetaDecay.Parameter) (finiteCompact : IsCompact parameters)
    (point : GeneralLinearGroup (Fin 3) ℝ) (rightSet : Set BinaryRealGL) (rightCompact : IsCompact rightSet)
    (cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ parameter ∈ parameters, ∀ right ∈ rightSet,
      ∀ (finitePoint : IntegralBinaryGL) (argument : ℂ) (positive : 0 < argument.im),
        1 ≤ argument.im → |argument.re| ≤ 1 → ∀ scale : ℝ, 0 < scale →
          scale ^ 7 * argument.im ^ cuspPower *
            (absoluteTail realTest finiteTest parameter (realTransform point (unit argument positive * right)).toContinuousLinearMap scale *
              ‖cuspValue data vector finitePoint right argument positive‖) ≤ constant := by
  obtain ⟨thetaConstant, thetaNonnegative, thetaBounded⟩ :=
    UniformAbsoluteTheta.uniform_small realTest finiteTest finiteContinuous finiteSupport parameters finiteCompact
  obtain ⟨distortion, distortionNonnegative, operatorBounded⟩ := CompactChartOperators.bounds point rightSet rightCompact
  obtain ⟨cuspConstant, cuspNonnegative, cuspBounded⟩ := UniformCuspThetaDecay.weighted_cusp data vector fixed rightSet rightCompact cuspPower
  let thetaBound := thetaConstant * distortion ^ 7
  have thetaBoundNonnegative : 0 ≤ thetaBound := mul_nonneg thetaNonnegative (pow_nonneg distortionNonnegative _)
  refine ⟨thetaBound * cuspConstant, mul_nonneg thetaBoundNonnegative cuspNonnegative, ?_⟩
  intro parameter parameterMem right rightMem finitePoint argument positive height horizontal scale scalePositive
  let transform := realTransform point (unit argument positive * right)
  have thetaEstimate : scale ^ 7 * absoluteTail realTest finiteTest parameter transform.toContinuousLinearMap scale ≤ thetaBound :=
    (thetaBounded parameter parameterMem transform scale scalePositive).2.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (operatorBounded right rightMem argument positive height horizontal).2.1 7) thetaNonnegative)
  calc
    _ = (scale ^ 7 * absoluteTail realTest finiteTest parameter transform.toContinuousLinearMap scale) *
        (argument.im ^ cuspPower * ‖cuspValue data vector finitePoint right argument positive‖) := by ring
    _ ≤ thetaBound * cuspConstant :=
      mul_le_mul thetaEstimate (cuspBounded right rightMem finitePoint argument positive)
        (mul_nonneg (pow_nonneg positive.le _) (norm_nonneg _)) thetaBoundNonnegative

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ChartAbsoluteDecay
