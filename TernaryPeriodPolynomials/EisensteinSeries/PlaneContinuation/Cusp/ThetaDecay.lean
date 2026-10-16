module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.ChartOperators

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDecay TernaryPeriodPolynomials.PlaneEisensteinContinuation.AdelicThetaDistortion TernaryPeriodPolynomials.PlaneEisensteinContinuation.RealFourierLinear
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspSupNorm TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.StageTranslation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.UnipotentDerivative
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspThetaDecay

def cuspValue {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (finitePoint : IntegralBinaryGL) (right : BinaryRealGL) (argument : ℂ) (positive : 0 < argument.im) : ℂ :=
  data.cusp.realize vector (atFinite (GeneralLinearGroup.map integralEmbedding finitePoint) *
    atInfinity (unit argument positive * right))

def cuspConstant {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (right : BinaryRealGL) (order : ℕ) : ℝ :=
  3 ^ order * cuspSupNorm ((directionalOperator data.cusp (conjugation right generator)) ^ order $ vector)

theorem cuspConstant_nonnegative {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (right : BinaryRealGL) (order : ℕ) : 0 ≤ cuspConstant data vector right order :=
  mul_nonneg (pow_nonneg (by norm_num) _) (cuspSupNorm_nonneg _)

theorem weighted_cusp {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (finitePoint : IntegralBinaryGL) (right : BinaryRealGL) (argument : ℂ) (positive : 0 < argument.im) (order : ℕ) :
    argument.im ^ order * ‖cuspValue data vector finitePoint right argument positive‖ ≤
      cuspConstant data vector right order := by
  have bounded := mul_le_mul_of_nonneg_left
    (CompactCuspDecay.norm_le_chart_right data vector fixed finitePoint argument positive right order)
    (pow_nonneg positive.le order)
  have cancellation : argument.im ^ order * (3 / argument.im) ^ order = 3 ^ order := by
    rw [← mul_pow, mul_div_cancel₀ 3 positive.ne']
  simpa only [mul_assoc, ← mul_assoc (argument.im ^ order), cancellation, cuspValue, cuspConstant] using bounded

theorem rapid_large {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (finiteTest : FiniteRectangularFourier.Space → ℂ)
    (finiteContinuous : Continuous finiteTest) (finiteSupport : HasCompactSupport finiteTest)
    (point : GeneralLinearGroup (Fin 3) ℝ) (right : BinaryRealGL) (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (finitePoint : IntegralBinaryGL) (argument : ℂ)
      (positive : 0 < argument.im), 1 ≤ argument.im → |argument.re| ≤ 1 → ∀ scale : ℝ, 1 ≤ scale →
        scale ^ power * argument.im ^ cuspPower *
          ‖(theta (pullback realTest (realTransform point (unit argument positive * right))) finiteTest scale -
            realTest 0 * finiteTest 0) * cuspValue data vector finitePoint right argument positive‖ ≤ constant := by
  obtain ⟨thetaConstant, thetaNonnegative, bounded⟩ :=
    AdelicThetaDistortion.rapid_large_opNorm realTest finiteTest finiteContinuous finiteSupport power
  let distortion := 2 * ‖RectangularOperatorBounds.bilinear‖ * ‖point.val‖ * ‖right⁻¹.val‖
  let order := power + Module.finrank ℤ integerLattice + 1
  let thetaBound := thetaConstant * distortion ^ order
  have distortionNonnegative : 0 ≤ distortion := by dsimp [distortion]; positivity
  have thetaBoundNonnegative : 0 ≤ thetaBound := mul_nonneg thetaNonnegative (pow_nonneg distortionNonnegative _)
  refine ⟨thetaBound * cuspConstant data vector right cuspPower,
    mul_nonneg thetaBoundNonnegative (cuspConstant_nonnegative data vector right cuspPower), ?_⟩
  intro finitePoint argument positive height horizontal scale scaleLower
  let transform := realTransform point (unit argument positive * right)
  have thetaEstimate : scale ^ power * ‖theta (pullback realTest transform) finiteTest scale - realTest 0 * finiteTest 0‖ ≤ thetaBound :=
    (bounded transform scale scaleLower).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (CuspChartOperators.inverse_bound point right argument positive height horizontal) order)
      thetaNonnegative)
  calc
    _ = (scale ^ power * ‖theta (pullback realTest transform) finiteTest scale - realTest 0 * finiteTest 0‖) *
        (argument.im ^ cuspPower * ‖cuspValue data vector finitePoint right argument positive‖) := by rw [norm_mul]; ring
    _ ≤ thetaBound * cuspConstant data vector right cuspPower :=
      mul_le_mul thetaEstimate (weighted_cusp data vector fixed finitePoint right argument positive cuspPower)
        (mul_nonneg (pow_nonneg positive.le _) (norm_nonneg _)) thetaBoundNonnegative

theorem rapid_small {degree : ℕ} (data : InducingData degree) (vector : data.cusp.smooth)
    (fixed : vector.val ∈ fixedSubspace data.cusp finiteCongruence)
    (realTest : SchwartzMap RealSpace ℂ) (latticeScale : ℚˣ)
    (finiteTest : FiniteRectangularFourier.Space → ℂ) (finiteSupport : HasCompactSupport finiteTest)
    (invariant : ∀ shift ∈ FiniteLatticeCosets.latticeSubgroup (FiniteLatticeMeasure.rationalScale latticeScale),
      ∀ value, finiteTest (shift + value) = finiteTest value)
    (point : GeneralLinearGroup (Fin 3) ℝ) (right : BinaryRealGL) (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (finitePoint : IntegralBinaryGL) (argument : ℂ)
      (positive : 0 < argument.im), 1 ≤ argument.im → |argument.re| ≤ 1 → ∀ scale : ℝ, 0 < scale → scale ≤ 1 →
        scale⁻¹ ^ power * argument.im ^ cuspPower *
          ‖(theta (pullback realTest (realTransform point (unit argument positive * right))) finiteTest scale -
            ((scale⁻¹ ^ 6 * factor (realTransform point (unit argument positive * right)) : ℝ) : ℂ) *
              (FourierTransform.fourier realTest 0 * FiniteRectangularFourier.transform finiteTest 0)) *
                cuspValue data vector finitePoint right argument positive‖ ≤ constant := by
  obtain ⟨thetaConstant, thetaNonnegative, bounded⟩ :=
    ThetaDistortionPoisson.rapid_small realTest latticeScale finiteTest finiteSupport invariant power
  let distortion := 2 * ‖RectangularOperatorBounds.bilinear‖ * ‖point⁻¹.val‖ * ‖right.val‖
  let determinant := |point.val.det| ^ 2 * |right.val.det|⁻¹ ^ 3
  let order := power + 6 + Module.finrank ℤ integerLattice + 1
  let thetaBound := thetaConstant * determinant * distortion ^ order
  have distortionNonnegative : 0 ≤ distortion := by dsimp [distortion]; positivity
  have determinantNonnegative : 0 ≤ determinant := by dsimp [determinant]; positivity
  have thetaBoundNonnegative : 0 ≤ thetaBound :=
    mul_nonneg (mul_nonneg thetaNonnegative determinantNonnegative) (pow_nonneg distortionNonnegative _)
  refine ⟨thetaBound * cuspConstant data vector right (cuspPower + order),
    mul_nonneg thetaBoundNonnegative (cuspConstant_nonnegative data vector right _), ?_⟩
  intro finitePoint argument positive height horizontal scale scalePositive scaleUpper
  let transform := realTransform point (unit argument positive * right)
  let remainder := theta (pullback realTest transform) finiteTest scale - ((scale⁻¹ ^ 6 * factor transform : ℝ) : ℂ) *
    (FourierTransform.fourier realTest 0 * FiniteRectangularFourier.transform finiteTest 0)
  have thetaEstimate : scale⁻¹ ^ power * ‖remainder‖ ≤ thetaBound * argument.im ^ order := by
    apply (bounded transform scale scalePositive scaleUpper).trans
    calc
      _ ≤ (thetaConstant * determinant) * (distortion * argument.im) ^ order :=
        mul_le_mul (mul_le_mul_of_nonneg_left (CuspChartOperators.factor_bound point right argument positive height) thetaNonnegative)
          (pow_le_pow_left₀ (norm_nonneg _) (CuspChartOperators.transform_bound point right argument positive height horizontal) order)
          (pow_nonneg (norm_nonneg _) _) (mul_nonneg thetaNonnegative determinantNonnegative)
      _ = thetaBound * argument.im ^ order := by rw [mul_pow]; exact (mul_assoc _ _ _).symm
  calc
    _ = (scale⁻¹ ^ power * ‖remainder‖) *
        (argument.im ^ cuspPower * ‖cuspValue data vector finitePoint right argument positive‖) := by rw [norm_mul]; ring
    _ ≤ (thetaBound * argument.im ^ order) *
        (argument.im ^ cuspPower * ‖cuspValue data vector finitePoint right argument positive‖) :=
      mul_le_mul_of_nonneg_right thetaEstimate (mul_nonneg (pow_nonneg positive.le _) (norm_nonneg _))
    _ = thetaBound * (argument.im ^ (cuspPower + order) * ‖cuspValue data vector finitePoint right argument positive‖) := by
      rw [pow_add]; ring
    _ ≤ thetaBound * cuspConstant data vector right (cuspPower + order) :=
      mul_le_mul_of_nonneg_left (weighted_cusp data vector fixed finitePoint right argument positive _) thetaBoundNonnegative

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspThetaDecay
