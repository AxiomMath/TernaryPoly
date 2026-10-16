module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Uniform.ThetaFamilies
public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Vector.CuspThetaDecay

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularSchwartz TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularTransport TernaryPeriodPolynomials.PlaneEisensteinContinuation.UpperTriangularChart
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel TernaryPeriodPolynomials.PlaneEisensteinContinuation.SobolevSeminorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.BanachThetaPoisson
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.VectorCuspThetaDecay

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformCuspTheta

variable {Source : Type} [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]

theorem large {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : Set (SchwartzMap RealSpace Source)) (testsBounded : UniformSchwartzBounds.Bounded tests)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (parameters : Set FiniteParameterThetaDecay.Parameter) (finiteCompact : IsCompact parameters)
    (point : GeneralLinearGroup (Fin 3) ℝ) (rightSet : Set BinaryRealGL) (rightCompact : IsCompact rightSet)
    (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ realTest ∈ tests, realTest 0 = 0 → ∀ parameter ∈ parameters, ∀ right ∈ rightSet,
      ∀ (integral : IntegralBinaryGL) (argument : UpperHalfPlane), 1 ≤ argument.im → |argument.re| ≤ 1 →
      ∀ scale : ℝ, 1 ≤ scale →
        scale ^ power * argument.im ^ cuspPower *
          ‖value data family (theta (pullback realTest (realTransform point (unit argument argument.im_pos * right)))
            (FiniteFourierUniform.test finiteScale offset parameter) scale) integral right argument‖ ≤ constant := by
  obtain ⟨thetaConstant, thetaNonnegative, thetaBounded⟩ :=
    UniformThetaFamilies.large_boxes tests testsBounded finiteScale offset parameters finiteCompact power
  obtain ⟨distortion, distortionNonnegative, operatorBounded⟩ := CompactChartOperators.bounds point rightSet rightCompact
  obtain ⟨cuspConstant, cuspNonnegative, cuspBounded⟩ := weighted_bound data family continuous rightSet rightCompact cuspPower
  let order := power + Module.finrank ℤ integerLattice + 1
  let thetaBound := thetaConstant * distortion ^ order
  have thetaBoundNonnegative : 0 ≤ thetaBound := mul_nonneg thetaNonnegative (pow_nonneg distortionNonnegative _)
  refine ⟨cuspConstant * thetaBound, mul_nonneg cuspNonnegative thetaBoundNonnegative, ?_⟩
  intro realTest testMembership zeroValue parameter parameterMem right rightMem integral argument height horizontal scale scaleLower
  let transform := realTransform point (unit argument argument.im_pos * right)
  let vector := theta (pullback realTest transform) (FiniteFourierUniform.test finiteScale offset parameter) scale
  have thetaEstimate : scale ^ power * ‖vector‖ ≤ thetaBound := by
    have result := (thetaBounded realTest testMembership parameter parameterMem transform scale scaleLower).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (operatorBounded right rightMem argument argument.im_pos height horizontal).2.1 order)
        thetaNonnegative)
    simpa only [zeroValue, smul_zero, sub_zero] using result
  calc
    _ = scale ^ power * (argument.im ^ cuspPower * ‖value data family vector integral right argument‖) := by ring
    _ ≤ scale ^ power * (cuspConstant * ‖vector‖) :=
      mul_le_mul_of_nonneg_left (cuspBounded right rightMem integral argument vector) (pow_nonneg (zero_le_one.trans scaleLower) _)
    _ = cuspConstant * (scale ^ power * ‖vector‖) := by ring
    _ ≤ cuspConstant * thetaBound := mul_le_mul_of_nonneg_left thetaEstimate cuspNonnegative

theorem small {degree : ℕ} (data : InducingData degree)
    (family : Source →ₗ[ℂ] fixedSmooth data.cusp finiteCongruence)
    (continuous : Continuous (fun vector => (family vector).val.val))
    (tests : Set (SchwartzMap RealSpace Source)) (testsBounded : UniformSchwartzBounds.Bounded tests)
    (finiteScale : FiniteAdelesˣ) (offset : FiniteRectangularFourier.Space)
    (parameters : Set FiniteParameterThetaDecay.Parameter) (finiteCompact : IsCompact parameters)
    (point : GeneralLinearGroup (Fin 3) ℝ) (rightSet : Set BinaryRealGL) (rightCompact : IsCompact rightSet)
    (power cuspPower : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ realTest ∈ tests, FourierTransform.fourier realTest 0 = 0 → ∀ parameter ∈ parameters, ∀ right ∈ rightSet,
      ∀ (integral : IntegralBinaryGL) (argument : UpperHalfPlane), 1 ≤ argument.im → |argument.re| ≤ 1 →
      ∀ scale : ℝ, 0 < scale → scale ≤ 1 →
        scale⁻¹ ^ power * argument.im ^ cuspPower *
          ‖value data family (theta (pullback realTest (realTransform point (unit argument argument.im_pos * right)))
            (FiniteFourierUniform.test finiteScale offset parameter) scale) integral right argument‖ ≤ constant := by
  obtain ⟨thetaConstant, thetaNonnegative, thetaBounded⟩ :=
    UniformThetaFamilies.small_boxes tests testsBounded finiteScale offset parameters finiteCompact power
  obtain ⟨distortion, distortionNonnegative, operatorBounded⟩ := CompactChartOperators.bounds point rightSet rightCompact
  let order := power + 6 + Module.finrank ℤ integerLattice + 1
  obtain ⟨cuspConstant, cuspNonnegative, cuspBounded⟩ := weighted_bound data family continuous rightSet rightCompact (cuspPower + order)
  let thetaBound := thetaConstant * distortion * distortion ^ order
  have thetaBoundNonnegative : 0 ≤ thetaBound :=
    mul_nonneg (mul_nonneg thetaNonnegative distortionNonnegative) (pow_nonneg distortionNonnegative _)
  refine ⟨cuspConstant * thetaBound, mul_nonneg cuspNonnegative thetaBoundNonnegative, ?_⟩
  intro realTest testMembership zeroFourier parameter parameterMem right rightMem integral argument height horizontal scale scalePositive scaleUpper
  let transform := realTransform point (unit argument argument.im_pos * right)
  let vector := theta (pullback realTest transform) (FiniteFourierUniform.test finiteScale offset parameter) scale
  have thetaEstimate : scale⁻¹ ^ power * ‖vector‖ ≤ thetaBound * argument.im ^ order := by
    have result : scale⁻¹ ^ power * ‖vector‖ ≤ thetaConstant * RealFourierLinear.factor transform * ‖transform.toContinuousLinearMap‖ ^ order := by
      simpa only [zeroFourier, smul_zero, sub_zero] using thetaBounded realTest testMembership parameter parameterMem transform scale scalePositive scaleUpper
    apply result.trans
    calc
      _ ≤ (thetaConstant * distortion) * (distortion * argument.im) ^ order :=
        mul_le_mul (mul_le_mul_of_nonneg_left (operatorBounded right rightMem argument argument.im_pos height horizontal).2.2 thetaNonnegative)
          (pow_le_pow_left₀ (norm_nonneg _) (operatorBounded right rightMem argument argument.im_pos height horizontal).1 order)
          (pow_nonneg (norm_nonneg _) _) (mul_nonneg thetaNonnegative distortionNonnegative)
      _ = thetaBound * argument.im ^ order := by rw [mul_pow]; exact (mul_assoc _ _ _).symm
  refine le_of_mul_le_mul_left (a := argument.im ^ order) ?_ (pow_pos argument.im_pos order)
  calc
    _ = scale⁻¹ ^ power * (argument.im ^ (cuspPower + order) * ‖value data family vector integral right argument‖) := by
      rw [pow_add]; ring
    _ ≤ scale⁻¹ ^ power * (cuspConstant * ‖vector‖) :=
      mul_le_mul_of_nonneg_left (cuspBounded right rightMem integral argument vector) (pow_nonneg (inv_nonneg.mpr scalePositive.le) _)
    _ = cuspConstant * (scale⁻¹ ^ power * ‖vector‖) := by ring
    _ ≤ cuspConstant * (thetaBound * argument.im ^ order) := mul_le_mul_of_nonneg_left thetaEstimate cuspNonnegative
    _ = _ := by ring


end TernaryPeriodPolynomials.PlaneEisensteinContinuation.UniformCuspTheta
