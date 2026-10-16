module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CauchyRiemannCircularMean
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.CompactSmoothIntegral

@[expose] public section


open MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance CauchyRiemannMeanRegularity_measurableSpaceCircle : MeasurableSpace Circle := borel Circle
local instance CauchyRiemannMeanRegularity_borelSpaceCircle : BorelSpace Circle := ⟨rfl⟩

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def circularMeanCorrection (derivative : ℂ → E) (center direction : ℂ) : E :=
  ∫ radial in (0 : ℝ)..1, ∫ angle : Circle,
    (starRingEnd ℂ) (direction * (angle : ℂ)) •
      derivative (center + radial • (direction * (angle : ℂ))) ∂binaryRotationMeasure

theorem circularMeanCorrection_contDiff {order : ℕ∞} (derivative : ℂ → E)
    (regular : ContDiff ℝ order derivative) :
    ContDiff ℝ order (Function.uncurry (circularMeanCorrection derivative)) := by
  let values : ((ℂ × ℂ) × ℝ) → ℂ → E := fun parameter angle =>
    (starRingEnd ℂ) (parameter.1.2 * angle) • derivative (parameter.1.1 + parameter.2 • (parameter.1.2 * angle))
  have kernel : ContDiff ℝ order (Function.uncurry values) := by
    dsimp only [Function.uncurry_def, values]
    exact (Complex.conjCLE.toContinuousLinearMap.contDiff.comp (by fun_prop)).smul (regular.comp (by fun_prop))
  have angular := contDiffOn_integral_compact_image (measure := binaryRotationMeasure)
    (fun angle : Circle => (angle : ℂ)) (by fun_prop) isOpen_univ kernel.contDiffOn
  have angular_regular : ContDiffOn ℝ order
      (fun parameter : (ℂ × ℂ) × ℝ => ∫ angle : Circle, values parameter (angle : ℂ) ∂binaryRotationMeasure)
      (Set.univ ×ˢ Set.univ) := by
    simpa only [Set.univ_prod_univ] using angular
  have result := contDiffOn_intervalIntegral (values := fun parameter radial =>
    ∫ angle : Circle, values (parameter, radial) (angle : ℂ) ∂binaryRotationMeasure)
    isOpen_univ angular_regular 0 1 (by norm_num)
  exact contDiffOn_univ.mp result

theorem circularMean_sub_contDiff [CompleteSpace E] {order : ℕ∞} (function : ℂ → E)
    (regular : ContDiff ℝ 1 function) (derivative_regular : ContDiff ℝ order (antiholomorphicDerivative function)) :
    ContDiff ℝ order (fun parameter : ℂ × ℂ =>
      (∫ angle : Circle, function (parameter.1 + parameter.2 * (angle : ℂ)) ∂binaryRotationMeasure) - function parameter.1) := by
  have smooth := circularMeanCorrection_contDiff (antiholomorphicDerivative function) derivative_regular
  convert smooth using 1
  funext parameter
  exact circularMean_affine_sub_eq_integral function regular parameter.1 parameter.2

end TernaryPeriodPolynomials.SphericalDetection.Helpers
