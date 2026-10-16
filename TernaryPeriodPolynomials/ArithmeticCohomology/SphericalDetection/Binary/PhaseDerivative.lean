module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationCovariance
public import Mathlib.Analysis.Calculus.Deriv.ZPow

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem normalizedComplex_hasDerivAt (function : ℝ → ℂ) (angle : Circle) (derivative : ℂ)
    (at_zero : function 0 = (angle : ℂ)) (regular : HasDerivAt function derivative 0) :
    HasDerivAt (fun parameter => function parameter / (‖function parameter‖ : ℂ))
      (derivative - (inner ℝ (angle : ℂ) derivative : ℂ) * (angle : ℂ)) 0 := by
  have norm_derivative : HasDerivAt (fun parameter => ‖function parameter‖)
      (inner ℝ (angle : ℂ) derivative) 0 := by
    have nonzero : ‖function 0‖ ^ 2 ≠ 0 := by rw [at_zero, Circle.norm_coe]; norm_num
    simpa only [Real.sqrt_sq (norm_nonneg _), at_zero, Circle.norm_coe, one_pow, Real.sqrt_one,
      mul_one, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using regular.norm_sq.sqrt nonzero
  have norm_nonzero : (‖function 0‖ : ℂ) ≠ 0 := by rw [at_zero, Circle.norm_coe]; norm_num
  have normalized := regular.mul (norm_derivative.ofReal_comp.inv norm_nonzero)
  convert normalized using 1 <;> first
    | rfl
    | (simp only [Pi.inv_apply, at_zero, Circle.norm_coe, Complex.ofReal_one, inv_one, one_pow,
        mul_one, div_one, mul_neg, sub_eq_add_neg, mul_comm])

def binaryRotationPhaseDerivative (angle : Circle) (direction : ℂ) : ℂ :=
  ((angle : ℂ).im : ℂ) * direction -
    (inner ℝ (angle : ℂ) (((angle : ℂ).im : ℂ) * direction) : ℂ) * (angle : ℂ)

theorem circle_coordinates_sq (angle : Circle) : (angle : ℂ).re ^ 2 + (angle : ℂ).im ^ 2 = 1 := by
  simpa only [Complex.normSq_apply, pow_two] using Circle.normSq_coe angle

theorem binaryRotationPhaseDerivative_coordinates (angle : Circle) (direction : ℂ) :
    binaryRotationPhaseDerivative angle direction =
      Complex.I * (angle : ℂ) *
        (((angle : ℂ).im * ((angle : ℂ).re * direction.im - (angle : ℂ).im * direction.re) : ℝ) : ℂ) := by
  have total := circle_coordinates_sq angle
  have inner_eq := inner_map_complex (LinearIsometryEquiv.refl ℝ ℂ) (angle : ℂ)
    (((angle : ℂ).im : ℂ) * direction)
  change inner ℝ (angle : ℂ) (((angle : ℂ).im : ℂ) * direction) =
    ((((angle : ℂ).im : ℂ) * direction) * (starRingEnd ℂ) (angle : ℂ)).re at inner_eq
  apply Complex.ext
  · simp only [binaryRotationPhaseDerivative, inner_eq, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.mul_im, Complex.I_re, Complex.I_im]
    linear_combination -((angle : ℂ).im * direction.re) * total
  · simp only [binaryRotationPhaseDerivative, inner_eq, Complex.sub_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      Complex.mul_im, Complex.I_re, Complex.I_im]
    linear_combination -((angle : ℂ).im * direction.im) * total

theorem binaryRotationPhase_hasDerivAt (angle : Circle) (direction : ℂ) :
    HasDerivAt
      (fun parameter : ℝ => binaryPhaseValue (binaryRotations angle) (Complex.I + parameter • direction))
      (binaryRotationPhaseDerivative angle direction) 0 := by
  have denominator_derivative :
      HasDerivAt (fun parameter : ℝ => UpperHalfPlane.denom (binaryRotations angle) (Complex.I + parameter • direction))
        (((angle : ℂ).im : ℂ) * direction) 0 := by
    have derived := ((complexAffineLine_hasDerivAt direction).const_mul ((angle : ℂ).im : ℂ)).add_const
      ((angle : ℂ).re : ℂ)
    exact derived
  exact normalizedComplex_hasDerivAt _ angle _ (by
    simp only [zero_smul, add_zero, binaryRotations_denom_I]) denominator_derivative

theorem hasDerivAt_complex_zpow_comp (function : ℝ → ℂ) (value derivative : ℂ) (power : ℤ)
    (at_zero : function 0 = value) (nonzero : value ≠ 0) (regular : HasDerivAt function derivative 0) :
    HasDerivAt (fun parameter => function parameter ^ power)
      ((power : ℂ) * value ^ (power - 1) * derivative) 0 := by
  have outer := (hasDerivAt_zpow power value (Or.inl nonzero)).hasFDerivAt.restrictScalars ℝ
  have composed := outer.comp_hasDerivAt_of_eq 0 regular at_zero.symm
  convert composed using 1 <;> first
    | rfl
    | (change (power : ℂ) * value ^ (power - 1) * derivative = derivative * ((power : ℂ) * value ^ (power - 1)); ring)

theorem binaryRotationPhase_zpow_hasDerivAt (angle : Circle) (direction : ℂ) (weight : ℤ) :
    HasDerivAt
      (fun parameter : ℝ => binaryPhaseValue (binaryRotations angle) (Complex.I + parameter • direction) ^ weight)
      ((weight : ℂ) * (angle : ℂ) ^ (weight - 1) * binaryRotationPhaseDerivative angle direction) 0 := by
  have nonzero : (angle : ℂ) ≠ 0 := by
    intro zero
    have norm := Circle.norm_coe angle
    rw [zero, norm_zero] at norm
    exact zero_ne_one norm
  exact hasDerivAt_complex_zpow_comp _ (angle : ℂ) _ weight
    (by simp only [zero_smul, add_zero, binaryPhaseValue_rotation_I]) nonzero
    (binaryRotationPhase_hasDerivAt angle direction)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
