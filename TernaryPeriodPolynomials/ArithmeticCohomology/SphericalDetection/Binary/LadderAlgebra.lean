module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.WeightDifferential

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realLinear_holomorphic_coordinates {E : Type} [AddCommGroup E] [Module ℂ E]
    [Module ℝ E] [IsScalarTower ℝ ℂ E] (linear : ℂ →ₗ[ℝ] E) (scalar : ℂ) :
    linear scalar - Complex.I • linear (scalar * Complex.I) =
      scalar • (linear 1 - Complex.I • linear Complex.I) := by
  rw [realLinear_complex_coordinates linear scalar,
    realLinear_complex_coordinates linear (scalar * Complex.I)]
  simp only [Complex.mul_I_re, Complex.mul_I_im, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have product : ((scalar.re : ℂ) + (scalar.im : ℂ) * Complex.I) * Complex.I =
      (scalar.re : ℂ) * Complex.I - (scalar.im : ℂ) := by
    rw [add_mul, mul_assoc, Complex.I_mul_I, mul_neg_one]
    rfl
  calc
    _ = ((scalar.re : ℂ) + (scalar.im : ℂ) * Complex.I) •
        (linear 1 - Complex.I • linear Complex.I) := by
      rw [smul_sub, smul_smul, product]
      module
    _ = _ := by rw [Complex.re_add_im]

theorem binaryRotationPhaseDerivative_holomorphic (angle : Circle) :
    binaryRotationPhaseDerivative angle 1 - Complex.I * binaryRotationPhaseDerivative angle Complex.I =
      ((angle : ℂ).im : ℂ) := by
  have conjugate : (starRingEnd ℂ) (angle : ℂ) =
      ((angle : ℂ).re : ℂ) - Complex.I * ((angle : ℂ).im : ℂ) := by
    apply Complex.ext <;> simp
  calc
    _ = (angle : ℂ) * (starRingEnd ℂ) (angle : ℂ) * ((angle : ℂ).im : ℂ) := by
      rw [binaryRotationPhaseDerivative_coordinates, binaryRotationPhaseDerivative_coordinates, conjugate]
      simp only [Complex.one_im, Complex.one_re, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, zero_sub, sub_zero, Complex.ofReal_mul, Complex.ofReal_neg]
      ring_nf
      simp [Complex.I_sq]
    _ = _ := by rw [Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one, one_mul]

theorem realLinear_antiholomorphic_coordinates {E : Type} [AddCommGroup E] [Module ℂ E]
    [Module ℝ E] [IsScalarTower ℝ ℂ E] (linear : ℂ →ₗ[ℝ] E) (scalar : ℂ) :
    linear scalar + Complex.I • linear (scalar * Complex.I) =
      (starRingEnd ℂ) scalar • (linear 1 + Complex.I • linear Complex.I) := by
  rw [realLinear_complex_coordinates linear scalar,
    realLinear_complex_coordinates linear (scalar * Complex.I)]
  simp only [Complex.mul_I_re, Complex.mul_I_im, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have product : ((scalar.re : ℂ) - (scalar.im : ℂ) * Complex.I) * Complex.I =
      (scalar.re : ℂ) * Complex.I + (scalar.im : ℂ) := by
    rw [sub_mul, mul_assoc, Complex.I_mul_I, mul_neg_one, sub_neg_eq_add]
  have conjugate : (starRingEnd ℂ) scalar = (scalar.re : ℂ) - (scalar.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [conjugate]
  conv_rhs => rw [smul_add, smul_smul, product]
  module

theorem binaryRotationPhaseDerivative_antiholomorphic (angle : Circle) :
    binaryRotationPhaseDerivative angle 1 + Complex.I * binaryRotationPhaseDerivative angle Complex.I =
      -(angle : ℂ) ^ 2 * ((angle : ℂ).im : ℂ) := by
  calc
    _ = -(angle : ℂ) * (((angle : ℂ).re : ℂ) + ((angle : ℂ).im : ℂ) * Complex.I) *
        ((angle : ℂ).im : ℂ) := by
      rw [binaryRotationPhaseDerivative_coordinates, binaryRotationPhaseDerivative_coordinates]
      simp only [Complex.one_im, Complex.one_re, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, zero_sub, sub_zero, Complex.ofReal_mul, Complex.ofReal_neg]
      ring_nf
      simp [Complex.I_sq, sub_eq_add_neg]
    _ = _ := by rw [Complex.re_add_im]; ring

theorem circle_square_phase (angle : Circle) :
    (angle : ℂ) ^ 2 = 1 + 2 * Complex.I * (angle : ℂ) * ((angle : ℂ).im : ℂ) := by
  have difference : (angle : ℂ) - (starRingEnd ℂ) (angle : ℂ) = 2 * Complex.I * ((angle : ℂ).im : ℂ) := by
    apply Complex.ext <;> simp
    ring
  have product := congrArg (fun value : ℂ => (angle : ℂ) * value) difference
  rw [mul_sub, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one] at product
  linear_combination product

theorem binaryLowering_scalar (angle : Circle) (weight : ℤ) :
    (weight : ℂ) * (angle : ℂ) ^ (weight - 1) * ((angle : ℂ).im : ℂ) +
      (Complex.I * (weight : ℂ) / 2) * (angle : ℂ) ^ weight =
        (angle : ℂ) ^ (weight - 2) * (Complex.I * (weight : ℂ) / 2) := by
  have nonzero : (angle : ℂ) ≠ 0 := by
    intro zero
    have norm := Circle.norm_coe angle
    rw [zero, norm_zero] at norm
    exact zero_ne_one norm
  have step_one : (angle : ℂ) ^ (weight - 1) = (angle : ℂ) ^ (weight - 2) * (angle : ℂ) := by
    rw [← zpow_add_one₀ nonzero]
    congr 1
    omega
  have step_two : (angle : ℂ) ^ weight = (angle : ℂ) ^ (weight - 2) * (angle : ℂ) ^ 2 := by
    rw [← zpow_natCast, ← zpow_add₀ nonzero]
    congr 1
    omega
  rw [step_one, step_two, circle_square_phase]
  ring_nf
  simp [Complex.I_sq]

theorem binaryRaising_scalar (angle : Circle) (weight : ℤ) :
    -((weight : ℂ) * (angle : ℂ) ^ (weight + 1) * ((angle : ℂ).im : ℂ)) +
      (Complex.I * (weight : ℂ) / 2) * (angle : ℂ) ^ weight =
        (angle : ℂ) ^ (weight + 2) * (Complex.I * (weight : ℂ) / 2) := by
  have nonzero : (angle : ℂ) ≠ 0 := by
    intro zero
    have norm := Circle.norm_coe angle
    rw [zero, norm_zero] at norm
    exact zero_ne_one norm
  rw [zpow_add_one₀ nonzero, zpow_add₀ nonzero]
  have square : (angle : ℂ) ^ (2 : ℤ) = 1 + 2 * Complex.I * (angle : ℂ) * ((angle : ℂ).im : ℂ) :=
    circle_square_phase angle
  rw [square]
  ring_nf
  simp [Complex.I_sq]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
