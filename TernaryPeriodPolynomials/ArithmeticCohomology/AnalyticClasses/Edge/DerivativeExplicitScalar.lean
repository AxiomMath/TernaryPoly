module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Edge.DerivativeExplicitAlgebra

@[expose] public section


/-!
# The explicit coefficients of the mixed derivative at the good-line coordinate

For the orthogonal Iwasawa factor `k = k(u)` of the good-line argument, `u = (s, t)`,
`α = √(1 + s²)` and `R = √(1 + s² + t²)`, the derivatives `ξ(W)` of the radical coordinate and
`ż(W)` of the Levi point at `k` in the directions `k H` and `k Rᵢ` are explicit rational
functions of `s, t, α, R`. With `E = i (R + α²) - s t` and `N = i (R - α²) - s t` (so that the
Levi point of the good-line vertex is `z = (i R - s t) / α²`, `z + i = E / α²` and
`z - i = N / α²`), the holomorphic coefficients satisfy
`c₁ (2 i α²)³ R³ = -2 i α³ (E³ + 3 E² N - 3 E N² - N³)` and
`c₀ (2 i α²)³ R³ = -2 α³ (E³ - 3 E² N - 3 E N² + N³)`; the antiholomorphic coefficients satisfy
the first identity and the negative of the second one with `s t` replaced by `-s t`. Moreover
`det k = -1`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace EdgeExplicit

/-! ### Entries -/

theorem gsOrthMatrix_00 (u : ℝ × ℝ) : gsOrthMatrix u 0 0 = 0 := by
  simp [gsOrthMatrix]

theorem gsOrthMatrix_01 (u : ℝ × ℝ) : gsOrthMatrix u 0 1 = 1 / gsAlpha u := by
  simp [gsOrthMatrix]

theorem gsOrthMatrix_02 (u : ℝ × ℝ) : gsOrthMatrix u 0 2 = -u.1 / gsAlpha u := by
  simp [gsOrthMatrix]

theorem gsOrthMatrix_10 (u : ℝ × ℝ) : gsOrthMatrix u 1 0 = gsAlpha u / gsRadius u := by
  simp [gsOrthMatrix]

theorem gsOrthMatrix_11 (u : ℝ × ℝ) :
    gsOrthMatrix u 1 1 = -(u.1 * u.2) / (gsRadius u * gsAlpha u) := by
  simp [gsOrthMatrix]

theorem gsOrthMatrix_12 (u : ℝ × ℝ) : gsOrthMatrix u 1 2 = -u.2 / (gsRadius u * gsAlpha u) := by
  simp [gsOrthMatrix]

theorem gsOrthMatrix_20 (u : ℝ × ℝ) : gsOrthMatrix u 2 0 = u.2 / gsRadius u := by
  simp [gsOrthMatrix]

theorem gsOrthMatrix_21 (u : ℝ × ℝ) : gsOrthMatrix u 2 1 = u.1 / gsRadius u := by
  simp [gsOrthMatrix]

theorem gsOrthMatrix_22 (u : ℝ × ℝ) : gsOrthMatrix u 2 2 = 1 / gsRadius u := by
  simp [gsOrthMatrix]

theorem flowVelocity_apply (a b : Fin 3) : flowVelocity a b =
    if a = 0 ∧ b = 0 then 1 else if a = 1 ∧ b = 1 then -1 else 0 := by
  fin_cases a <;> fin_cases b <;> simp [flowVelocity]

theorem axisVelocity_zero_apply (a b : Fin 3) :
    axisVelocity 0 a b = if a = 2 ∧ b = 0 then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> simp [axisVelocity]

theorem axisVelocity_one_apply (a b : Fin 3) :
    axisVelocity 1 a b = if a = 2 ∧ b = 1 then 1 else 0 := by
  fin_cases a <;> fin_cases b <;> simp [axisVelocity]

/-! ### The derivative of the Gram matrix along `k H` and `k Rᵢ` -/

theorem gramFlow_02 (u : ℝ × ℝ) :
    gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity) 0 2 =
      -2 * u.1 / (gsRadius u * gsAlpha u) := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  simp (config := { decide := true }) only [gramDerivLinear_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, gsOrthMatrix_00, gsOrthMatrix_01,
    gsOrthMatrix_02, gsOrthMatrix_20, gsOrthMatrix_21, gsOrthMatrix_22, flowVelocity_apply,
    Fin.isValue, true_and, false_and, ite_true, ite_false, mul_zero, mul_one, zero_mul, add_zero,
    zero_add]
  field_simp
  ring

theorem gramFlow_12 (u : ℝ × ℝ) :
    gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity) 1 2 =
      2 * u.2 * (2 * u.1 ^ 2 + 1) / (gsRadius u ^ 2 * gsAlpha u) := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  simp (config := { decide := true }) only [gramDerivLinear_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, gsOrthMatrix_10, gsOrthMatrix_11,
    gsOrthMatrix_12, gsOrthMatrix_20, gsOrthMatrix_21, gsOrthMatrix_22, flowVelocity_apply,
    Fin.isValue, true_and, false_and, ite_true, ite_false, mul_zero, mul_one, zero_mul, add_zero,
    zero_add]
  field_simp
  linear_combination 2 * u.2 * ha2

theorem gramFlow_01 (u : ℝ × ℝ) :
    gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity) 0 1 =
      2 * u.1 * u.2 / (gsRadius u * gsAlpha u ^ 2) := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  simp (config := { decide := true }) only [gramDerivLinear_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, gsOrthMatrix_00, gsOrthMatrix_01,
    gsOrthMatrix_02, gsOrthMatrix_10, gsOrthMatrix_11, gsOrthMatrix_12, flowVelocity_apply,
    Fin.isValue, true_and, false_and, ite_true, ite_false, mul_zero, mul_one, zero_mul, add_zero,
    zero_add]
  field_simp
  ring

theorem gramFlow_diag (u : ℝ × ℝ) :
    gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity) 0 0 -
      gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * flowVelocity) 1 1 =
      -2 * (u.1 ^ 4 - u.1 ^ 2 * u.2 ^ 2 + 3 * u.1 ^ 2 + u.2 ^ 2 + 2) /
      (gsRadius u ^ 2 * gsAlpha u ^ 2) := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  simp (config := { decide := true }) only [gramDerivLinear_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, gsOrthMatrix_00, gsOrthMatrix_01,
    gsOrthMatrix_02, gsOrthMatrix_10, gsOrthMatrix_11, gsOrthMatrix_12, flowVelocity_apply,
    Fin.isValue, true_and, false_and, ite_true, ite_false, mul_zero, mul_one, zero_mul, add_zero,
    zero_add]
  field_simp
  linear_combination (-2) * hR2 - 2 * (gsAlpha u ^ 2 + 1 + u.1 ^ 2) * ha2

theorem gramAxisZero_02 (u : ℝ × ℝ) :
    gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity 0) 0 2 =
      -(u.1 * u.2) / (gsRadius u * gsAlpha u) := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  simp (config := { decide := true }) only [gramDerivLinear_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, gsOrthMatrix_00, gsOrthMatrix_01,
    gsOrthMatrix_02, gsOrthMatrix_20, gsOrthMatrix_21, gsOrthMatrix_22, axisVelocity_zero_apply,
    Fin.isValue, true_and, false_and, ite_true, ite_false, mul_zero, mul_one, zero_mul, add_zero,
    zero_add]
  field_simp

theorem gramAxisZero_12 (u : ℝ × ℝ) :
    gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity 0) 1 2 =
      (u.1 ^ 2 - u.2 ^ 2 + 1) / (gsRadius u ^ 2 * gsAlpha u) := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  simp (config := { decide := true }) only [gramDerivLinear_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, gsOrthMatrix_10, gsOrthMatrix_11,
    gsOrthMatrix_12, gsOrthMatrix_20, gsOrthMatrix_21, gsOrthMatrix_22, axisVelocity_zero_apply,
    Fin.isValue, true_and, false_and, ite_true, ite_false, mul_zero, mul_one, zero_mul, add_zero,
    zero_add]
  field_simp
  linear_combination ha2

theorem gramAxisZero_01 (u : ℝ × ℝ) :
    gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity 0) 0 1 =
      -u.1 / gsRadius u := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  simp (config := { decide := true }) only [gramDerivLinear_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, gsOrthMatrix_00, gsOrthMatrix_01,
    gsOrthMatrix_02, gsOrthMatrix_10, gsOrthMatrix_11, gsOrthMatrix_12, axisVelocity_zero_apply,
    Fin.isValue, true_and, false_and, ite_true, ite_false, mul_zero, mul_one, zero_mul, add_zero,
    zero_add]
  field_simp

theorem gramAxisZero_diag (u : ℝ × ℝ) :
    gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity 0) 0 0 -
      gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity 0) 1 1 =
      2 * u.2 / gsRadius u ^ 2 := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  simp (config := { decide := true }) only [gramDerivLinear_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, gsOrthMatrix_00, gsOrthMatrix_01,
    gsOrthMatrix_02, gsOrthMatrix_10, gsOrthMatrix_11, gsOrthMatrix_12, axisVelocity_zero_apply,
    Fin.isValue, true_and, false_and, ite_true, ite_false, mul_zero, mul_one, zero_mul, add_zero,
    zero_add]
  field_simp
  ring

theorem gramAxisOne_02 (u : ℝ × ℝ) :
    gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity 1) 0 2 =
      (1 - u.1 ^ 2) / (gsRadius u * gsAlpha u) := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  simp (config := { decide := true }) only [gramDerivLinear_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, gsOrthMatrix_00, gsOrthMatrix_01,
    gsOrthMatrix_02, gsOrthMatrix_20, gsOrthMatrix_21, gsOrthMatrix_22, axisVelocity_one_apply,
    Fin.isValue, true_and, false_and, ite_true, ite_false, mul_zero, mul_one, zero_mul, add_zero,
    zero_add]
  field_simp
  ring

theorem gramAxisOne_12 (u : ℝ × ℝ) :
    gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity 1) 1 2 =
      -2 * u.1 * u.2 / (gsRadius u ^ 2 * gsAlpha u) := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  simp (config := { decide := true }) only [gramDerivLinear_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, gsOrthMatrix_10, gsOrthMatrix_11,
    gsOrthMatrix_12, gsOrthMatrix_20, gsOrthMatrix_21, gsOrthMatrix_22, axisVelocity_one_apply,
    Fin.isValue, true_and, false_and, ite_true, ite_false, mul_zero, mul_one, zero_mul, add_zero,
    zero_add]
  field_simp
  ring

theorem gramAxisOne_01 (u : ℝ × ℝ) :
    gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity 1) 0 1 =
      u.2 * (u.1 ^ 2 - 1) / (gsRadius u * gsAlpha u ^ 2) := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  simp (config := { decide := true }) only [gramDerivLinear_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, gsOrthMatrix_00, gsOrthMatrix_01,
    gsOrthMatrix_02, gsOrthMatrix_10, gsOrthMatrix_11, gsOrthMatrix_12, axisVelocity_one_apply,
    Fin.isValue, true_and, false_and, ite_true, ite_false, mul_zero, mul_one, zero_mul, add_zero,
    zero_add]
  field_simp
  ring

theorem gramAxisOne_diag (u : ℝ × ℝ) :
    gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity 1) 0 0 -
      gramDerivLinear (gsOrthMatrix u) (gsOrthMatrix u * axisVelocity 1) 1 1 =
      -2 * u.1 * (u.1 ^ 2 + 2 * u.2 ^ 2 + 1) / (gsRadius u ^ 2 * gsAlpha u ^ 2) := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  simp (config := { decide := true }) only [gramDerivLinear_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, gsOrthMatrix_00, gsOrthMatrix_01,
    gsOrthMatrix_02, gsOrthMatrix_10, gsOrthMatrix_11, gsOrthMatrix_12, axisVelocity_one_apply,
    Fin.isValue, true_and, false_and, ite_true, ite_false, mul_zero, mul_one, zero_mul, add_zero,
    zero_add]
  field_simp
  linear_combination (-2 * u.1) * hR2

/-! ### The derivatives of the radical coordinate and of the Levi point -/

theorem radicalDeriv_eq_gram (k W : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 2) :
    radicalDeriv k W i = gramDerivLinear k W i.castSucc 2 := rfl

theorem pointDeriv_eq_gram (k W : Matrix (Fin 3) (Fin 3) ℝ) :
    pointDeriv k W = ((gramDerivLinear k W 0 1 : ℝ) : ℂ) +
      Complex.I / 2 * ((gramDerivLinear k W 0 0 - gramDerivLinear k W 1 1 : ℝ) : ℂ) := by
  rw [pointDeriv_apply, Complex.ofReal_sub]
  rfl

theorem binaryComplexReflection_parts (x y : ℝ) :
    binaryComplexReflection ((x : ℂ) + Complex.I / 2 * (y : ℂ)) =
      -(x : ℂ) + Complex.I / 2 * (y : ℂ) := by
  rw [binaryComplexReflection]
  simp only [_root_.neg_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    map_add, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-! ### Polynomial identities -/

theorem holCoeff_one_identity_generic (s t a R : ℂ) (ha : a ≠ 0) (hR : R ≠ 0)
    (ha2 : a ^ 2 = 1 + s ^ 2) (hR2 : R ^ 2 = 1 + s ^ 2 + t ^ 2) :
    ((2 * s * t / (R * a ^ 2) + Complex.I / 2 * (-2 * (s ^ 4 - s ^ 2 * t ^ 2 + 3 * s ^ 2 + t ^ 2 +
        2) / (R ^ 2 * a ^ 2))) * (((1 - s ^ 2) / (R * a)) - Complex.I * (-2 * s * t / (R ^ 2 *
        a))) - (t * (s ^ 2 - 1) / (R * a ^ 2) + Complex.I / 2 * (-2 * s * (s ^ 2 + 2 * t ^ 2 +
        1) / (R ^ 2 * a ^ 2))) * ((-2 * s / (R * a)) - Complex.I * (2 * t * (2 * s ^ 2 +
        1) / (R ^ 2 * a)))) * (2 * Complex.I * a ^ 2) ^ 3 * R ^ 3 = -2 * Complex.I * a ^ 3 *
        ((Complex.I * (R + a ^ 2) - s * t) ^ 3 + 3 * (Complex.I * (R + a ^ 2) - s * t) ^ 2 *
        (Complex.I * (R - a ^ 2) - s * t) - 3 * (Complex.I * (R + a ^ 2) - s * t) * (Complex.I *
        (R - a ^ 2) - s * t) ^ 2 - (Complex.I * (R - a ^ 2) - s * t) ^ 3) := by
  field_simp
  linear_combination (12 * Complex.I^3 * R^3 - 4 * Complex.I^3 * R * a^4 - 4 * Complex.I^3 * R * a^2
    * s^2 - 4 * Complex.I^3 * R * a^2 - 4 * Complex.I^3 * R * s^4 - 8 * Complex.I^3 * R * s^2 - 4 *
    Complex.I^3 * R - 24 * Complex.I^2 * R^2 * s * t + 12 * Complex.I * R * s^2 * t^2) * ha2 + (12 *
    Complex.I^3 * R * s^2 + 12 * Complex.I^3 * R - 24 * Complex.I^2 * s^3 * t - 24 * Complex.I^2 * s
    * t) * hR2 + (-24 * Complex.I^2 * s^5 * t - 24 * Complex.I^2 * s^3 * t^3 - 48 * Complex.I^2 *
    s^3 * t - 24 * Complex.I^2 * s * t^3 - 24 * Complex.I^2 * s * t + 12 * Complex.I * R * s^4 * t^2
    + 12 * Complex.I * R * s^2 * t^2) * Complex.I_sq

theorem holCoeff_zero_identity_generic (s t a R : ℂ) (ha : a ≠ 0) (hR : R ≠ 0)
    (ha2 : a ^ 2 = 1 + s ^ 2) (hR2 : R ^ 2 = 1 + s ^ 2 + t ^ 2) :
    ((2 * s * t / (R * a ^ 2) + Complex.I / 2 * (-2 * (s ^ 4 - s ^ 2 * t ^ 2 + 3 * s ^ 2 + t ^ 2 +
        2) / (R ^ 2 * a ^ 2))) * ((-(s * t) / (R * a)) - Complex.I * ((s ^ 2 - t ^ 2 +
        1) / (R ^ 2 * a))) - (-s / R + Complex.I / 2 * (2 * t / R ^ 2)) * ((-2 * s / (R * a)) -
        Complex.I * (2 * t * (2 * s ^ 2 + 1) / (R ^ 2 * a)))) * (2 * Complex.I * a ^ 2) ^ 3 *
        R ^ 3 = 2 * Complex.I * a ^ 3 * (Complex.I * ((Complex.I * (R + a ^ 2) - s * t) ^ 3 - 3 *
        (Complex.I * (R + a ^ 2) - s * t) ^ 2 * (Complex.I * (R - a ^ 2) - s * t) - 3 *
        (Complex.I * (R + a ^ 2) - s * t) * (Complex.I * (R - a ^ 2) - s * t) ^ 2 + (Complex.I *
        (R - a ^ 2) - s * t) ^ 3)) := by
  field_simp
  linear_combination (-12 * Complex.I^3 * R^2 * a^2 - 12 * Complex.I^3 * R^2 * s^2 - 12 *
    Complex.I^3 * R^2 + 16 * Complex.I^3 * s^2 * t^2 + 8 * Complex.I^3 * t^2 + 12 * Complex.I^2 * R
    * a^2 * s * t - 4 * Complex.I^2 * R * s^3 * t + 12 * Complex.I^2 * R * s * t - 8 * Complex.I *
    R^2 * s^2) * ha2 + (4 * Complex.I^3 * R^2 - 12 * Complex.I^3 * s^4 - 20 * Complex.I^3 * s^2 + 4
    * Complex.I^3 * t^2 - 8 * Complex.I^3 - 12 * Complex.I^2 * R * s * t - 8 * Complex.I * s^4 + 4 *
    Complex.I * s^2 * t^2 - 8 * Complex.I * s^2) * hR2 + (-8 * Complex.I * s^6 - 4 * Complex.I * s^4
    * t^2 - 16 * Complex.I * s^4 + 4 * Complex.I * s^2 * t^4 - 4 * Complex.I * s^2 * t^2 - 8 *
    Complex.I * s^2 - 4 * R * s^3 * t^3) * Complex.I_sq

theorem antiCoeff_one_identity_generic (s t a R : ℂ) (ha : a ≠ 0) (hR : R ≠ 0)
    (ha2 : a ^ 2 = 1 + s ^ 2) (hR2 : R ^ 2 = 1 + s ^ 2 + t ^ 2) :
    ((-(2 * s * t / (R * a ^ 2)) + Complex.I / 2 * (-2 * (s ^ 4 - s ^ 2 * t ^ 2 + 3 * s ^ 2 +
        t ^ 2 + 2) / (R ^ 2 * a ^ 2))) * (((1 - s ^ 2) / (R * a)) + Complex.I * (-2 * s *
        t / (R ^ 2 * a))) - (-(t * (s ^ 2 - 1) / (R * a ^ 2)) + Complex.I / 2 * (-2 * s * (s ^ 2 +
        2 * t ^ 2 + 1) / (R ^ 2 * a ^ 2))) * ((-2 * s / (R * a)) + Complex.I * (2 * t * (2 *
        s ^ 2 + 1) / (R ^ 2 * a)))) * (2 * Complex.I * a ^ 2) ^ 3 * R ^ 3 = -2 * Complex.I *
        a ^ 3 * ((Complex.I * (R + a ^ 2) + s * t) ^ 3 + 3 * (Complex.I * (R + a ^ 2) + s *
        t) ^ 2 * (Complex.I * (R - a ^ 2) + s * t) - 3 * (Complex.I * (R + a ^ 2) + s * t) *
        (Complex.I * (R - a ^ 2) + s * t) ^ 2 - (Complex.I * (R - a ^ 2) + s * t) ^ 3) := by
  field_simp
  linear_combination (12 * Complex.I^3 * R^3 - 4 * Complex.I^3 * R * a^4 - 4 * Complex.I^3 * R * a^2
    * s^2 - 4 * Complex.I^3 * R * a^2 - 4 * Complex.I^3 * R * s^4 - 8 * Complex.I^3 * R * s^2 - 4 *
    Complex.I^3 * R + 24 * Complex.I^2 * R^2 * s * t + 12 * Complex.I * R * s^2 * t^2) * ha2 + (12 *
    Complex.I^3 * R * s^2 + 12 * Complex.I^3 * R + 24 * Complex.I^2 * s^3 * t + 24 * Complex.I^2 * s
    * t) * hR2 + (24 * Complex.I^2 * s^5 * t + 24 * Complex.I^2 * s^3 * t^3 + 48 * Complex.I^2 * s^3
    * t + 24 * Complex.I^2 * s * t^3 + 24 * Complex.I^2 * s * t + 12 * Complex.I * R * s^4 * t^2 +
    12 * Complex.I * R * s^2 * t^2) * Complex.I_sq

theorem antiCoeff_zero_identity_generic (s t a R : ℂ) (ha : a ≠ 0) (hR : R ≠ 0)
    (ha2 : a ^ 2 = 1 + s ^ 2) (hR2 : R ^ 2 = 1 + s ^ 2 + t ^ 2) :
    ((-(2 * s * t / (R * a ^ 2)) + Complex.I / 2 * (-2 * (s ^ 4 - s ^ 2 * t ^ 2 + 3 * s ^ 2 +
        t ^ 2 + 2) / (R ^ 2 * a ^ 2))) * ((-(s * t) / (R * a)) + Complex.I * ((s ^ 2 - t ^ 2 +
        1) / (R ^ 2 * a))) - (-(-s / R) + Complex.I / 2 * (2 * t / R ^ 2)) * ((-2 * s / (R * a)) +
        Complex.I * (2 * t * (2 * s ^ 2 + 1) / (R ^ 2 * a)))) * (2 * Complex.I * a ^ 2) ^ 3 *
        R ^ 3 = 2 * Complex.I * a ^ 3 * (-Complex.I * ((Complex.I * (R + a ^ 2) + s * t) ^ 3 - 3 *
        (Complex.I * (R + a ^ 2) + s * t) ^ 2 * (Complex.I * (R - a ^ 2) + s * t) - 3 *
        (Complex.I * (R + a ^ 2) + s * t) * (Complex.I * (R - a ^ 2) + s * t) ^ 2 + (Complex.I *
        (R - a ^ 2) + s * t) ^ 3)) := by
  field_simp
  linear_combination (12 * Complex.I^3 * R^2 * a^2 + 12 * Complex.I^3 * R^2 * s^2 + 12 * Complex.I^3
    * R^2 - 16 * Complex.I^3 * s^2 * t^2 - 8 * Complex.I^3 * t^2 + 12 * Complex.I^2 * R * a^2 * s *
    t - 4 * Complex.I^2 * R * s^3 * t + 12 * Complex.I^2 * R * s * t + 8 * Complex.I * R^2 * s^2) *
    ha2 + (-4 * Complex.I^3 * R^2 + 12 * Complex.I^3 * s^4 + 20 * Complex.I^3 * s^2 - 4 *
    Complex.I^3 * t^2 + 8 * Complex.I^3 - 12 * Complex.I^2 * R * s * t + 8 * Complex.I * s^4 - 4 *
    Complex.I * s^2 * t^2 + 8 * Complex.I * s^2) * hR2 + (8 * Complex.I * s^6 + 4 * Complex.I * s^4
    * t^2 + 16 * Complex.I * s^4 - 4 * Complex.I * s^2 * t^4 + 4 * Complex.I * s^2 * t^2 + 8 *
    Complex.I * s^2 - 4 * R * s^3 * t^3) * Complex.I_sq

/-! ### The coefficients at the good-line coordinate -/

/-- The cubic `E³ + 3 E² N - 3 E N² - N³`. -/
def cubicP (E N : ℂ) : ℂ := E ^ 3 + 3 * E ^ 2 * N - 3 * E * N ^ 2 - N ^ 3

/-- The cubic `E³ - 3 E² N - 3 E N² + N³`. -/
def cubicQ (E N : ℂ) : ℂ := E ^ 3 - 3 * E ^ 2 * N - 3 * E * N ^ 2 + N ^ 3

/-- `E = i (R + α²) - s t`, so that `z + i = E / α²` for the Levi point `z = (i R - s t) / α²`. -/
def holE (u : ℝ × ℝ) : ℂ :=
  Complex.I * ((gsRadius u : ℂ) + (gsAlpha u : ℂ) ^ 2) - (u.1 : ℂ) * (u.2 : ℂ)

/-- `N = i (R - α²) - s t`, so that `z - i = N / α²`. -/
def holN (u : ℝ × ℝ) : ℂ :=
  Complex.I * ((gsRadius u : ℂ) - (gsAlpha u : ℂ) ^ 2) - (u.1 : ℂ) * (u.2 : ℂ)

/-- `E₂ = i (R + α²) + s t`, so that `refl(z) + i = E₂ / α²`. -/
def antiE (u : ℝ × ℝ) : ℂ :=
  Complex.I * ((gsRadius u : ℂ) + (gsAlpha u : ℂ) ^ 2) + (u.1 : ℂ) * (u.2 : ℂ)

/-- `N₂ = i (R - α²) + s t`, so that `refl(z) - i = N₂ / α²`. -/
def antiN (u : ℝ × ℝ) : ℂ :=
  Complex.I * ((gsRadius u : ℂ) - (gsAlpha u : ℂ) ^ 2) + (u.1 : ℂ) * (u.2 : ℂ)

theorem gsAlpha_complex_ne_zero (u : ℝ × ℝ) : (gsAlpha u : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (gsAlpha_pos u).ne'

theorem gsRadius_complex_ne_zero (u : ℝ × ℝ) : (gsRadius u : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (gsRadius_pos u).ne'

theorem gsAlpha_complex_sq (u : ℝ × ℝ) : (gsAlpha u : ℂ) ^ 2 = 1 + (u.1 : ℂ) ^ 2 := by
  exact_mod_cast gsAlpha_sq u

theorem gsRadius_complex_sq (u : ℝ × ℝ) :
    (gsRadius u : ℂ) ^ 2 = 1 + (u.1 : ℂ) ^ 2 + (u.2 : ℂ) ^ 2 := by
  exact_mod_cast gsRadius_sq u

/-- **The first holomorphic coefficient.** -/
theorem holCoeff_one_eq (u : ℝ × ℝ) :
    holCoeff u 1 * (2 * Complex.I * (gsAlpha u : ℂ) ^ 2) ^ 3 * (gsRadius u : ℂ) ^ 3 =
      -2 * Complex.I * (gsAlpha u : ℂ) ^ 3 * cubicP (holE u) (holN u) := by
  have key := holCoeff_one_identity_generic (u.1 : ℂ) (u.2 : ℂ) _ _
    (gsAlpha_complex_ne_zero u) (gsRadius_complex_ne_zero u) (gsAlpha_complex_sq u)
    (gsRadius_complex_sq u)
  simp only [holCoeff, radicalDeriv_eq_gram, pointDeriv_eq_gram, Fin.castSucc_zero,
    Fin.castSucc_one, gramFlow_02, gramFlow_12, gramFlow_01, gramFlow_diag, gramAxisOne_02,
    gramAxisOne_12, gramAxisOne_01, gramAxisOne_diag]
  push_cast
  simp only [cubicP, holE, holN]
  linear_combination key

/-- **The second holomorphic coefficient.** -/
theorem holCoeff_zero_eq (u : ℝ × ℝ) :
    holCoeff u 0 * (2 * Complex.I * (gsAlpha u : ℂ) ^ 2) ^ 3 * (gsRadius u : ℂ) ^ 3 =
      2 * Complex.I * (gsAlpha u : ℂ) ^ 3 * (Complex.I * cubicQ (holE u) (holN u)) := by
  have key := holCoeff_zero_identity_generic (u.1 : ℂ) (u.2 : ℂ) _ _
    (gsAlpha_complex_ne_zero u) (gsRadius_complex_ne_zero u) (gsAlpha_complex_sq u)
    (gsRadius_complex_sq u)
  simp only [holCoeff, radicalDeriv_eq_gram, pointDeriv_eq_gram, Fin.castSucc_zero,
    Fin.castSucc_one, gramFlow_02, gramFlow_12, gramFlow_01, gramFlow_diag, gramAxisZero_02,
    gramAxisZero_12, gramAxisZero_01, gramAxisZero_diag]
  push_cast
  simp only [cubicQ, holE, holN]
  linear_combination key

/-- **The first antiholomorphic coefficient.** -/
theorem antiCoeff_one_eq (u : ℝ × ℝ) :
    antiCoeff u 1 * (2 * Complex.I * (gsAlpha u : ℂ) ^ 2) ^ 3 * (gsRadius u : ℂ) ^ 3 =
      -2 * Complex.I * (gsAlpha u : ℂ) ^ 3 * cubicP (antiE u) (antiN u) := by
  have key := antiCoeff_one_identity_generic (u.1 : ℂ) (u.2 : ℂ) _ _
    (gsAlpha_complex_ne_zero u) (gsRadius_complex_ne_zero u) (gsAlpha_complex_sq u)
    (gsRadius_complex_sq u)
  simp only [antiCoeff, radicalDeriv_eq_gram, pointDeriv_eq_gram, binaryComplexReflection_parts,
    Fin.castSucc_zero, Fin.castSucc_one, gramFlow_02, gramFlow_12, gramFlow_01, gramFlow_diag,
    gramAxisOne_02, gramAxisOne_12, gramAxisOne_01, gramAxisOne_diag]
  push_cast
  simp only [cubicP, antiE, antiN]
  linear_combination key

/-- **The second antiholomorphic coefficient.** -/
theorem antiCoeff_zero_eq (u : ℝ × ℝ) :
    antiCoeff u 0 * (2 * Complex.I * (gsAlpha u : ℂ) ^ 2) ^ 3 * (gsRadius u : ℂ) ^ 3 =
      2 * Complex.I * (gsAlpha u : ℂ) ^ 3 * (-Complex.I * cubicQ (antiE u) (antiN u)) := by
  have key := antiCoeff_zero_identity_generic (u.1 : ℂ) (u.2 : ℂ) _ _
    (gsAlpha_complex_ne_zero u) (gsRadius_complex_ne_zero u) (gsAlpha_complex_sq u)
    (gsRadius_complex_sq u)
  simp only [antiCoeff, radicalDeriv_eq_gram, pointDeriv_eq_gram, binaryComplexReflection_parts,
    Fin.castSucc_zero, Fin.castSucc_one, gramFlow_02, gramFlow_12, gramFlow_01, gramFlow_diag,
    gramAxisZero_02, gramAxisZero_12, gramAxisZero_01, gramAxisZero_diag]
  push_cast
  simp only [cubicQ, antiE, antiN]
  linear_combination key

/-! ### The determinant and the entries of the complex matrix -/

theorem det_gsOrthMatrix (u : ℝ × ℝ) : (gsOrthMatrix u).det = -1 := by
  have ha := (gsAlpha_pos u).ne'
  have hr := (gsRadius_pos u).ne'
  have ha2 := gsAlpha_sq u
  have hR2 := gsRadius_sq u
  rw [Matrix.det_fin_three, gsOrthMatrix_00, gsOrthMatrix_01, gsOrthMatrix_02, gsOrthMatrix_10,
    gsOrthMatrix_11, gsOrthMatrix_12, gsOrthMatrix_20, gsOrthMatrix_21, gsOrthMatrix_22]
  field_simp
  linear_combination (gsRadius u ^ 2 - u.1 ^ 2 - 1) * ha2 + (u.1 ^ 2 + 1) * hR2

theorem complexOrth_apply (u : ℝ × ℝ) (a b : Fin 3) :
    complexOrth u a b = ((gsOrthMatrix u a b : ℝ) : ℂ) := rfl

end EdgeExplicit

end TernaryPeriodPolynomials.AnalyticClasses
