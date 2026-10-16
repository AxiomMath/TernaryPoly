module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.SmallDivisorKernel
public import Mathlib.NumberTheory.Transcendental.Liouville.Basic
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Algebra.Polynomial.DenomsClearable
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

@[expose] public section


open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SqrtTwoApproximation

theorem exists_approximation_constant : ∃ bound : ℝ, 0 < bound ∧
    ∀ (numerator : ℤ) (denominator : ℕ),
      1 ≤ ((denominator : ℝ) + 1) ^ 2 *
        (|Real.sqrt 2 - numerator / (denominator + 1)| * bound) := by
  have root : Polynomial.eval (Real.sqrt 2)
      (Polynomial.map (algebraMap ℤ ℝ) ((Polynomial.X : Polynomial ℤ) ^ 2 - Polynomial.C 2)) = 0 := by
    simp [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have estimate := Liouville.exists_pos_real_of_irrational_root irrational_sqrt_two
    (Polynomial.X_pow_sub_C_ne_zero (show 0 < 2 by norm_num) (2 : ℤ)) root
  simpa only [Polynomial.natDegree_X_pow_sub_C] using estimate

theorem norm_exp_sub_one_lower_bound (value : ℝ) (small : |value| ≤ 1 / 2) :
    4 * |value| ≤ ‖Complex.exp (Complex.I * (2 * Real.pi * value : ℝ)) - 1‖ := by
  have near : |Real.pi * value| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [mul_le_mul_of_nonneg_left small Real.pi_pos.le]
  have sine := Real.mul_abs_le_abs_sin near
  rw [abs_mul, abs_of_pos Real.pi_pos] at sine
  have simplification : 2 / Real.pi * (Real.pi * |value|) = 2 * |value| := by
    field_simp
  rw [simplification] at sine
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have half : 2 * Real.pi * value / 2 = Real.pi * value := by ring
  rw [half, Real.norm_eq_abs, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  linarith

theorem fourier_one_eq_exp (value : ℝ) :
    fourier 1 (value : Parameter) = Complex.exp (Complex.I * (2 * Real.pi * value : ℝ)) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem fourier_norm_sub_one_lower_bound (value : ℝ) (integer : ℤ) (near : |value - integer| ≤ 1 / 2) :
    4 * |value - integer| ≤ ‖fourier 1 (value : Parameter) - 1‖ := by
  have integerZero : ((integer : ℝ) : Parameter) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨integer, by simp⟩
  have quotientEquality : ((value - integer : ℝ) : Parameter) = (value : Parameter) := by
    rw [AddCircle.coe_sub, integerZero, sub_zero]
  have equality : fourier 1 (value : Parameter) = Complex.exp (Complex.I * (2 * Real.pi * (value - integer) : ℝ)) := by
    rw [← quotientEquality, fourier_one_eq_exp]
  rw [equality]
  exact norm_exp_sub_one_lower_bound (value - integer) near

theorem fourier_mul_int_argument (index : ℤ) (value : ℝ) :
    fourier index (value : Parameter) = fourier 1 (((index : ℝ) * value : ℝ) : Parameter) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem exists_fourier_lower_bound : ∃ bound : ℝ, 0 < bound ∧ ∀ denominator : ℕ,
    4 ≤ ((denominator : ℝ) + 1) * bound *
      ‖fourier ((denominator : ℤ) + 1) (Real.sqrt 2 : Parameter) - 1‖ := by
  obtain ⟨bound, positiveBound, approximation⟩ := exists_approximation_constant
  refine ⟨bound, positiveBound, ?_⟩
  intro denominator
  let integer := round (((denominator : ℝ) + 1) * Real.sqrt 2)
  have positiveDenominator : (0 : ℝ) < denominator + 1 := by positivity
  have approximationBound := approximation integer denominator
  have scalarEquality : Real.sqrt 2 - integer / ((denominator : ℝ) + 1) =
      (((denominator : ℝ) + 1) * Real.sqrt 2 - integer) / ((denominator : ℝ) + 1) := by
    field_simp
  have productEquality : ((denominator : ℝ) + 1) ^ 2 *
      (|Real.sqrt 2 - integer / ((denominator : ℝ) + 1)| * bound) =
      ((denominator : ℝ) + 1) * bound * |((denominator : ℝ) + 1) * Real.sqrt 2 - integer| := by
    rw [scalarEquality, abs_div, abs_of_pos positiveDenominator]
    field_simp
  rw [productEquality] at approximationBound
  have near := abs_sub_round (((denominator : ℝ) + 1) * Real.sqrt 2)
  have trigonometricBound := fourier_norm_sub_one_lower_bound
    (((denominator : ℝ) + 1) * Real.sqrt 2) integer near
  have multipliedBound := mul_le_mul_of_nonneg_left trigonometricBound
    (mul_pos positiveDenominator positiveBound).le
  rw [fourier_mul_int_argument]
  push_cast
  nlinarith

theorem fourier_neg_sub_one_norm (index : ℤ) (parameter : Parameter) :
    ‖fourier (-index) parameter - 1‖ = ‖fourier index parameter - 1‖ := by
  calc
    _ = ‖fourier index parameter * (fourier (-index) parameter - 1)‖ := by
      rw [norm_mul, fourier_norm_one, one_mul]
    _ = ‖1 - fourier index parameter‖ := by rw [mul_sub, fourier_mul_neg, mul_one]
    _ = _ := norm_sub_rev _ _

theorem exists_inverse_bound : ∃ bound : ℝ, 0 < bound ∧ ∀ index : ℤ,
    ‖(fourier index (Real.sqrt 2 : Parameter) - 1)⁻¹‖ ≤ bound * |(index : ℝ)| := by
  obtain ⟨bound, positiveBound, estimate⟩ := exists_fourier_lower_bound
  refine ⟨bound / 4, by positivity, ?_⟩
  have naturalBound (index : ℕ) :
      ‖(fourier (index : ℤ) (Real.sqrt 2 : Parameter) - 1)⁻¹‖ ≤ bound / 4 * (index : ℝ) := by
    cases index with
    | zero => simp
    | succ index =>
        have lower := estimate index
        have positiveNorm : 0 < ‖fourier ((index : ℤ) + 1) (Real.sqrt 2 : Parameter) - 1‖ := by
          by_contra nonpositive
          have normZero := le_antisymm (le_of_not_gt nonpositive) (norm_nonneg _)
          rw [normZero, mul_zero] at lower
          norm_num at lower
        rw [Nat.cast_succ, Nat.cast_succ, norm_inv, inv_eq_one_div, div_le_iff₀ positiveNorm]
        nlinarith
  intro index
  cases index with
  | ofNat index =>
      change ‖(fourier (index : ℤ) (Real.sqrt 2 : Parameter) - 1)⁻¹‖ ≤ bound / 4 * |(index : ℝ)|
      simpa only [abs_of_nonneg (Nat.cast_nonneg index : (0 : ℝ) ≤ index)] using naturalBound index
  | negSucc index =>
      change ‖(fourier (-((index + 1 : ℕ) : ℤ)) (Real.sqrt 2 : Parameter) - 1)⁻¹‖ ≤ _
      rw [norm_inv, fourier_neg_sub_one_norm, ← norm_inv]
      simpa only [Int.cast_negSucc, abs_neg, Nat.cast_add, Nat.cast_one,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ index + 1)] using naturalBound (index + 1)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SqrtTwoApproximation
