module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Lie.Operators

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieNorms

theorem raising_inner (data : CuspidalRepresentation) (first second : data.smooth) :
    inner ℂ first.val (raising data second).val +
      inner ℂ (lowering data first).val second.val = 0 := by
  have diagonal := directionalOperator_inner data first second diagonalMatrix
  have symmetric := directionalOperator_inner data first second symmetricMatrix
  change inner ℂ first.val ((diagonalOperator data second).val - Complex.I • (symmetricOperator data second).val) +
    inner ℂ ((diagonalOperator data first).val + Complex.I • (symmetricOperator data first).val) second.val = 0
  simp only [inner_sub_right, inner_add_left, inner_smul_right, inner_smul_left, Complex.conj_I]
  change inner ℂ first.val (diagonalOperator data second).val +
    inner ℂ (diagonalOperator data first).val second.val = 0 at diagonal
  change inner ℂ first.val (symmetricOperator data second).val +
    inner ℂ (symmetricOperator data first).val second.val = 0 at symmetric
  linear_combination diagonal - Complex.I * symmetric

theorem lowering_inner (data : CuspidalRepresentation) (first second : data.smooth) :
    inner ℂ first.val (lowering data second).val +
      inner ℂ (raising data first).val second.val = 0 := by
  have diagonal := directionalOperator_inner data first second diagonalMatrix
  have symmetric := directionalOperator_inner data first second symmetricMatrix
  change inner ℂ first.val ((diagonalOperator data second).val + Complex.I • (symmetricOperator data second).val) +
    inner ℂ ((diagonalOperator data first).val - Complex.I • (symmetricOperator data first).val) second.val = 0
  simp only [inner_add_right, inner_sub_left, inner_smul_right, inner_smul_left, Complex.conj_I]
  change inner ℂ first.val (diagonalOperator data second).val +
    inner ℂ (diagonalOperator data first).val second.val = 0 at diagonal
  change inner ℂ first.val (symmetricOperator data second).val +
    inner ℂ (symmetricOperator data first).val second.val = 0 at symmetric
  linear_combination diagonal + Complex.I * symmetric

theorem lowering_raising_eigen (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (eigen : rotationOperator data vector = (Complex.I * index) • vector) :
    lowering data (raising data vector) - raising data (lowering data vector) =
      (-4 * (index : ℂ)) • vector := by
  have equality := congrArg (fun operator : Module.End ℂ data.smooth => operator vector) (lowering_raising data)
  change lowering data (raising data vector) - raising data (lowering data vector) =
    (4 * Complex.I) • rotationOperator data vector at equality
  rw [eigen, smul_smul] at equality
  simpa only [mul_assoc, ← mul_assoc Complex.I, Complex.I_mul_I, mul_neg_one, neg_mul,
    one_mul, mul_neg] using equality

/-- The two ladder norms differ by the actual rotation weight. -/
theorem raising_lowering_norm_sq (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (eigen : rotationOperator data vector = (Complex.I * index) • vector) :
    ‖(raising data vector).val‖ ^ 2 - ‖(lowering data vector).val‖ ^ 2 =
      4 * (index : ℝ) * ‖vector.val‖ ^ 2 := by
  have raisingSkew := lowering_inner data vector (raising data vector)
  have loweringSkew := raising_inner data vector (lowering data vector)
  have commutation := congrArg (fun value : data.smooth => inner ℂ vector.val value.val)
    (lowering_raising_eigen data vector index eigen)
  change inner ℂ vector.val ((lowering data (raising data vector)).val -
    (raising data (lowering data vector)).val) = inner ℂ vector.val ((-4 * (index : ℂ)) • vector.val) at commutation
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K] at commutation
  rw [inner_self_eq_norm_sq_to_K] at raisingSkew loweringSkew
  have complexEquality : (‖(raising data vector).val‖ : ℂ) ^ 2 -
      (‖(lowering data vector).val‖ : ℂ) ^ 2 = 4 * (index : ℂ) * (‖vector.val‖ : ℂ) ^ 2 := by
    linear_combination raisingSkew - loweringSkew - commutation
  exact_mod_cast complexEquality

theorem eq_zero_of_raising_eq_zero_of_positive (data : CuspidalRepresentation) (vector : data.smooth)
    (index : ℤ) (positive : 0 < index)
    (eigen : rotationOperator data vector = (Complex.I * index) • vector)
    (vanishing : raising data vector = 0) : vector = 0 := by
  have identity := raising_lowering_norm_sq data vector index eigen
  have zeroNorm : ‖(raising data vector).val‖ = 0 := by rw [vanishing]; simp
  rw [zeroNorm] at identity
  have indexPositive : (0 : ℝ) < index := by exact_mod_cast positive
  have vectorNorm : ‖vector.val‖ = 0 := by
    apply le_antisymm ?_ (norm_nonneg _)
    by_contra! positiveNorm
    have rhsPositive : 0 < 4 * (index : ℝ) * ‖vector.val‖ ^ 2 := by positivity
    nlinarith [sq_nonneg ‖(lowering data vector).val‖]
  exact Subtype.ext (norm_eq_zero.mp vectorNorm)

theorem eq_zero_of_lowering_eq_zero_of_negative (data : CuspidalRepresentation) (vector : data.smooth)
    (index : ℤ) (negative : index < 0)
    (eigen : rotationOperator data vector = (Complex.I * index) • vector)
    (vanishing : lowering data vector = 0) : vector = 0 := by
  have identity := raising_lowering_norm_sq data vector index eigen
  have zeroNorm : ‖(lowering data vector).val‖ = 0 := by rw [vanishing]; simp
  rw [zeroNorm] at identity
  have indexNegative : (index : ℝ) < 0 := by exact_mod_cast negative
  have vectorNorm : ‖vector.val‖ = 0 := by
    apply le_antisymm ?_ (norm_nonneg _)
    by_contra! positiveNorm
    have rhsNegative : 4 * (index : ℝ) * ‖vector.val‖ ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos positiveNorm)
    nlinarith [sq_nonneg ‖(raising data vector).val‖]
  exact Subtype.ext (norm_eq_zero.mp vectorNorm)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieNorms
