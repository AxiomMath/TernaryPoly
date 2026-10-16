module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Lie.Casimir

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieDifferentiation
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieNorms TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieCasimir

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirNorms

theorem directional_square_inner (data : CuspidalRepresentation) (first second : data.smooth)
    (direction : BinaryMatrix) :
    inner ℂ first.val ((directionalOperator data direction ^ 2) second).val =
      inner ℂ ((directionalOperator data direction ^ 2) first).val second.val := by
  have left := directionalOperator_inner data first (directionalOperator data direction second) direction
  have right := directionalOperator_inner data (directionalOperator data direction first) second direction
  simp only [pow_two, Module.End.mul_apply]
  linear_combination left - right

theorem casimir_inner (data : CuspidalRepresentation) (first second : data.smooth) :
    inner ℂ first.val (casimir data second).val = inner ℂ (casimir data first).val second.val := by
  change inner ℂ first.val (((diagonalOperator data ^ 2) second).val +
      ((symmetricOperator data ^ 2) second).val - ((rotationOperator data ^ 2) second).val) =
    inner ℂ (((diagonalOperator data ^ 2) first).val +
      ((symmetricOperator data ^ 2) first).val - ((rotationOperator data ^ 2) first).val) second.val
  simp only [inner_sub_right, inner_add_right, inner_sub_left, inner_add_left]
  have diagonal : inner ℂ first.val ((diagonalOperator data ^ 2) second).val =
      inner ℂ ((diagonalOperator data ^ 2) first).val second.val :=
    directional_square_inner data first second diagonalMatrix
  have symmetric : inner ℂ first.val ((symmetricOperator data ^ 2) second).val =
      inner ℂ ((symmetricOperator data ^ 2) first).val second.val :=
    directional_square_inner data first second symmetricMatrix
  have rotation : inner ℂ first.val ((rotationOperator data ^ 2) second).val =
      inner ℂ ((rotationOperator data ^ 2) first).val second.val :=
    directional_square_inner data first second rotationMatrix
  rw [diagonal, symmetric, rotation]

theorem casimir_eigen_real (data : CuspidalRepresentation) (vector : data.smooth)
    (nonzero : vector ≠ 0) (value : ℂ) (eigen : casimir data vector = value • vector) : value.im = 0 := by
  have equality := casimir_inner data vector vector
  rw [eigen] at equality
  change inner ℂ vector.val (value • vector.val) = inner ℂ (value • vector.val) vector.val at equality
  rw [inner_smul_right, inner_smul_left, inner_self_eq_norm_sq_to_K] at equality
  have vectorNonzero : vector.val ≠ 0 := by
    intro vanishing
    exact nonzero (Subtype.ext vanishing)
  have normNonzero : (‖vector.val‖ : ℂ) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (norm_ne_zero_iff.mpr vectorNonzero)
  have scalarEquality : value = starRingEnd ℂ value := mul_right_cancel₀ normNonzero equality
  have imaginaryEquality := congrArg Complex.im scalarEquality
  rw [Complex.conj_im] at imaginaryEquality
  linarith

theorem raising_norm_sq (data : CuspidalRepresentation) (vector : data.smooth)
    (index : ℤ) (value : ℝ)
    (rotationEigen : rotationOperator data vector = (Complex.I * index) • vector)
    (casimirEigen : casimir data vector = (value : ℂ) • vector) :
    ‖(raising data vector).val‖ ^ 2 = ((index : ℝ) * (index + 2) - value) * ‖vector.val‖ ^ 2 := by
  have equality := lowering_inner data vector (raising data vector)
  rw [lowering_raising_of_eigen data vector index value rotationEigen casimirEigen] at equality
  change inner ℂ vector.val (((value : ℂ) - (index : ℂ) * (index + 2)) • vector.val) +
    inner ℂ (raising data vector).val (raising data vector).val = 0 at equality
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at equality
  have complexEquality : (‖(raising data vector).val‖ : ℂ) ^ 2 =
      ((index : ℂ) * (index + 2) - value) * (‖vector.val‖ : ℂ) ^ 2 := by
    linear_combination equality
  exact_mod_cast complexEquality

theorem lowering_norm_sq (data : CuspidalRepresentation) (vector : data.smooth)
    (index : ℤ) (value : ℝ)
    (rotationEigen : rotationOperator data vector = (Complex.I * index) • vector)
    (casimirEigen : casimir data vector = (value : ℂ) • vector) :
    ‖(lowering data vector).val‖ ^ 2 = ((index : ℝ) * (index - 2) - value) * ‖vector.val‖ ^ 2 := by
  have equality := raising_inner data vector (lowering data vector)
  rw [raising_lowering_of_eigen data vector index value rotationEigen casimirEigen] at equality
  change inner ℂ vector.val (((value : ℂ) - (index : ℂ) * (index - 2)) • vector.val) +
    inner ℂ (lowering data vector).val (lowering data vector).val = 0 at equality
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at equality
  have complexEquality : (‖(lowering data vector).val‖ : ℂ) ^ 2 =
      ((index : ℂ) * (index - 2) - value) * (‖vector.val‖ : ℂ) ^ 2 := by
    linear_combination equality
  exact_mod_cast complexEquality

theorem raising_coefficient_nonneg (data : CuspidalRepresentation) (vector : data.smooth)
    (nonzero : vector ≠ 0) (index : ℤ) (value : ℝ)
    (rotationEigen : rotationOperator data vector = (Complex.I * index) • vector)
    (casimirEigen : casimir data vector = (value : ℂ) • vector) :
    value ≤ (index : ℝ) * (index + 2) := by
  have identity := raising_norm_sq data vector index value rotationEigen casimirEigen
  have normPositive : 0 < ‖vector.val‖ ^ 2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro vanishing
    exact nonzero (Subtype.ext vanishing)
  have coefficientNonnegative : 0 ≤ (index : ℝ) * (index + 2) - value :=
    nonneg_of_mul_nonneg_left (identity ▸ sq_nonneg _) normPositive
  linarith

theorem lowering_coefficient_nonneg (data : CuspidalRepresentation) (vector : data.smooth)
    (nonzero : vector ≠ 0) (index : ℤ) (value : ℝ)
    (rotationEigen : rotationOperator data vector = (Complex.I * index) • vector)
    (casimirEigen : casimir data vector = (value : ℂ) • vector) :
    value ≤ (index : ℝ) * (index - 2) := by
  have identity := lowering_norm_sq data vector index value rotationEigen casimirEigen
  have normPositive : 0 < ‖vector.val‖ ^ 2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro vanishing
    exact nonzero (Subtype.ext vanishing)
  have coefficientNonnegative : 0 ≤ (index : ℝ) * (index - 2) - value :=
    nonneg_of_mul_nonneg_left (identity ▸ sq_nonneg _) normPositive
  linarith

theorem lowest_weight_casimir (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (rotationEigen : rotationOperator data vector = (Complex.I * index) • vector)
    (lowest : lowering data vector = 0) :
    casimir data vector = ((index : ℂ) * (index - 2)) • vector := by
  have equality := congrArg (fun operator : Module.End ℂ data.smooth => operator vector) (raising_mul_lowering data)
  change raising data (lowering data vector) = casimir data vector +
    (rotationOperator data ^ 2) vector - (2 * Complex.I) • rotationOperator data vector at equality
  rw [lowest, map_zero, rotation_sq_eigen data vector index rotationEigen, rotationEigen, smul_smul] at equality
  have solved : casimir data vector = (2 * Complex.I * (Complex.I * index)) • vector -
      (-(index : ℂ) ^ 2) • vector := by
    rw [eq_comm, sub_eq_zero] at equality
    exact eq_sub_iff_add_eq.mpr equality
  rw [solved]
  simp only [mul_assoc, ← mul_assoc Complex.I, Complex.I_mul_I, neg_mul, one_mul, mul_neg]
  module

theorem highest_weight_casimir (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (rotationEigen : rotationOperator data vector = (Complex.I * index) • vector)
    (highest : raising data vector = 0) :
    casimir data vector = ((index : ℂ) * (index + 2)) • vector := by
  have equality := congrArg (fun operator : Module.End ℂ data.smooth => operator vector) (lowering_mul_raising data)
  change lowering data (raising data vector) = casimir data vector +
    (rotationOperator data ^ 2) vector + (2 * Complex.I) • rotationOperator data vector at equality
  rw [highest, map_zero, rotation_sq_eigen data vector index rotationEigen, rotationEigen, smul_smul] at equality
  have solved : casimir data vector = -(2 * Complex.I * (Complex.I * index)) • vector -
      (-(index : ℂ) ^ 2) • vector := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left equality.symm
  rw [solved]
  simp only [mul_assoc, ← mul_assoc Complex.I, Complex.I_mul_I, neg_mul, one_mul, mul_neg]
  module

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirNorms
