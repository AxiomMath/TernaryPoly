module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RankOneOperators

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

attribute [local instance] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

theorem cuspRaising_lowering_adjoint (cusp : CuspidalRepresentation) (first second : cusp.smooth) :
    inner ℂ (cuspRaisingOperator cusp first).val second.val +
      inner ℂ first.val (cuspLoweringOperator cusp second).val = 0 := by
  have split := cuspDerivedAction_skew cusp binarySplitDirection first second
  have symmetric := cuspDerivedAction_skew cusp binarySymmetricDirection first second
  change inner ℂ ((cuspSplitOperator cusp first).val + Complex.I • (cuspSymmetricOperator cusp first).val)
      second.val + inner ℂ first.val
        ((cuspSplitOperator cusp second).val - Complex.I • (cuspSymmetricOperator cusp second).val) = 0
  simp only [inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  change inner ℂ (cuspSplitOperator cusp first).val second.val +
    inner ℂ first.val (cuspSplitOperator cusp second).val = 0 at split
  change inner ℂ (cuspSymmetricOperator cusp first).val second.val +
    inner ℂ first.val (cuspSymmetricOperator cusp second).val = 0 at symmetric
  linear_combination split - Complex.I * symmetric

theorem cuspLowering_raising_adjoint (cusp : CuspidalRepresentation) (first second : cusp.smooth) :
    inner ℂ (cuspLoweringOperator cusp first).val second.val +
      inner ℂ first.val (cuspRaisingOperator cusp second).val = 0 := by
  have split := cuspDerivedAction_skew cusp binarySplitDirection first second
  have symmetric := cuspDerivedAction_skew cusp binarySymmetricDirection first second
  change inner ℂ ((cuspSplitOperator cusp first).val - Complex.I • (cuspSymmetricOperator cusp first).val)
      second.val + inner ℂ first.val
        ((cuspSplitOperator cusp second).val + Complex.I • (cuspSymmetricOperator cusp second).val) = 0
  simp only [inner_sub_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  change inner ℂ (cuspSplitOperator cusp first).val second.val +
    inner ℂ first.val (cuspSplitOperator cusp second).val = 0 at split
  change inner ℂ (cuspSymmetricOperator cusp first).val second.val +
    inner ℂ first.val (cuspSymmetricOperator cusp second).val = 0 at symmetric
  linear_combination split + Complex.I * symmetric

theorem cuspRaising_lowering_norm_difference (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    (‖(cuspRaisingOperator cusp vector).val‖ : ℂ) ^ 2 -
      (‖(cuspLoweringOperator cusp vector).val‖ : ℂ) ^ 2 =
      (-4 * Complex.I) * inner ℂ vector.val (cuspRotationOperator cusp vector).val := by
  have raising := cuspRaising_lowering_adjoint cusp vector (cuspRaisingOperator cusp vector)
  have lowering := cuspLowering_raising_adjoint cusp vector (cuspLoweringOperator cusp vector)
  have bracket := congrArg (fun operator : Module.End ℂ cusp.smooth =>
    inner ℂ vector.val (operator vector).val) (cuspRaising_lowering_bracket cusp)
  change inner ℂ vector.val
      ((cuspRaisingOperator cusp (cuspLoweringOperator cusp vector)).val -
        (cuspLoweringOperator cusp (cuspRaisingOperator cusp vector)).val) =
    inner ℂ vector.val ((-4 * Complex.I) • (cuspRotationOperator cusp vector).val) at bracket
  simp only [inner_sub_right, inner_smul_right] at bracket
  rw [inner_self_eq_norm_sq_to_K] at raising lowering
  linear_combination raising - lowering + bracket

theorem cuspRaising_lowering_norm_difference_of_weight (cusp : CuspidalRepresentation)
    (weight : ℝ) (vector : cusp.smooth)
    (eigenvector : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector) :
    ‖(cuspRaisingOperator cusp vector).val‖ ^ 2 -
      ‖(cuspLoweringOperator cusp vector).val‖ ^ 2 = 4 * weight * ‖vector.val‖ ^ 2 := by
  have difference := cuspRaising_lowering_norm_difference cusp vector
  rw [eigenvector, Submodule.coe_smul, inner_smul_right, inner_self_eq_norm_sq_to_K] at difference
  apply Complex.ofReal_injective
  push_cast
  rw [difference]
  calc
    (-4 * Complex.I) * (Complex.I * (weight : ℂ) * (‖vector.val‖ : ℂ) ^ 2) =
      (-4 : ℂ) * (Complex.I * Complex.I) * (weight : ℂ) * (‖vector.val‖ : ℂ) ^ 2 := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

theorem cuspRaising_weight (cusp : CuspidalRepresentation) (weight : ℂ) (vector : cusp.smooth)
    (eigenvector : cuspRotationOperator cusp vector = (Complex.I * weight) • vector) :
    cuspRotationOperator cusp (cuspRaisingOperator cusp vector) =
      (Complex.I * (weight + 2)) • (cuspRaisingOperator cusp vector) := by
  have bracket := congrArg (fun operator : Module.End ℂ cusp.smooth => operator vector)
    (cuspRotation_raising_bracket cusp)
  change cuspRotationOperator cusp (cuspRaisingOperator cusp vector) -
    cuspRaisingOperator cusp (cuspRotationOperator cusp vector) =
      (2 * Complex.I) • cuspRaisingOperator cusp vector at bracket
  rw [eigenvector, map_smul] at bracket
  rw [sub_eq_iff_eq_add] at bracket
  rw [bracket]
  module

theorem cuspLowering_weight (cusp : CuspidalRepresentation) (weight : ℂ) (vector : cusp.smooth)
    (eigenvector : cuspRotationOperator cusp vector = (Complex.I * weight) • vector) :
    cuspRotationOperator cusp (cuspLoweringOperator cusp vector) =
      (Complex.I * (weight - 2)) • (cuspLoweringOperator cusp vector) := by
  have bracket := congrArg (fun operator : Module.End ℂ cusp.smooth => operator vector)
    (cuspRotation_lowering_bracket cusp)
  change cuspRotationOperator cusp (cuspLoweringOperator cusp vector) -
    cuspLoweringOperator cusp (cuspRotationOperator cusp vector) =
      (-2 * Complex.I) • cuspLoweringOperator cusp vector at bracket
  rw [eigenvector, map_smul] at bracket
  rw [sub_eq_iff_eq_add] at bracket
  rw [bracket]
  module

theorem cuspRaising_ne_zero_of_positive_weight (cusp : CuspidalRepresentation)
    (weight : ℝ) (positive : 0 < weight) (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (eigenvector : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector) :
    cuspRaisingOperator cusp vector ≠ 0 := by
  intro zero_raising
  have difference := cuspRaising_lowering_norm_difference_of_weight cusp weight vector eigenvector
  rw [zero_raising, Submodule.coe_zero, norm_zero, zero_pow (by decide), zero_sub] at difference
  have vector_nonzero : vector.val ≠ 0 := by intro zero; exact nonzero (Subtype.ext zero)
  have norm_positive := norm_pos_iff.mpr vector_nonzero
  have right_positive : 0 < 4 * weight * ‖vector.val‖ ^ 2 :=
    mul_pos (mul_pos (by norm_num) positive) (sq_pos_of_pos norm_positive)
  linarith [sq_nonneg ‖(cuspLoweringOperator cusp vector).val‖]

theorem cuspLowering_ne_zero_of_negative_weight (cusp : CuspidalRepresentation)
    (weight : ℝ) (negative : weight < 0) (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (eigenvector : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector) :
    cuspLoweringOperator cusp vector ≠ 0 := by
  intro zero_lowering
  have difference := cuspRaising_lowering_norm_difference_of_weight cusp weight vector eigenvector
  rw [zero_lowering, Submodule.coe_zero, norm_zero, zero_pow (by decide), sub_zero] at difference
  have vector_nonzero : vector.val ≠ 0 := by intro zero; exact nonzero (Subtype.ext zero)
  have norm_positive := norm_pos_iff.mpr vector_nonzero
  have right_negative : 4 * weight * ‖vector.val‖ ^ 2 < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) negative) (sq_pos_of_pos norm_positive)
  linarith [sq_nonneg ‖(cuspRaisingOperator cusp vector).val‖]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
