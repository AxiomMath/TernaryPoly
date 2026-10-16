module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.RaisingLoweringNorms

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

attribute [local instance] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false

noncomputable def cuspCasimirOperator (cusp : CuspidalRepresentation) : Module.End ℂ cusp.smooth :=
  cuspSplitOperator cusp * cuspSplitOperator cusp +
    cuspSymmetricOperator cusp * cuspSymmetricOperator cusp -
      cuspRotationOperator cusp * cuspRotationOperator cusp

theorem cuspOperator_bracket_product (cusp : CuspidalRepresentation)
    (first second third : Module.End ℂ cusp.smooth) :
    ⁅first, second * third⁆ = ⁅first, second⁆ * third + second * ⁅first, third⁆ := by
  simp only [Ring.lie_def, sub_mul, mul_sub, mul_assoc]
  abel

theorem cuspRotation_casimir_bracket (cusp : CuspidalRepresentation) :
    ⁅cuspRotationOperator cusp, cuspCasimirOperator cusp⁆ = 0 := by
  rw [cuspCasimirOperator]
  simp only [lie_sub, lie_add, cuspOperator_bracket_product,
    cuspRotation_split_bracket, cuspRotation_symmetric_bracket, lie_self, zero_mul, mul_zero,
    zero_add, sub_zero]
  apply LinearMap.ext
  intro vector
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.zero_apply,
    map_add, map_neg, two_smul]
  abel

theorem cuspSplit_casimir_bracket (cusp : CuspidalRepresentation) :
    ⁅cuspSplitOperator cusp, cuspCasimirOperator cusp⁆ = 0 := by
  have reverse : ⁅cuspSplitOperator cusp, cuspRotationOperator cusp⁆ = 2 • cuspSymmetricOperator cusp := by
    rw [← lie_skew, cuspRotation_split_bracket, neg_neg]
  rw [cuspCasimirOperator]
  simp only [lie_sub, lie_add, cuspOperator_bracket_product,
    cuspSplit_symmetric_bracket, reverse, lie_self, zero_mul, mul_zero, zero_add,
    two_smul, add_mul, mul_add]
  abel

theorem cuspSymmetric_casimir_bracket (cusp : CuspidalRepresentation) :
    ⁅cuspSymmetricOperator cusp, cuspCasimirOperator cusp⁆ = 0 := by
  have reverse_rotation : ⁅cuspSymmetricOperator cusp, cuspRotationOperator cusp⁆ =
      -(2 • cuspSplitOperator cusp) := by rw [← lie_skew, cuspRotation_symmetric_bracket]
  have reverse_split : ⁅cuspSymmetricOperator cusp, cuspSplitOperator cusp⁆ =
      -(2 • cuspRotationOperator cusp) := by rw [← lie_skew, cuspSplit_symmetric_bracket]
  rw [cuspCasimirOperator]
  simp only [lie_sub, lie_add, cuspOperator_bracket_product, reverse_rotation, reverse_split,
    lie_self, zero_mul, mul_zero, add_zero]
  apply LinearMap.ext
  intro vector
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.zero_apply, map_add, map_neg, two_smul]
  abel

theorem cuspRaising_lowering_product (cusp : CuspidalRepresentation) :
    cuspRaisingOperator cusp * cuspLoweringOperator cusp =
      cuspCasimirOperator cusp + cuspRotationOperator cusp * cuspRotationOperator cusp -
        (2 * Complex.I) • cuspRotationOperator cusp := by
  calc
    _ = cuspSplitOperator cusp * cuspSplitOperator cusp +
        cuspSymmetricOperator cusp * cuspSymmetricOperator cusp -
          Complex.I • ⁅cuspSplitOperator cusp, cuspSymmetricOperator cusp⁆ := by
      simp only [cuspRaisingOperator, cuspLoweringOperator, Ring.lie_def, add_mul, mul_sub,
        smul_add, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I, neg_one_smul, smul_sub]
      abel
    _ = _ := by
      rw [cuspSplit_symmetric_bracket, cuspCasimirOperator]
      module

theorem cuspLowering_raising_product (cusp : CuspidalRepresentation) :
    cuspLoweringOperator cusp * cuspRaisingOperator cusp =
      cuspCasimirOperator cusp + cuspRotationOperator cusp * cuspRotationOperator cusp +
        (2 * Complex.I) • cuspRotationOperator cusp := by
  have bracket := cuspRaising_lowering_bracket cusp
  rw [Ring.lie_def, cuspRaising_lowering_product] at bracket
  calc
    _ = (cuspCasimirOperator cusp + cuspRotationOperator cusp * cuspRotationOperator cusp -
        (2 * Complex.I) • cuspRotationOperator cusp) -
          (-4 * Complex.I) • cuspRotationOperator cusp := by
      apply eq_sub_iff_add_eq.mpr
      rw [add_comm]
      exact (sub_eq_iff_eq_add.mp bracket).symm
    _ = _ := by module

theorem cuspDerivedAction_square_symmetric (cusp : CuspidalRepresentation)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) (first second : cusp.smooth) :
    inner ℂ (cuspDerivedAction cusp direction (cuspDerivedAction cusp direction first)).val second.val =
      inner ℂ first.val (cuspDerivedAction cusp direction (cuspDerivedAction cusp direction second)).val := by
  have first_skew := cuspDerivedAction_skew cusp direction (cuspDerivedAction cusp direction first) second
  have second_skew := cuspDerivedAction_skew cusp direction first (cuspDerivedAction cusp direction second)
  linear_combination first_skew - second_skew

theorem cuspCasimirOperator_symmetric (cusp : CuspidalRepresentation) (first second : cusp.smooth) :
    inner ℂ (cuspCasimirOperator cusp first).val second.val =
      inner ℂ first.val (cuspCasimirOperator cusp second).val := by
  change inner ℂ
    ((cuspDerivedAction cusp binarySplitDirection (cuspDerivedAction cusp binarySplitDirection first)).val +
      (cuspDerivedAction cusp binarySymmetricDirection (cuspDerivedAction cusp binarySymmetricDirection first)).val -
        (cuspDerivedAction cusp binaryRotationDirection (cuspDerivedAction cusp binaryRotationDirection first)).val)
    second.val = inner ℂ first.val
    ((cuspDerivedAction cusp binarySplitDirection (cuspDerivedAction cusp binarySplitDirection second)).val +
      (cuspDerivedAction cusp binarySymmetricDirection (cuspDerivedAction cusp binarySymmetricDirection second)).val -
        (cuspDerivedAction cusp binaryRotationDirection (cuspDerivedAction cusp binaryRotationDirection second)).val)
  simp only [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
    cuspDerivedAction_square_symmetric]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
