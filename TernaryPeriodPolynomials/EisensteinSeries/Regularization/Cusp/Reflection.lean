module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cohomological.ExtremalWeight

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binarySplitDirection_square : binarySplitDirection * binarySplitDirection = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [binarySplitDirection, Matrix.mul_apply, Fin.sum_univ_two]

def binaryReflection : BinaryRealGL :=
  ⟨binarySplitDirection, binarySplitDirection, binarySplitDirection_square, binarySplitDirection_square⟩

theorem binaryReflection_conjugate_rotation :
    binaryReflection.inv * binaryRotationDirection * binaryReflection.val = -binaryRotationDirection := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [binaryReflection, binarySplitDirection, binaryRotationDirection, Matrix.mul_apply, Fin.sum_univ_two]

theorem binaryReflection_conjugate_split :
    binaryReflection.inv * binarySplitDirection * binaryReflection.val = binarySplitDirection := by
  change (binarySplitDirection * binarySplitDirection) * binarySplitDirection = binarySplitDirection
  rw [binarySplitDirection_square, one_mul]

theorem binaryReflection_conjugate_symmetric :
    binaryReflection.inv * binarySymmetricDirection * binaryReflection.val = -binarySymmetricDirection := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [binaryReflection, binarySplitDirection, binarySymmetricDirection, Matrix.mul_apply, Fin.sum_univ_two]

theorem cuspRotation_reflection (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    cuspRotationOperator cusp (cuspSmoothAction cusp (atInfinity binaryReflection) vector) =
      -(cuspSmoothAction cusp (atInfinity binaryReflection) (cuspRotationOperator cusp vector)) := by
  change cuspDerivedAction cusp _ _ = _
  rw [cuspDerivedAction_real_covariance, binaryReflection_conjugate_rotation, map_neg, LinearMap.neg_apply, map_neg]
  rfl

theorem cuspSplit_reflection (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    cuspSplitOperator cusp (cuspSmoothAction cusp (atInfinity binaryReflection) vector) =
      cuspSmoothAction cusp (atInfinity binaryReflection) (cuspSplitOperator cusp vector) := by
  exact (cuspDerivedAction_real_covariance cusp binaryReflection binarySplitDirection vector).trans
    (by rw [binaryReflection_conjugate_split]; rfl)

theorem cuspSymmetric_reflection (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    cuspSymmetricOperator cusp (cuspSmoothAction cusp (atInfinity binaryReflection) vector) =
      -(cuspSmoothAction cusp (atInfinity binaryReflection) (cuspSymmetricOperator cusp vector)) := by
  change cuspDerivedAction cusp _ _ = _
  rw [cuspDerivedAction_real_covariance, binaryReflection_conjugate_symmetric, map_neg, LinearMap.neg_apply, map_neg]
  rfl

theorem cuspLowering_reflection (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    cuspLoweringOperator cusp (cuspSmoothAction cusp (atInfinity binaryReflection) vector) =
      cuspSmoothAction cusp (atInfinity binaryReflection) (cuspRaisingOperator cusp vector) := by
  simp only [cuspLoweringOperator, cuspRaisingOperator, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, cuspSplit_reflection, cuspSymmetric_reflection, map_add, map_smul]
  module

theorem cuspRaising_reflection (cusp : CuspidalRepresentation) (vector : cusp.smooth) :
    cuspRaisingOperator cusp (cuspSmoothAction cusp (atInfinity binaryReflection) vector) =
      cuspSmoothAction cusp (atInfinity binaryReflection) (cuspLoweringOperator cusp vector) := by
  simp only [cuspLoweringOperator, cuspRaisingOperator, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, cuspSplit_reflection, cuspSymmetric_reflection, map_sub, map_smul]
  module

theorem cuspSmoothAction_ne_zero (cusp : CuspidalRepresentation) (matrix : BinaryAdelicGL)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) : cuspSmoothAction cusp matrix vector ≠ 0 := by
  intro zero
  have hilbert_zero : cusp.π matrix vector.val = cusp.π matrix 0 := by
    simpa only [cuspSmoothAction_apply_val, Submodule.coe_zero, map_zero] using congrArg Subtype.val zero
  exact nonzero (Subtype.ext ((cuspUnitaryAction cusp matrix).injective hilbert_zero))

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
