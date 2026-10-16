module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.ConjugateRotation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def binaryRotationScale : BinaryRealGL :=
  ⟨!![2, 0; 0, 1], !![1 / 2, 0; 0, 1], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem binaryRotationScale_conjugate :
    binaryRotationScale.inv * binaryRotationDirection * binaryRotationScale.val =
      (5 / 4 : ℝ) • binaryRotationDirection - (3 / 4 : ℝ) • binarySymmetricDirection := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [binaryRotationScale, binaryRotationDirection, binarySymmetricDirection, Matrix.mul_apply, Fin.sum_univ_two]

theorem binaryUnipotent_conjugate_rotation :
    (binaryUnipotent (1 : ℝ)).inv * binaryRotationDirection * (binaryUnipotent (1 : ℝ)).val =
      binarySplitDirection + (3 / 2 : ℝ) • binaryRotationDirection + (1 / 2 : ℝ) • binarySymmetricDirection := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [binaryUnipotent, binaryRotationDirection, binarySplitDirection, binarySymmetricDirection,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem binary_linear_zero_of_rotation_conjugates {V : Type*} [AddCommGroup V] [Module ℝ V]
    (functional : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] V)
    (vanishes : ∀ matrix : BinaryRealGL, functional (matrix.inv * binaryRotationDirection * matrix.val) = 0)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) (traceless : Matrix.trace direction = 0) :
    functional direction = 0 := by
  have rotation : functional binaryRotationDirection = 0 := by simpa using vanishes 1
  have scaled := vanishes binaryRotationScale
  rw [binaryRotationScale_conjugate, map_sub, map_smul, map_smul, rotation, smul_zero, zero_sub, neg_eq_zero] at scaled
  have symmetric : functional binarySymmetricDirection = 0 :=
    (smul_eq_zero.mp scaled).resolve_left (by norm_num)
  have split := vanishes (binaryUnipotent (1 : ℝ))
  rw [binaryUnipotent_conjugate_rotation, map_add, map_add, map_smul, map_smul,
    rotation, symmetric, smul_zero, smul_zero, add_zero, add_zero] at split
  rw [binary_traceless_decomposition direction traceless]
  simp only [map_add, map_smul, split, symmetric, rotation, smul_zero, add_zero]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
