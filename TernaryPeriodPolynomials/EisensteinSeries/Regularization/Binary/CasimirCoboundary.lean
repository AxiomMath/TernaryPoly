module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CohomologicalMixedBrackets
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CocycleLieIdentity

@[expose] public section


open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binary_rankOne_directions_traceless :
    Matrix.trace binaryRotationDirection = 0 ∧ Matrix.trace binarySplitDirection = 0 ∧
      Matrix.trace binarySymmetricDirection = 0 := by
  norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two, binaryRotationDirection,
    binarySplitDirection, binarySymmetricDirection]

theorem binaryCohomological_difference_casimir_scalar (cusp : CuspidalRepresentation) (degree : ℕ)
    (scalar : ℂ) (casimir : cuspCasimirOperator cusp = scalar • 1) :
    binaryCohomologicalDifferenceOperator cusp degree binarySplitDirection *
        binaryCohomologicalDerivedOperator cusp degree binarySplitDirection +
      binaryCohomologicalDifferenceOperator cusp degree binarySymmetricDirection *
        binaryCohomologicalDerivedOperator cusp degree binarySymmetricDirection -
      binaryCohomologicalDifferenceOperator cusp degree binaryRotationDirection *
        binaryCohomologicalDerivedOperator cusp degree binaryRotationDirection =
      (scalar - ((degree : ℂ) + 1) * ((degree : ℂ) + 3)) • 1 := by
  rw [binaryCohomological_difference_casimir, casimir, map_smul, map_one]
  module

theorem binary_lie_cocycle_coboundary_of_distinct_casimir
    (cusp : CuspidalRepresentation) (degree : ℕ) (scalar : ℂ)
    (casimir : cuspCasimirOperator cusp = scalar • 1)
    (distinct : scalar ≠ ((degree : ℂ) + 1) * ((degree : ℂ) + 3))
    (cocycle : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] (BinaryDegreeMonomial (degree + 1) → cusp.smooth))
    (lie_identity : ∀ first second, Matrix.trace first = 0 → Matrix.trace second = 0 →
      cocycle (first * second - second * first) =
        binaryCohomologicalDerivedOperator cusp degree first (cocycle second) -
          binaryCohomologicalDerivedOperator cusp degree second (cocycle first)) :
    ∃ vector : BinaryDegreeMonomial (degree + 1) → cusp.smooth,
      binaryCohomologicalDerivedOperator cusp degree binaryRotationDirection vector = cocycle binaryRotationDirection ∧
      binaryCohomologicalDerivedOperator cusp degree binarySplitDirection vector = cocycle binarySplitDirection ∧
      binaryCohomologicalDerivedOperator cusp degree binarySymmetricDirection vector = cocycle binarySymmetricDirection := by
  let T := binaryCohomologicalDerivedOperator cusp degree
  let D := binaryCohomologicalDifferenceOperator cusp degree
  let K := binaryRotationDirection
  let H := binarySplitDirection
  let B := binarySymmetricDirection
  have traceless := binary_rankOne_directions_traceless
  have kh : T K (cocycle H) - T H (cocycle K) = -(2 • cocycle B) := by
    have bracket : K * H - H * K = -(2 • B) := by
      simpa only [Ring.lie_def] using binaryRotation_split_bracket
    have equation := lie_identity K H traceless.1 traceless.2.1
    rw [bracket, map_neg, map_nsmul] at equation
    exact equation.symm
  have kb : T K (cocycle B) - T B (cocycle K) = 2 • cocycle H := by
    have bracket : K * B - B * K = 2 • H := by
      simpa only [Ring.lie_def] using binaryRotation_symmetric_bracket
    have equation := lie_identity K B traceless.1 traceless.2.2
    rw [bracket, map_nsmul] at equation
    exact equation.symm
  have hb : T H (cocycle B) - T B (cocycle H) = 2 • cocycle K := by
    have bracket : H * B - B * H = 2 • K := by
      simpa only [Ring.lie_def] using binarySplit_symmetric_bracket
    have equation := lie_identity H B traceless.2.1 traceless.2.2
    rw [bracket, map_nsmul] at equation
    exact equation.symm
  have hk : T H (cocycle K) - T K (cocycle H) = 2 • cocycle B := by
    have reverse : T H (cocycle K) - T K (cocycle H) = -(T K (cocycle H) - T H (cocycle K)) := by abel
    rw [reverse, kh, neg_neg]
  have bk : T B (cocycle K) - T K (cocycle B) = -(2 • cocycle H) := by
    rw [← kb]
    abel
  have bh : T B (cocycle H) - T H (cocycle B) = -(2 • cocycle K) := by
    rw [← hb]
    abel
  have mixed_hk : T H * D K - D K * T H = 2 • D B := by
    rw [binaryCohomological_mixed_swap, binaryCohomological_mixed_rotation_split, neg_neg]
  have mixed_bk : T B * D K - D K * T B = -(2 • D H) := by
    rw [binaryCohomological_mixed_swap, binaryCohomological_mixed_rotation_symmetric]
  have mixed_bh : T B * D H - D H * T B = -(2 • D K) := by
    rw [binaryCohomological_mixed_swap, binaryCohomological_mixed_split_symmetric]
  let primitive := rankOneCocyclePrimitive (D H) (D B) (D K) (cocycle H) (cocycle B) (cocycle K)
  have rotation := rankOneCocyclePrimitive_rotation (T K) (T H) (T B) (D K) (D H) (D B)
    (cocycle K) (cocycle H) (cocycle B)
    (binaryCohomological_mixed_self cusp degree K)
    (binaryCohomological_mixed_rotation_split cusp degree)
    (binaryCohomological_mixed_rotation_symmetric cusp degree) kh kb
  have split := rankOneCocyclePrimitive_split (T K) (T H) (T B) (D K) (D H) (D B)
    (cocycle K) (cocycle H) (cocycle B) mixed_hk
    (binaryCohomological_mixed_self cusp degree H)
    (binaryCohomological_mixed_split_symmetric cusp degree) hk hb
  have symmetric := rankOneCocyclePrimitive_symmetric (T K) (T H) (T B) (D K) (D H) (D B)
    (cocycle K) (cocycle H) (cocycle B) mixed_bk mixed_bh
    (binaryCohomological_mixed_self cusp degree B) bk bh
  have difference : D H * T H + D B * T B - D K * T K =
      (scalar - ((degree : ℂ) + 1) * ((degree : ℂ) + 3)) • 1 :=
    binaryCohomological_difference_casimir_scalar cusp degree scalar casimir
  rw [difference, LinearMap.smul_apply, Module.End.one_apply] at rotation split symmetric
  refine ⟨(scalar - ((degree : ℂ) + 1) * ((degree : ℂ) + 3))⁻¹ • primitive, ?_, ?_, ?_⟩
  · change T K (_ • primitive) = cocycle K
    rw [map_smul, rotation, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr distinct), one_smul]
  · change T H (_ • primitive) = cocycle H
    rw [map_smul, split, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr distinct), one_smul]
  · change T B (_ • primitive) = cocycle B
    rw [map_smul, symmetric, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr distinct), one_smul]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
