module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.CohomologicalMixedOperators

@[expose] public section


open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem binaryCohomological_mixed_self (cusp : CuspidalRepresentation) (degree : ℕ)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryCohomologicalDerivedOperator cusp degree direction * binaryCohomologicalDifferenceOperator cusp degree direction -
      binaryCohomologicalDifferenceOperator cusp degree direction * binaryCohomologicalDerivedOperator cusp degree direction = 0 := by
  have coefficient : binaryCoefficientDerivedOperator degree direction * binaryCoefficientDerivedOperator degree direction -
      binaryCoefficientDerivedOperator degree direction * binaryCoefficientDerivedOperator degree direction =
      binaryCoefficientDerivedOperator degree (direction * direction - direction * direction) := by
    rw [sub_self, binaryCoefficientDerivedOperator_zero]
    exact sub_self (binaryCoefficientDerivedOperator degree direction * binaryCoefficientDerivedOperator degree direction)
  simpa only [sub_self, binaryCohomologicalDifferenceOperator_zero] using
    binaryCohomological_mixed_bracket cusp degree direction direction coefficient

theorem binaryCohomological_mixed_swap (cusp : CuspidalRepresentation) (degree : ℕ)
    (first second : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryCohomologicalDerivedOperator cusp degree first * binaryCohomologicalDifferenceOperator cusp degree second -
      binaryCohomologicalDifferenceOperator cusp degree second * binaryCohomologicalDerivedOperator cusp degree first =
      -(binaryCohomologicalDerivedOperator cusp degree second * binaryCohomologicalDifferenceOperator cusp degree first -
        binaryCohomologicalDifferenceOperator cusp degree first * binaryCohomologicalDerivedOperator cusp degree second) := by
  rw [binaryCohomologicalDerivedOperator_eq_sum, binaryCohomologicalDerivedOperator_eq_sum,
    binaryCohomologicalDifferenceOperator, binaryCohomologicalDifferenceOperator]
  simp only [sub_mul, mul_sub, add_mul, mul_add]
  rw [(binaryCuspTuple_coefficient_commute cusp degree (cuspDerivedAction cusp first)
      (binaryCoefficientDerivedOperator degree second)).eq,
    (binaryCuspTuple_coefficient_commute cusp degree (cuspDerivedAction cusp second)
      (binaryCoefficientDerivedOperator degree first)).eq]
  abel

theorem binaryCohomological_mixed_rotation_split (cusp : CuspidalRepresentation) (degree : ℕ) :
    binaryCohomologicalDerivedOperator cusp degree binaryRotationDirection *
        binaryCohomologicalDifferenceOperator cusp degree binarySplitDirection -
      binaryCohomologicalDifferenceOperator cusp degree binarySplitDirection *
        binaryCohomologicalDerivedOperator cusp degree binaryRotationDirection =
      -(2 • binaryCohomologicalDifferenceOperator cusp degree binarySymmetricDirection) := by
  have matrix : binaryRotationDirection * binarySplitDirection - binarySplitDirection * binaryRotationDirection =
      -(2 • binarySymmetricDirection) := by simpa only [Ring.lie_def] using binaryRotation_split_bracket
  have coefficient : binaryCoefficientDerivedOperator degree binaryRotationDirection * binaryCoefficientDerivedOperator degree binarySplitDirection -
      binaryCoefficientDerivedOperator degree binarySplitDirection * binaryCoefficientDerivedOperator degree binaryRotationDirection =
      binaryCoefficientDerivedOperator degree (binaryRotationDirection * binarySplitDirection - binarySplitDirection * binaryRotationDirection) := by
    rw [matrix, binaryCoefficientDerivedOperator_neg, binaryCoefficientDerivedOperator_nsmul,
      binaryCoefficientDerivedOperator_rotation, binaryCoefficientDerivedOperator_split, binaryCoefficientDerivedOperator_symmetric]
    exact binaryCoefficient_rotation_split_bracket degree
  simpa only [matrix, binaryCohomologicalDifferenceOperator_neg, binaryCohomologicalDifferenceOperator_nsmul] using
    binaryCohomological_mixed_bracket cusp degree binaryRotationDirection binarySplitDirection coefficient

theorem binaryCohomological_mixed_rotation_symmetric (cusp : CuspidalRepresentation) (degree : ℕ) :
    binaryCohomologicalDerivedOperator cusp degree binaryRotationDirection *
        binaryCohomologicalDifferenceOperator cusp degree binarySymmetricDirection -
      binaryCohomologicalDifferenceOperator cusp degree binarySymmetricDirection *
        binaryCohomologicalDerivedOperator cusp degree binaryRotationDirection =
      2 • binaryCohomologicalDifferenceOperator cusp degree binarySplitDirection := by
  have matrix : binaryRotationDirection * binarySymmetricDirection - binarySymmetricDirection * binaryRotationDirection =
      2 • binarySplitDirection := by simpa only [Ring.lie_def] using binaryRotation_symmetric_bracket
  have coefficient : binaryCoefficientDerivedOperator degree binaryRotationDirection * binaryCoefficientDerivedOperator degree binarySymmetricDirection -
      binaryCoefficientDerivedOperator degree binarySymmetricDirection * binaryCoefficientDerivedOperator degree binaryRotationDirection =
      binaryCoefficientDerivedOperator degree (binaryRotationDirection * binarySymmetricDirection - binarySymmetricDirection * binaryRotationDirection) := by
    rw [matrix, binaryCoefficientDerivedOperator_nsmul, binaryCoefficientDerivedOperator_rotation,
      binaryCoefficientDerivedOperator_split, binaryCoefficientDerivedOperator_symmetric]
    exact binaryCoefficient_rotation_symmetric_bracket degree
  simpa only [matrix, binaryCohomologicalDifferenceOperator_nsmul] using
    binaryCohomological_mixed_bracket cusp degree binaryRotationDirection binarySymmetricDirection coefficient

theorem binaryCohomological_mixed_split_symmetric (cusp : CuspidalRepresentation) (degree : ℕ) :
    binaryCohomologicalDerivedOperator cusp degree binarySplitDirection *
        binaryCohomologicalDifferenceOperator cusp degree binarySymmetricDirection -
      binaryCohomologicalDifferenceOperator cusp degree binarySymmetricDirection *
        binaryCohomologicalDerivedOperator cusp degree binarySplitDirection =
      2 • binaryCohomologicalDifferenceOperator cusp degree binaryRotationDirection := by
  have matrix : binarySplitDirection * binarySymmetricDirection - binarySymmetricDirection * binarySplitDirection =
      2 • binaryRotationDirection := by simpa only [Ring.lie_def] using binarySplit_symmetric_bracket
  have coefficient : binaryCoefficientDerivedOperator degree binarySplitDirection * binaryCoefficientDerivedOperator degree binarySymmetricDirection -
      binaryCoefficientDerivedOperator degree binarySymmetricDirection * binaryCoefficientDerivedOperator degree binarySplitDirection =
      binaryCoefficientDerivedOperator degree (binarySplitDirection * binarySymmetricDirection - binarySymmetricDirection * binarySplitDirection) := by
    rw [matrix, binaryCoefficientDerivedOperator_nsmul, binaryCoefficientDerivedOperator_rotation,
      binaryCoefficientDerivedOperator_split, binaryCoefficientDerivedOperator_symmetric]
    exact binaryCoefficient_split_symmetric_bracket degree
  simpa only [matrix, binaryCohomologicalDifferenceOperator_nsmul] using
    binaryCohomological_mixed_bracket cusp degree binarySplitDirection binarySymmetricDirection coefficient

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
