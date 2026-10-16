module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.RankOneCocyclePrimitive

@[expose] public section


open GeneralEisenstein Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def binaryCohomologicalDifferenceOperator (cusp : CuspidalRepresentation) (degree : ℕ)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    Module.End ℂ (BinaryDegreeMonomial (degree + 1) → cusp.smooth) :=
  binaryCuspTupleOperator cusp degree (cuspDerivedAction cusp direction) -
    binaryCuspCoefficientHom cusp degree (binaryCoefficientDerivedOperator degree direction)

theorem binaryCoefficientDerivedOperator_zero (degree : ℕ) :
    binaryCoefficientDerivedOperator degree 0 = 0 := by
  simp [binaryCoefficientDerivedOperator]
  exact @neg_zero (Module.End ℂ (Binary.HomogeneousPoly (degree + 1))) inferInstance

theorem binaryCoefficientDerivedOperator_add (degree : ℕ)
    (first second : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryCoefficientDerivedOperator degree (first + second) =
      binaryCoefficientDerivedOperator degree first + binaryCoefficientDerivedOperator degree second := by
  simp only [binaryCoefficientDerivedOperator, Matrix.add_apply, Complex.ofReal_add, add_smul,
    Finset.sum_add_distrib]
  abel

theorem binaryCoefficientDerivedOperator_neg (degree : ℕ)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryCoefficientDerivedOperator degree (-direction) = -binaryCoefficientDerivedOperator degree direction := by
  apply (eq_neg_iff_add_eq_zero (a := binaryCoefficientDerivedOperator degree (-direction))
    (b := binaryCoefficientDerivedOperator degree direction)).mpr
  rw [← binaryCoefficientDerivedOperator_add, neg_add_cancel, binaryCoefficientDerivedOperator_zero]

theorem binaryCoefficientDerivedOperator_nsmul (degree : ℕ)
    (count : ℕ) (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryCoefficientDerivedOperator degree (count • direction) = count • binaryCoefficientDerivedOperator degree direction := by
  induction count with
  | zero => simp [binaryCoefficientDerivedOperator_zero]
  | succ count induction_hypothesis =>
    rw [succ_nsmul, binaryCoefficientDerivedOperator_add, induction_hypothesis, succ_nsmul]

theorem binaryCohomological_mixed_bracket (cusp : CuspidalRepresentation) (degree : ℕ)
    (first second : Matrix (Fin 2) (Fin 2) ℝ)
    (coefficient_bracket : binaryCoefficientDerivedOperator degree first * binaryCoefficientDerivedOperator degree second -
      binaryCoefficientDerivedOperator degree second * binaryCoefficientDerivedOperator degree first =
      binaryCoefficientDerivedOperator degree (first * second - second * first)) :
    binaryCohomologicalDerivedOperator cusp degree first * binaryCohomologicalDifferenceOperator cusp degree second -
      binaryCohomologicalDifferenceOperator cusp degree second * binaryCohomologicalDerivedOperator cusp degree first =
      binaryCohomologicalDifferenceOperator cusp degree (first * second - second * first) := by
  have cusp_bracket : cuspDerivedAction cusp first * cuspDerivedAction cusp second -
      cuspDerivedAction cusp second * cuspDerivedAction cusp first =
      cuspDerivedAction cusp (first * second - second * first) := by
    let _ : LieRing (Matrix (Fin 2) (Fin 2) ℝ) := LieRing.ofAssociativeRing
    let _ : LieRing (Module.End ℂ cusp.smooth) := LieRing.ofAssociativeRing
    simpa only [Ring.lie_def] using ((cuspDerivedAction cusp).map_lie first second).symm
  let A := binaryCuspTupleOperator cusp degree
  let B := binaryCuspCoefficientHom cusp degree
  rw [binaryCohomologicalDerivedOperator_eq_sum, binaryCohomologicalDifferenceOperator,
    binaryCohomologicalDifferenceOperator]
  change (A (cuspDerivedAction cusp first) + B (binaryCoefficientDerivedOperator degree first)) *
      (A (cuspDerivedAction cusp second) - B (binaryCoefficientDerivedOperator degree second)) -
      (A (cuspDerivedAction cusp second) - B (binaryCoefficientDerivedOperator degree second)) *
        (A (cuspDerivedAction cusp first) + B (binaryCoefficientDerivedOperator degree first)) = _
  calc
    _ = A (cuspDerivedAction cusp first * cuspDerivedAction cusp second -
          cuspDerivedAction cusp second * cuspDerivedAction cusp first) -
        B (binaryCoefficientDerivedOperator degree first * binaryCoefficientDerivedOperator degree second -
          binaryCoefficientDerivedOperator degree second * binaryCoefficientDerivedOperator degree first) := by
      rw [map_sub B, map_mul B, map_mul B]
      simp only [map_sub, map_mul, add_mul, mul_add, sub_mul, mul_sub]
      rw [(binaryCuspTuple_coefficient_commute cusp degree (cuspDerivedAction cusp first)
        (binaryCoefficientDerivedOperator degree second)).eq,
        (binaryCuspTuple_coefficient_commute cusp degree (cuspDerivedAction cusp second)
        (binaryCoefficientDerivedOperator degree first)).eq]
      dsimp only [A, B]
      abel
    _ = _ := by rw [cusp_bracket, coefficient_bracket]

theorem binaryCohomologicalDifferenceOperator_zero (cusp : CuspidalRepresentation) (degree : ℕ) :
    binaryCohomologicalDifferenceOperator cusp degree 0 = 0 := by
  simp [binaryCohomologicalDifferenceOperator, binaryCoefficientDerivedOperator_zero]

theorem binaryCohomologicalDifferenceOperator_neg (cusp : CuspidalRepresentation) (degree : ℕ)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryCohomologicalDifferenceOperator cusp degree (-direction) =
      -binaryCohomologicalDifferenceOperator cusp degree direction := by
  simp only [binaryCohomologicalDifferenceOperator, binaryCoefficientDerivedOperator_neg]
  rw [map_neg (cuspDerivedAction cusp), map_neg (binaryCuspTupleOperator cusp degree),
    map_neg (binaryCuspCoefficientHom cusp degree)]
  abel

theorem binaryCohomologicalDifferenceOperator_nsmul (cusp : CuspidalRepresentation) (degree : ℕ)
    (count : ℕ) (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryCohomologicalDifferenceOperator cusp degree (count • direction) =
      count • binaryCohomologicalDifferenceOperator cusp degree direction := by
  simp only [binaryCohomologicalDifferenceOperator, map_nsmul, binaryCoefficientDerivedOperator_nsmul,
    nsmul_sub]

theorem binaryCohomologicalDifference_times_derived (cusp : CuspidalRepresentation) (degree : ℕ)
    (direction : Matrix (Fin 2) (Fin 2) ℝ) :
    binaryCohomologicalDifferenceOperator cusp degree direction * binaryCohomologicalDerivedOperator cusp degree direction =
      binaryCuspTupleOperator cusp degree (cuspDerivedAction cusp direction * cuspDerivedAction cusp direction) -
      binaryCuspCoefficientHom cusp degree
        (binaryCoefficientDerivedOperator degree direction * binaryCoefficientDerivedOperator degree direction) := by
  rw [binaryCohomologicalDifferenceOperator, binaryCohomologicalDerivedOperator_eq_sum]
  simp only [map_mul, sub_mul, mul_add]
  rw [(binaryCuspTuple_coefficient_commute cusp degree (cuspDerivedAction cusp direction)
    (binaryCoefficientDerivedOperator degree direction)).eq]
  abel

theorem binaryCohomological_difference_casimir (cusp : CuspidalRepresentation) (degree : ℕ) :
    binaryCohomologicalDifferenceOperator cusp degree binarySplitDirection *
        binaryCohomologicalDerivedOperator cusp degree binarySplitDirection +
      binaryCohomologicalDifferenceOperator cusp degree binarySymmetricDirection *
        binaryCohomologicalDerivedOperator cusp degree binarySymmetricDirection -
      binaryCohomologicalDifferenceOperator cusp degree binaryRotationDirection *
        binaryCohomologicalDerivedOperator cusp degree binaryRotationDirection =
      binaryCuspTupleOperator cusp degree (cuspCasimirOperator cusp) -
        (((degree : ℂ) + 1) * ((degree : ℂ) + 3)) • 1 := by
  rw [binaryCohomologicalDifference_times_derived, binaryCohomologicalDifference_times_derived,
    binaryCohomologicalDifference_times_derived]
  have coefficient := congrArg (binaryCuspCoefficientHom cusp degree) (binaryCoefficientDerivedOperator_casimir degree)
  rw [map_sub (binaryCuspCoefficientHom cusp degree), map_add] at coefficient
  simp only [map_smul, map_one] at coefficient
  rw [cuspCasimirOperator, map_sub, map_add, ← coefficient]
  unfold cuspSplitOperator cuspSymmetricOperator cuspRotationOperator
  abel

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
