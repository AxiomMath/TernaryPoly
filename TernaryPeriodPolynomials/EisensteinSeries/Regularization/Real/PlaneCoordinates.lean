module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.GroupAverages

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

noncomputable def realPlaneRowSquare (matrix : RealSL3) : ℝ :=
  ∑ column : Fin 3, matrix.val 2 column ^ 2

theorem realPlaneRowSquare_positive (matrix : RealSL3) : 0 < realPlaneRowSquare matrix := by
  have positive := Real.sqrt_pos.mp (realPlaneHeight_pos (SpecialLinearGroup.toGL matrix))
  change 0 < matrix.val 2 0 ^ 2 + matrix.val 2 1 ^ 2 + matrix.val 2 2 ^ 2 at positive
  simpa only [realPlaneRowSquare, Fin.sum_univ_three] using positive

theorem realPlaneRowSquare_continuous : Continuous realPlaneRowSquare := by
  unfold realPlaneRowSquare
  apply continuous_finsetSum
  intro column _
  exact ((continuous_apply column).comp ((continuous_apply 2).comp
    (show Continuous (fun matrix : RealSL3 => matrix.val) from continuous_subtype_val))).pow 2

noncomputable def realPlaneCoordinate (matrix : RealSL3) (row : Fin 2) : ℝ :=
  (∑ column : Fin 3, matrix.val row.castSucc column * matrix.val 2 column) / realPlaneRowSquare matrix

theorem realPlaneCoordinate_continuous (row : Fin 2) : Continuous (fun matrix => realPlaneCoordinate matrix row) := by
  unfold realPlaneCoordinate
  apply Continuous.div _ realPlaneRowSquare_continuous (fun matrix => ne_of_gt (realPlaneRowSquare_positive matrix))
  apply continuous_finsetSum
  intro column _
  exact (((continuous_apply column).comp ((continuous_apply row.castSucc).comp
    (show Continuous (fun matrix : RealSL3 => matrix.val) from continuous_subtype_val)))).mul
    ((continuous_apply column).comp ((continuous_apply 2).comp
      (show Continuous (fun matrix : RealSL3 => matrix.val) from continuous_subtype_val)))

theorem realSpecialPlane_mul_last_row (first second : ℝ) (matrix : RealSL3) (column : Fin 3) :
    (realSpecialPlane first second * matrix).val 2 column = matrix.val 2 column := by
  simp [realSpecialPlane, realSpecialUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem realSpecialPlane_mul_first_rows (coordinates : Fin 2 → ℝ) (matrix : RealSL3) (row : Fin 2) (column : Fin 3) :
    (realSpecialPlane (coordinates 0) (coordinates 1) * matrix).val row.castSucc column =
      matrix.val row.castSucc column + coordinates row * matrix.val 2 column := by
  fin_cases row <;>
    simp [realSpecialPlane, realSpecialUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

theorem realPlaneRowSquare_plane_mul (first second : ℝ) (matrix : RealSL3) :
    realPlaneRowSquare (realSpecialPlane first second * matrix) = realPlaneRowSquare matrix := by
  unfold realPlaneRowSquare
  simp only [realSpecialPlane_mul_last_row]

theorem realPlaneCoordinate_plane_mul (coordinates : Fin 2 → ℝ) (matrix : RealSL3) (row : Fin 2) :
    realPlaneCoordinate (realSpecialPlane (coordinates 0) (coordinates 1) * matrix) row =
      coordinates row + realPlaneCoordinate matrix row := by
  unfold realPlaneCoordinate
  rw [realPlaneRowSquare_plane_mul]
  simp only [realSpecialPlane_mul_first_rows, realSpecialPlane_mul_last_row, add_mul, mul_assoc,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  have squares : (∑ column : Fin 3, matrix.val 2 column * matrix.val 2 column) = realPlaneRowSquare matrix := by
    simp only [realPlaneRowSquare, pow_two]
  rw [squares, add_div, mul_div_cancel_right₀ _ (ne_of_gt (realPlaneRowSquare_positive matrix)), add_comm]

theorem realSpecialPlane_add (first second first' second' : ℝ) :
    realSpecialPlane first second * realSpecialPlane first' second' = realSpecialPlane (first + first') (second + second') := by
  unfold realSpecialPlane
  rw [realSpecialUnipotent_mul]
  simp only [add_zero, zero_mul]

theorem realSpecialPlane_zero : realSpecialPlane 0 0 = 1 := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [realSpecialPlane, realSpecialUnipotent]

noncomputable def realPlaneBase (matrix : RealSL3) : RealSL3 :=
  realSpecialPlane (-realPlaneCoordinate matrix 0) (-realPlaneCoordinate matrix 1) * matrix

theorem realPlaneBase_continuous : Continuous realPlaneBase :=
  (realSpecialPlane_continuous.comp
    ((realPlaneCoordinate_continuous 0).neg.prodMk (realPlaneCoordinate_continuous 1).neg)).mul continuous_id

theorem realPlaneCoordinate_base (matrix : RealSL3) (row : Fin 2) : realPlaneCoordinate (realPlaneBase matrix) row = 0 := by
  have identity := realPlaneCoordinate_plane_mul (fun row => -realPlaneCoordinate matrix row) matrix row
  simpa only [realPlaneBase, neg_add_cancel] using identity

theorem realPlaneBase_factorization (matrix : RealSL3) :
    realSpecialPlane (realPlaneCoordinate matrix 0) (realPlaneCoordinate matrix 1) * realPlaneBase matrix = matrix := by
  rw [realPlaneBase, ← mul_assoc, realSpecialPlane_add, add_neg_cancel, add_neg_cancel, realSpecialPlane_zero, one_mul]

theorem realPlaneBase_plane_mul (coordinates : Fin 2 → ℝ) (matrix : RealSL3) :
    realPlaneBase (realSpecialPlane (coordinates 0) (coordinates 1) * matrix) = realPlaneBase matrix := by
  simp only [realPlaneBase, realPlaneCoordinate_plane_mul, ← mul_assoc, realSpecialPlane_add]
  congr 2 <;> ring

theorem realPlaneCoordinate_plane_mul_zero (first second : ℝ) (matrix : RealSL3) :
    realPlaneCoordinate (realSpecialPlane first second * matrix) 0 = first + realPlaneCoordinate matrix 0 :=
  realPlaneCoordinate_plane_mul ![first, second] matrix 0

theorem realPlaneCoordinate_plane_mul_one (first second : ℝ) (matrix : RealSL3) :
    realPlaneCoordinate (realSpecialPlane first second * matrix) 1 = second + realPlaneCoordinate matrix 1 :=
  realPlaneCoordinate_plane_mul ![first, second] matrix 1

theorem realPlaneBase_pair_plane_mul (first second : ℝ) (matrix : RealSL3) :
    realPlaneBase (realSpecialPlane first second * matrix) = realPlaneBase matrix :=
  realPlaneBase_plane_mul ![first, second] matrix

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
