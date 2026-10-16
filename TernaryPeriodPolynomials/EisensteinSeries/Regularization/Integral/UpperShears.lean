module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.TriangularMinima
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Binary.Periodicity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

noncomputable def integralUpperShear (horizontal firstVertical secondVertical : ℤ) : IntegralGL3 :=
  planeUnipotent firstVertical secondVertical * planeLevi (binaryUnipotent horizontal) 1

theorem integralUpperShear_val (horizontal firstVertical secondVertical : ℤ) :
    (integralUpperShear horizontal firstVertical secondVertical).val =
      !![1, horizontal, firstVertical; 0, 1, secondVertical; 0, 0, 1] := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [integralUpperShear, planeUnipotent, planeLevi, planeBlock, binaryUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem integralUpperShear_real_val (horizontal firstVertical secondVertical : ℤ) :
    (integralRealGroup (integralUpperShear horizontal firstVertical secondVertical)).val =
      !![1, (horizontal : ℝ), (firstVertical : ℝ); 0, 1, (secondVertical : ℝ); 0, 0, 1] := by
  change (integralUpperShear horizontal firstVertical secondVertical).val.map (Int.castRingHom ℝ) = _
  rw [integralUpperShear_val]
  ext row column
  fin_cases row <;> fin_cases column <;> simp

theorem integralUpperShear_last_row (matrix : RealGL3) (horizontal firstVertical secondVertical : ℤ) :
    (integralRealGroup (integralUpperShear horizontal firstVertical secondVertical) * matrix).val 2 = matrix.val 2 := by
  change ((integralRealGroup (integralUpperShear horizontal firstVertical secondVertical)).val * matrix.val) 2 = _
  rw [integralUpperShear_real_val]
  ext column
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem realPlaneHeight_integralUpperShear (matrix : RealGL3) (horizontal firstVertical secondVertical : ℤ) :
    realPlaneHeight (integralRealGroup (integralUpperShear horizontal firstVertical secondVertical) * matrix) =
      realPlaneHeight matrix := by
  change realRowHeight ((integralRealGroup (integralUpperShear horizontal firstVertical secondVertical) * matrix).val 2) = _
  rw [integralUpperShear_last_row, realRowHeight_last]

theorem integralUpperShear_triangular_val (matrix : RealGL3) (parabolic : InPlaneParabolic matrix)
    (triangular : matrix.val 1 0 = 0) (horizontal firstVertical secondVertical : ℤ) :
    (integralRealGroup (integralUpperShear horizontal firstVertical secondVertical) * matrix).val =
      !![matrix.val 0 0, matrix.val 0 1 + horizontal * matrix.val 1 1,
          matrix.val 0 2 + horizontal * matrix.val 1 2 + firstVertical * matrix.val 2 2;
        0, matrix.val 1 1, matrix.val 1 2 + secondVertical * matrix.val 2 2;
        0, 0, matrix.val 2 2] := by
  change (integralRealGroup (integralUpperShear horizontal firstVertical secondVertical)).val * matrix.val = _
  rw [integralUpperShear_real_val]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, parabolic.1, parabolic.2, triangular]

theorem integralUpperShear_binary_projected (matrix : RealGL3) (parabolic : InPlaneParabolic matrix)
    (binary : GeneralLinearGroup (Fin 2) ℤ) (horizontal firstVertical secondVertical : ℤ) :
    realProjectedRowSq (integralRealGroup (planeLevi binary 1) *
      (integralRealGroup (integralUpperShear horizontal firstVertical secondVertical) * matrix)) =
    realProjectedRowSq (integralRealGroup (planeLevi (binary * binaryUnipotent horizontal) 1) * matrix) := by
  rw [planeLevi_binary_mul, map_mul, mul_assoc]
  simp [realProjectedRowSq, integralUpperShear, integralRealGroup, planeUnipotent,
    planeLevi, planeBlock, binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_three, parabolic.1, parabolic.2]

theorem realProjectedRowSq_integralUpperShear (matrix : RealGL3) (parabolic : InPlaneParabolic matrix)
    (horizontal firstVertical secondVertical : ℤ) :
    realProjectedRowSq (integralRealGroup (integralUpperShear horizontal firstVertical secondVertical) * matrix) =
      realProjectedRowSq matrix := by
  simp [realProjectedRowSq, integralUpperShear, integralRealGroup, planeUnipotent,
    planeLevi, planeBlock, binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_three, parabolic.1, parabolic.2]

theorem real_integer_shear_bound (value scale : ℝ) (positive : 0 < scale) :
    ∃ shift : ℤ, |value + shift * scale| ≤ scale / 2 := by
  refine ⟨-round (value / scale), ?_⟩
  have identity : value + (-round (value / scale) : ℤ) * scale =
      (value / scale - (round (value / scale) : ℝ)) * scale := by
    push_cast
    field_simp
    ring
  rw [identity, abs_mul, abs_of_pos positive]
  exact (mul_le_mul_of_nonneg_right (abs_sub_round (value / scale)) positive.le).trans_eq (by ring)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
