module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Integral.UpperShears

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

def integerBinaryQuarterTurn : GeneralLinearGroup (Fin 2) ℤ :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by decide, by decide⟩

theorem integerBinaryQuarterTurn_line_height_sq (matrix : RealGL3) :
    realPlaneHeight (integralRealGroup (lineLevi 1 integerBinaryQuarterTurn) * matrix) ^ 2 =
      matrix.val 1 0 ^ 2 + matrix.val 1 1 ^ 2 + matrix.val 1 2 ^ 2 := by
  rw [realPlaneHeight_sq]
  simp [integralRealGroup, lineLevi_val, integerBinaryQuarterTurn, Matrix.mul_apply,
    Fin.sum_univ_three]

theorem integerBinaryQuarterTurn_plane_projected (matrix : RealGL3) :
    realProjectedRowSq (integralRealGroup (planeLevi integerBinaryQuarterTurn 1) * matrix) =
      matrix.val 0 0 ^ 2 + matrix.val 0 1 ^ 2 := by
  simp [realProjectedRowSq, integralRealGroup, planeLevi, planeBlock, integerBinaryQuarterTurn,
    Matrix.mul_apply, Fin.sum_univ_three]

def realTriangularReduced (matrix : RealGL3) : Prop :=
  InPlaneParabolic matrix ∧ matrix.val 1 0 = 0 ∧
    0 < matrix.val 1 1 ∧ 0 < matrix.val 2 2 ∧
    |matrix.val 0 1| ≤ matrix.val 1 1 / 2 ∧
    |matrix.val 0 2| ≤ matrix.val 2 2 / 2 ∧
    |matrix.val 1 2| ≤ matrix.val 2 2 / 2 ∧
    3 * matrix.val 1 1 ^ 2 ≤ 4 * matrix.val 0 0 ^ 2 ∧
    3 * matrix.val 2 2 ^ 2 ≤ 4 * matrix.val 1 1 ^ 2

theorem real_triangular_diagonal_bounds (matrix : RealGL3)
    (parabolic : InPlaneParabolic matrix) (triangular : matrix.val 1 0 = 0)
    (horizontal : |matrix.val 0 1| ≤ matrix.val 1 1 / 2)
    (vertical : |matrix.val 1 2| ≤ matrix.val 2 2 / 2)
    (first_minimal : ∀ integral : IntegralGL3,
      realPlaneHeight matrix ≤ realPlaneHeight (integralRealGroup integral * matrix))
    (second_minimal : ∀ binary : GeneralLinearGroup (Fin 2) ℤ,
      realProjectedRowSq matrix ≤ realProjectedRowSq (integralRealGroup (planeLevi binary 1) * matrix)) :
    3 * matrix.val 1 1 ^ 2 ≤ 4 * matrix.val 0 0 ^ 2 ∧
      3 * matrix.val 2 2 ^ 2 ≤ 4 * matrix.val 1 1 ^ 2 := by
  have second := second_minimal integerBinaryQuarterTurn
  rw [integerBinaryQuarterTurn_plane_projected, realProjectedRowSq, triangular] at second
  have first := pow_le_pow_left₀ (realPlaneHeight_pos matrix).le
    (first_minimal (lineLevi 1 integerBinaryQuarterTurn)) 2
  rw [integerBinaryQuarterTurn_line_height_sq, realPlaneHeight_sq, parabolic.1, parabolic.2, triangular] at first
  have horizontal_sq := pow_le_pow_left₀ (abs_nonneg (matrix.val 0 1)) horizontal 2
  have vertical_sq := pow_le_pow_left₀ (abs_nonneg (matrix.val 1 2)) vertical 2
  constructor
  · nlinarith [sq_abs (matrix.val 0 1)]
  · nlinarith [sq_abs (matrix.val 1 2)]

theorem real_triangular_minima_size_reduction (matrix : RealGL3)
    (parabolic : InPlaneParabolic matrix) (triangular : matrix.val 1 0 = 0)
    (second_positive : 0 < matrix.val 1 1) (last_positive : 0 < matrix.val 2 2)
    (first_minimal : ∀ integral : IntegralGL3,
      realPlaneHeight matrix ≤ realPlaneHeight (integralRealGroup integral * matrix))
    (second_minimal : ∀ binary : GeneralLinearGroup (Fin 2) ℤ,
      realProjectedRowSq matrix ≤ realProjectedRowSq (integralRealGroup (planeLevi binary 1) * matrix)) :
    ∃ integral : IntegralGL3, realTriangularReduced (integralRealGroup integral * matrix) := by
  obtain ⟨horizontal, horizontal_bound⟩ := real_integer_shear_bound (matrix.val 0 1) (matrix.val 1 1) second_positive
  obtain ⟨secondVertical, second_bound⟩ := real_integer_shear_bound (matrix.val 1 2) (matrix.val 2 2) last_positive
  obtain ⟨firstVertical, first_bound⟩ := real_integer_shear_bound
    (matrix.val 0 2 + horizontal * matrix.val 1 2) (matrix.val 2 2) last_positive
  let integral := integralUpperShear horizontal firstVertical secondVertical
  let reduced := integralRealGroup integral * matrix
  have formula := integralUpperShear_triangular_val matrix parabolic triangular horizontal firstVertical secondVertical
  change reduced.val = _ at formula
  have reduced_parabolic : InPlaneParabolic reduced := by constructor <;> simp [formula]
  have reduced_triangular : reduced.val 1 0 = 0 := by simp [formula]
  have reduced_second_positive : 0 < reduced.val 1 1 := by simpa [formula] using second_positive
  have reduced_last_positive : 0 < reduced.val 2 2 := by simpa [formula] using last_positive
  have reduced_horizontal : |reduced.val 0 1| ≤ reduced.val 1 1 / 2 := by simpa [formula] using horizontal_bound
  have reduced_vertical : |reduced.val 1 2| ≤ reduced.val 2 2 / 2 := by simpa [formula] using second_bound
  have reduced_first_minimal : ∀ other : IntegralGL3,
      realPlaneHeight reduced ≤ realPlaneHeight (integralRealGroup other * reduced) := by
    intro other
    change realPlaneHeight (integralRealGroup (integralUpperShear horizontal firstVertical secondVertical) * matrix) ≤ _
    rw [realPlaneHeight_integralUpperShear]
    simpa only [map_mul, mul_assoc] using first_minimal (other * integral)
  have reduced_second_minimal : ∀ binary : GeneralLinearGroup (Fin 2) ℤ,
      realProjectedRowSq reduced ≤ realProjectedRowSq (integralRealGroup (planeLevi binary 1) * reduced) := by
    intro binary
    change realProjectedRowSq (integralRealGroup (integralUpperShear horizontal firstVertical secondVertical) * matrix) ≤ _
    rw [realProjectedRowSq_integralUpperShear matrix parabolic]
    change realProjectedRowSq matrix ≤ realProjectedRowSq (integralRealGroup (planeLevi binary 1) *
      (integralRealGroup (integralUpperShear horizontal firstVertical secondVertical) * matrix))
    rw [integralUpperShear_binary_projected matrix parabolic]
    exact second_minimal (binary * binaryUnipotent horizontal)
  refine ⟨integral, reduced_parabolic, reduced_triangular, reduced_second_positive, reduced_last_positive,
    reduced_horizontal, ?_, reduced_vertical, ?_⟩
  · change |reduced.val 0 2| ≤ reduced.val 2 2 / 2
    simpa [formula] using first_bound
  · exact real_triangular_diagonal_bounds reduced reduced_parabolic reduced_triangular
      reduced_horizontal reduced_vertical
      reduced_first_minimal reduced_second_minimal

theorem integral_real_reduced_triangular_decomposition (matrix : RealGL3) :
    ∃ integral : IntegralGL3, ∃ rotation : RealGL3,
      rotation.val.transpose * rotation.val = 1 ∧
      realTriangularReduced (integralRealGroup integral * matrix * rotation) := by
  obtain ⟨first, rotation, orthogonal, parabolic, triangular, second_positive, last_positive,
    first_minimal, second_minimal⟩ := integral_real_triangular_two_minima matrix
  obtain ⟨correction, reduced⟩ := real_triangular_minima_size_reduction
    (integralRealGroup first * matrix * rotation) parabolic triangular second_positive last_positive
    first_minimal second_minimal
  refine ⟨correction * first, rotation, orthogonal, ?_⟩
  simpa only [map_mul, mul_assoc] using reduced

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
