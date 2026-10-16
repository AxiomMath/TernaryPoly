module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ReflectionModes

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryGenerators

def lowerUnipotent (parameter : ℝ) : BinaryRealGL :=
  ⟨!![1, 0; parameter, 1], !![1, 0; -parameter, 1], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def determinantDiagonal (scalar : ℝˣ) : BinaryRealGL :=
  ⟨!![1, 0; 0, scalar.val], !![1, 0; 0, scalar⁻¹.val], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def balancedDiagonal (scalar : ℝˣ) : BinaryRealGL :=
  ⟨!![scalar.val, 0; 0, scalar⁻¹.val], !![scalar⁻¹.val, 0; 0, scalar.val], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem upper_det (parameter : ℝ) : Matrix.GeneralLinearGroup.det (binaryUnipotent parameter) = 1 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, binaryUnipotent, Matrix.det_fin_two]

theorem upper_zero : binaryUnipotent (0 : ℝ) = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [binaryUnipotent]

theorem lower_zero : lowerUnipotent 0 = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [lowerUnipotent]

theorem determinantDiagonal_one : determinantDiagonal 1 = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [determinantDiagonal]

theorem determinantDiagonal_mul (first second : ℝˣ) :
    determinantDiagonal (first * second) = determinantDiagonal first * determinantDiagonal second := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> simp [determinantDiagonal, Matrix.mul_apply, Fin.sum_univ_two]

theorem balancedDiagonal_decomposition (scalar : ℝˣ) :
    balancedDiagonal scalar = binaryUnipotent scalar.val * lowerUnipotent (-scalar⁻¹.val) *
      binaryUnipotent scalar.val * binaryUnipotent (-1 : ℝ) * lowerUnipotent 1 * binaryUnipotent (-1 : ℝ) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [balancedDiagonal, binaryUnipotent, lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem gauss_decomposition (matrix : BinaryRealGL) (pivot : matrix.val 0 0 ≠ 0) :
    matrix = lowerUnipotent (matrix.val 1 0 / matrix.val 0 0) *
      balancedDiagonal (Units.mk0 (matrix.val 0 0) pivot) *
      determinantDiagonal (Matrix.GeneralLinearGroup.det matrix) *
      binaryUnipotent (matrix.val 0 1 / matrix.val 0 0) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [lowerUnipotent, balancedDiagonal, determinantDiagonal, binaryUnipotent,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    <;> field_simp
  all_goals ring

theorem balancedDiagonal_mem (group : Subgroup BinaryRealGL)
    (upper : ∀ parameter : ℝ, binaryUnipotent parameter ∈ group)
    (lower : ∀ parameter : ℝ, lowerUnipotent parameter ∈ group) (scalar : ℝˣ) :
    balancedDiagonal scalar ∈ group := by
  rw [balancedDiagonal_decomposition]
  exact group.mul_mem (group.mul_mem (group.mul_mem (group.mul_mem (group.mul_mem
    (upper _) (lower _)) (upper _)) (upper _)) (lower _)) (upper _)

theorem mem_of_pivot (group : Subgroup BinaryRealGL)
    (upper : ∀ parameter : ℝ, binaryUnipotent parameter ∈ group)
    (lower : ∀ parameter : ℝ, lowerUnipotent parameter ∈ group)
    (matrix : BinaryRealGL) (pivot : matrix.val 0 0 ≠ 0)
    (diagonal : determinantDiagonal (Matrix.GeneralLinearGroup.det matrix) ∈ group) : matrix ∈ group := by
  rw [gauss_decomposition matrix pivot]
  exact group.mul_mem (group.mul_mem (group.mul_mem (lower _)
    (balancedDiagonal_mem group upper lower _)) diagonal) (upper _)

theorem mem_of_determinantDiagonal (group : Subgroup BinaryRealGL)
    (upper : ∀ parameter : ℝ, binaryUnipotent parameter ∈ group)
    (lower : ∀ parameter : ℝ, lowerUnipotent parameter ∈ group)
    (matrix : BinaryRealGL)
    (diagonal : determinantDiagonal (Matrix.GeneralLinearGroup.det matrix) ∈ group) : matrix ∈ group := by
  by_cases pivot : matrix.val 0 0 ≠ 0
  · exact mem_of_pivot group upper lower matrix pivot diagonal
  · have firstEntry : matrix.val 0 0 = 0 := not_ne_iff.mp pivot
    have secondEntry : matrix.val 1 0 ≠ 0 := by
      intro vanishing
      have determinantNonzero := Matrix.GeneralLinearGroup.det_ne_zero matrix
      apply determinantNonzero
      simp [Matrix.det_fin_two, firstEntry, vanishing]
    have shiftedPivot : (binaryUnipotent (1 : ℝ) * matrix).val 0 0 ≠ 0 := by
      simpa [binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two, firstEntry] using secondEntry
    have shiftedDiagonal : determinantDiagonal (Matrix.GeneralLinearGroup.det (binaryUnipotent (1 : ℝ) * matrix)) ∈ group := by
      simpa only [map_mul, upper_det, one_mul] using diagonal
    have shiftedMember := mem_of_pivot group upper lower _ shiftedPivot shiftedDiagonal
    have cancellation : (binaryUnipotent (1 : ℝ))⁻¹ * (binaryUnipotent (1 : ℝ) * matrix) = matrix := inv_mul_cancel_left _ _
    rw [← cancellation]
    exact group.mul_mem (group.inv_mem (upper 1)) shiftedMember

theorem positive_det_mem (group : Subgroup BinaryRealGL)
    (upper : ∀ parameter : ℝ, binaryUnipotent parameter ∈ group)
    (lower : ∀ parameter : ℝ, lowerUnipotent parameter ∈ group)
    (diagonal : ∀ scalar : ℝˣ, 0 < scalar.val → determinantDiagonal scalar ∈ group)
    (matrix : BinaryRealGL) (positive : 0 < matrix.val.det) : matrix ∈ group :=
  mem_of_determinantDiagonal group upper lower matrix (diagonal _ positive)

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryGenerators
