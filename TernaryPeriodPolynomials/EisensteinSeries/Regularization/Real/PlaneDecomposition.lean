module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ParabolicFactorization
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.Valuation.IsTrivialOn

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def firstRealRotation (cosine sine : ℝ) (unit : cosine ^ 2 + sine ^ 2 = 1) : RealGL3 :=
  ⟨!![cosine, sine, 0; -sine, cosine, 0; 0, 0, 1],
    !![cosine, -sine, 0; sine, cosine, 0; 0, 0, 1], by
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith,
    by
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith⟩

def lastRealRotation (cosine sine : ℝ) (unit : cosine ^ 2 + sine ^ 2 = 1) : RealGL3 :=
  ⟨!![1, 0, 0; 0, cosine, sine; 0, -sine, cosine],
    !![1, 0, 0; 0, cosine, -sine; 0, sine, cosine], by
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith,
    by
      ext row column
      fin_cases row <;> fin_cases column <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith⟩

theorem firstRealRotation_orthogonal (cosine sine : ℝ) (unit : cosine ^ 2 + sine ^ 2 = 1) :
    (firstRealRotation cosine sine unit).val.transpose *
      (firstRealRotation cosine sine unit).val = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [firstRealRotation, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith

theorem lastRealRotation_orthogonal (cosine sine : ℝ) (unit : cosine ^ 2 + sine ^ 2 = 1) :
    (lastRealRotation cosine sine unit).val.transpose *
      (lastRealRotation cosine sine unit).val = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [lastRealRotation, Matrix.mul_apply, Fin.sum_univ_three] <;> nlinarith

theorem real_orthogonal_mul {first second : RealGL3}
    (first_orthogonal : first.val.transpose * first.val = 1)
    (second_orthogonal : second.val.transpose * second.val = 1) :
    (first * second).val.transpose * (first * second).val = 1 := by
  change (first.val * second.val).transpose * (first.val * second.val) = 1
  rw [Matrix.transpose_mul, ← mul_assoc, mul_assoc second.val.transpose,
    first_orthogonal, mul_one, second_orthogonal]

theorem real_orthogonal_inv {matrix : RealGL3}
    (orthogonal : matrix.val.transpose * matrix.val = 1) :
    matrix⁻¹.val.transpose * matrix⁻¹.val = 1 := by
  have inverse : matrix.inv = matrix.val.transpose := by
    calc
      matrix.inv = (matrix.val.transpose * matrix.val) * matrix.inv := by rw [orthogonal, one_mul]
      _ = matrix.val.transpose := by rw [mul_assoc, matrix.val_inv, mul_one]
  change matrix.inv.transpose * matrix.inv = 1
  rw [inverse, Matrix.transpose_transpose, ← inverse]
  exact matrix.val_inv

noncomputable def realPlaneHeight (matrix : RealGL3) : ℝ :=
  Real.sqrt (matrix.val 2 0 ^ 2 + matrix.val 2 1 ^ 2 + matrix.val 2 2 ^ 2)

theorem realPlaneHeight_pos (matrix : RealGL3) : 0 < realPlaneHeight matrix := by
  apply Real.sqrt_pos.mpr
  have nonnegative : 0 ≤ matrix.val 2 0 ^ 2 + matrix.val 2 1 ^ 2 + matrix.val 2 2 ^ 2 :=
    by positivity
  by_contra! not_positive
  have zero_first : matrix.val 2 0 = 0 := by nlinarith [sq_nonneg (matrix.val 2 1), sq_nonneg (matrix.val 2 2)]
  have zero_second : matrix.val 2 1 = 0 := by nlinarith [sq_nonneg (matrix.val 2 0), sq_nonneg (matrix.val 2 2)]
  have zero_last : matrix.val 2 2 = 0 := by nlinarith [sq_nonneg (matrix.val 2 0), sq_nonneg (matrix.val 2 1)]
  have entry := congrArg (fun value : Matrix (Fin 3) (Fin 3) ℝ => value 2 2) matrix.val_inv
  simp [Matrix.mul_apply, Fin.sum_univ_three, zero_first, zero_second, zero_last] at entry

theorem realPlaneHeight_sq (matrix : RealGL3) :
    realPlaneHeight matrix ^ 2 =
      matrix.val 2 0 ^ 2 + matrix.val 2 1 ^ 2 + matrix.val 2 2 ^ 2 := by
  apply Real.sq_sqrt
  positivity

theorem real_plane_first_rotation (matrix : RealGL3) :
    ∃ rotation : RealGL3, rotation.val.transpose * rotation.val = 1 ∧
      (matrix * rotation).val 2 0 = 0 ∧
      (matrix * rotation).val 2 1 ^ 2 + (matrix * rotation).val 2 2 ^ 2 =
        realPlaneHeight matrix ^ 2 := by
  by_cases zero : matrix.val 2 0 ^ 2 + matrix.val 2 1 ^ 2 = 0
  · have first_zero : matrix.val 2 0 = 0 := by nlinarith [sq_nonneg (matrix.val 2 1)]
    refine ⟨1, by simp, by simpa, ?_⟩
    simp only [mul_one, realPlaneHeight_sq, first_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
  · let radius := Real.sqrt (matrix.val 2 0 ^ 2 + matrix.val 2 1 ^ 2)
    have radius_sq : radius ^ 2 = matrix.val 2 0 ^ 2 + matrix.val 2 1 ^ 2 :=
      Real.sq_sqrt (by positivity)
    have radius_nonzero : radius ≠ 0 := by
      intro radius_zero
      rw [radius_zero, zero_pow (by decide : 2 ≠ 0)] at radius_sq
      exact zero radius_sq.symm
    have unit : (matrix.val 2 1 / radius) ^ 2 + (matrix.val 2 0 / radius) ^ 2 = 1 := by
      field_simp
      nlinarith
    let rotation := firstRealRotation (matrix.val 2 1 / radius) (matrix.val 2 0 / radius) unit
    refine ⟨rotation, firstRealRotation_orthogonal _ _ _, ?_, ?_⟩
    · change (matrix.val * rotation.val) 2 0 = 0
      simp [rotation, firstRealRotation, Matrix.mul_apply, Fin.sum_univ_three]
      ring
    · have second : (matrix * rotation).val 2 1 = radius := by
        change (matrix.val * rotation.val) 2 1 = radius
        simp [rotation, firstRealRotation, Matrix.mul_apply, Fin.sum_univ_three]
        field_simp
        nlinarith
      have last : (matrix * rotation).val 2 2 = matrix.val 2 2 := by
        change (matrix.val * rotation.val) 2 2 = matrix.val 2 2
        simp [rotation, firstRealRotation, Matrix.mul_apply, Fin.sum_univ_three]
      rw [second, last, radius_sq, realPlaneHeight_sq]

theorem real_plane_rotation (matrix : RealGL3) :
    ∃ rotation : RealGL3, rotation.val.transpose * rotation.val = 1 ∧
      InPlaneParabolic (matrix * rotation) ∧
      (matrix * rotation).val 2 2 = realPlaneHeight matrix := by
  obtain ⟨first, first_orthogonal, first_zero, row_norm⟩ := real_plane_first_rotation matrix
  let intermediate := matrix * first
  have height_nonzero : realPlaneHeight matrix ≠ 0 := ne_of_gt (realPlaneHeight_pos matrix)
  have unit : (intermediate.val 2 2 / realPlaneHeight matrix) ^ 2 +
      (intermediate.val 2 1 / realPlaneHeight matrix) ^ 2 = 1 := by
    field_simp
    nlinarith
  let last := lastRealRotation (intermediate.val 2 2 / realPlaneHeight matrix)
    (intermediate.val 2 1 / realPlaneHeight matrix) unit
  refine ⟨first * last, real_orthogonal_mul first_orthogonal (lastRealRotation_orthogonal _ _ _), ?_, ?_⟩
  · rw [← mul_assoc]
    constructor
    · change (intermediate.val * last.val) 2 0 = 0
      simpa [last, lastRealRotation, Matrix.mul_apply, Fin.sum_univ_three] using
        (show intermediate.val 2 0 = 0 from first_zero)
    · change (intermediate.val * last.val) 2 1 = 0
      simp [last, lastRealRotation, Matrix.mul_apply, Fin.sum_univ_three]
      ring
  · rw [← mul_assoc]
    change (intermediate.val * last.val) 2 2 = realPlaneHeight matrix
    simp [last, lastRealRotation, Matrix.mul_apply, Fin.sum_univ_three]
    field_simp
    nlinarith

theorem real_plane_decomposition (matrix : RealGL3) :
    ∃ parabolic compactMatrix : RealGL3,
      matrix = parabolic * compactMatrix ∧ InPlaneParabolic parabolic ∧
      compactMatrix.val.transpose * compactMatrix.val = 1 ∧
      parabolic.val 2 2 = realPlaneHeight matrix := by
  obtain ⟨rotation, orthogonal, parabolic, height⟩ := real_plane_rotation matrix
  exact ⟨matrix * rotation, rotation⁻¹, by simp, parabolic, real_orthogonal_inv orthogonal, height⟩

theorem real_plane_levi_decomposition (matrix : RealGL3) :
    ∃ (first second : ℝ) (binary : BinaryRealGL) (scalar : ℝˣ) (compactMatrix : RealGL3),
      matrix = planeUnipotent first second * planeLevi binary scalar * compactMatrix ∧
      compactMatrix.val.transpose * compactMatrix.val = 1 ∧
      scalar.val = realPlaneHeight matrix := by
  obtain ⟨parabolic, compactMatrix, decomposition, parabolic_spec, orthogonal, height⟩ :=
    real_plane_decomposition matrix
  obtain ⟨first, second, binary, scalar, factorization⟩ :=
    planeParabolic_factorization parabolic parabolic_spec
  refine ⟨first, second, binary, scalar, compactMatrix, ?_, orthogonal, ?_⟩
  · rw [← factorization]
    exact decomposition
  · rw [factorization] at height
    simpa [planeUnipotent, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_three] using height

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
