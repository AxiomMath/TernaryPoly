module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.DirectionalRealization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.StageTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationCircle TernaryPeriodPolynomials.PlaneEisensteinContinuation.RotationDifferentiation
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixRotationSpan

noncomputable def diagonalDouble : BinaryRealGL :=
  ⟨!![2, 0; 0, 1], !![1 / 2, 0; 0, 1], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem generator_matrix : generator = !![0, -(2 * Real.pi); 2 * Real.pi, 0] := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp [generator, complexMatrix]

theorem conjugate_diagonalDouble :
    conjugation diagonalDouble generator = !![0, -Real.pi; 4 * Real.pi, 0] := by
  rw [conjugation_apply, generator_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [diagonalDouble, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem conjugate_unipotent :
    conjugation (binaryUnipotent (1 : ℝ)) generator =
      !![-(2 * Real.pi), -(4 * Real.pi); 2 * Real.pi, 2 * Real.pi] := by
  rw [conjugation_apply, generator_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The identity and three explicit conjugate rotation directions span all binary real matrices. -/
theorem exists_decomposition (matrix : BinaryMatrix) :
    ∃ a b c d : ℝ, matrix = a • (1 : BinaryMatrix) + b • generator +
      c • conjugation diagonalDouble generator + d • conjugation (binaryUnipotent (1 : ℝ)) generator := by
  refine ⟨(matrix 0 0 + matrix 1 1) / 2,
    (7 * matrix 0 0 - 7 * matrix 1 1 - 8 * matrix 0 1 - 2 * matrix 1 0) / (12 * Real.pi),
    (2 * matrix 0 1 + 2 * matrix 1 0 + matrix 1 1 - matrix 0 0) / (6 * Real.pi),
    (matrix 1 1 - matrix 0 0) / (4 * Real.pi), ?_⟩
  rw [conjugate_diagonalDouble, conjugate_unipotent, generator_matrix]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    <;> field_simp <;> ring

theorem linearMap_ext {Target : Type*} [AddCommGroup Target] [Module ℝ Target]
    (first second : BinaryMatrix →ₗ[ℝ] Target)
    (identity : first 1 = second 1)
    (rotation : first generator = second generator)
    (diagonal : first (conjugation diagonalDouble generator) = second (conjugation diagonalDouble generator))
    (unipotent : first (conjugation (binaryUnipotent (1 : ℝ)) generator) =
      second (conjugation (binaryUnipotent (1 : ℝ)) generator)) : first = second := by
  apply LinearMap.ext
  intro matrix
  obtain ⟨a, b, c, d, equality⟩ := exists_decomposition matrix
  rw [equality]
  simp only [map_add, map_smul, identity, rotation, diagonal, unipotent]

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.MatrixRotationSpan
