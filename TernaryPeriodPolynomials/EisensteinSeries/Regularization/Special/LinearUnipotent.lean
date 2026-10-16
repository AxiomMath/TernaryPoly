module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearReduction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

def realSpecialUnipotent (horizontal secondVertical firstVertical : ℝ) :
    SpecialLinearGroup (Fin 3) ℝ :=
  ⟨!![1, horizontal, firstVertical; 0, 1, secondVertical; 0, 0, 1], by
    simp [Matrix.det_fin_three]⟩

theorem realSpecialUnipotent_mul (x y z x' y' z' : ℝ) :
    realSpecialUnipotent x y z * realSpecialUnipotent x' y' z' =
      realSpecialUnipotent (x + x') (y + y') (z + z' + x * y') := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [realSpecialUnipotent, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem realSpecialUnipotent_continuous :
    Continuous (fun coordinates : ℝ × ℝ × ℝ =>
      realSpecialUnipotent coordinates.1 coordinates.2.1 coordinates.2.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro row
  apply continuous_pi
  intro column
  fin_cases row <;> fin_cases column <;> fun_prop

def realPositiveDiagonal (matrix : RealGL3) : Prop :=
  (∀ row column, row ≠ column → matrix.val row column = 0) ∧
    ∀ index, 0 < matrix.val index index

theorem realSpecialUnipotent_diagonal_val (x y z : ℝ) (diagonal : SpecialLinearGroup (Fin 3) ℝ)
    (diagonal_spec : realPositiveDiagonal (SpecialLinearGroup.toGL diagonal)) :
    (SpecialLinearGroup.toGL (realSpecialUnipotent x y z * diagonal)).val =
      !![diagonal.val 0 0, x * diagonal.val 1 1, z * diagonal.val 2 2;
        0, diagonal.val 1 1, y * diagonal.val 2 2; 0, 0, diagonal.val 2 2] := by
  have off (row column : Fin 3) (different : row ≠ column) : diagonal.val row column = 0 :=
    diagonal_spec.1 row column different
  change (realSpecialUnipotent x y z).val * diagonal.val = _
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [realSpecialUnipotent, Matrix.mul_apply, Fin.sum_univ_three,
      off 0 1 (by decide), off 0 2 (by decide), off 1 0 (by decide),
      off 1 2 (by decide), off 2 0 (by decide), off 2 1 (by decide)]

theorem realSpecialUnipotent_diagonal_positiveTriangular (x y z : ℝ)
    (diagonal : SpecialLinearGroup (Fin 3) ℝ)
    (diagonal_spec : realPositiveDiagonal (SpecialLinearGroup.toGL diagonal)) :
    realPositiveTriangular (SpecialLinearGroup.toGL (realSpecialUnipotent x y z * diagonal)) := by
  unfold realPositiveTriangular InPlaneParabolic
  rw [realSpecialUnipotent_diagonal_val _ _ _ _ diagonal_spec]
  exact ⟨⟨rfl, rfl⟩, rfl, diagonal_spec.2 0, diagonal_spec.2 1, diagonal_spec.2 2⟩

theorem realSpecialUnipotent_coordinates_unique {x y z x' y' z' : ℝ}
    {diagonal diagonal' rotation rotation' : SpecialLinearGroup (Fin 3) ℝ}
    (diagonal_spec : realPositiveDiagonal (SpecialLinearGroup.toGL diagonal))
    (diagonal_spec' : realPositiveDiagonal (SpecialLinearGroup.toGL diagonal'))
    (orthogonal : rotation ∈ realSpecialOrthogonal)
    (orthogonal' : rotation' ∈ realSpecialOrthogonal)
    (equality : realSpecialUnipotent x y z * diagonal * rotation =
      realSpecialUnipotent x' y' z' * diagonal' * rotation') :
    x = x' ∧ y = y' ∧ z = z' := by
  have equalityGL := congrArg SpecialLinearGroup.toGL equality
  simp only [map_mul] at equalityGL
  obtain ⟨triangular_eq, _⟩ := realPositiveTriangular_orthogonal_unique
    (realSpecialUnipotent_diagonal_positiveTriangular x y z diagonal diagonal_spec)
    (realSpecialUnipotent_diagonal_positiveTriangular x' y' z' diagonal' diagonal_spec')
    orthogonal orthogonal' (by simpa only [map_mul] using equalityGL)
  have values := congrArg Units.val triangular_eq
  rw [realSpecialUnipotent_diagonal_val _ _ _ _ diagonal_spec,
    realSpecialUnipotent_diagonal_val _ _ _ _ diagonal_spec'] at values
  have middle := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix 1 1) values
  have last := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix 2 2) values
  have horizontal := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix 0 1) values
  have vertical1 := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix 1 2) values
  have vertical0 := congrArg (fun matrix : Matrix (Fin 3) (Fin 3) ℝ => matrix 0 2) values
  change diagonal.val 1 1 = diagonal'.val 1 1 at middle
  change diagonal.val 2 2 = diagonal'.val 2 2 at last
  change x * diagonal.val 1 1 = x' * diagonal'.val 1 1 at horizontal
  change y * diagonal.val 2 2 = y' * diagonal'.val 2 2 at vertical1
  change z * diagonal.val 2 2 = z' * diagonal'.val 2 2 at vertical0
  rw [middle] at horizontal
  rw [last] at vertical1 vertical0
  exact ⟨mul_right_cancel₀ (ne_of_gt (diagonal_spec'.2 1)) horizontal,
    mul_right_cancel₀ (ne_of_gt (diagonal_spec'.2 2)) vertical1,
    mul_right_cancel₀ (ne_of_gt (diagonal_spec'.2 2)) vertical0⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
