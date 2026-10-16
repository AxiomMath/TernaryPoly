module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Adelic.Pivot

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BinaryGaussian

variable {R : Type*} [CommRing R]

def lower (entry : R) : GeneralLinearGroup (Fin 2) R where
  val := !![1, 0; entry, 1]
  inv := !![1, 0; -entry, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def diagonal (first second : Rˣ) : GeneralLinearGroup (Fin 2) R where
  val := !![first.val, 0; 0, second.val]
  inv := !![first.inv, 0; 0, second.inv]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem upper_det (entry : R) : GeneralLinearGroup.det (binaryUnipotent entry) = 1 := by
  apply Units.ext
  simp [GeneralLinearGroup.det, binaryUnipotent, Matrix.det_fin_two]

theorem lower_det (entry : R) : GeneralLinearGroup.det (lower entry) = 1 := by
  apply Units.ext
  simp [GeneralLinearGroup.det, lower, Matrix.det_fin_two]

theorem diagonal_det (first second : Rˣ) : GeneralLinearGroup.det (diagonal first second) = first * second := by
  apply Units.ext
  simp [GeneralLinearGroup.det, diagonal, Matrix.det_fin_two]

theorem upper_neg_mul (entry : R) : binaryUnipotent (-entry) * binaryUnipotent entry = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem pivot_decomposition (matrix : GeneralLinearGroup (Fin 2) R) (pivot : Rˣ)
    (pivotEntry : pivot.val = matrix.val 0 0) :
    matrix = lower (matrix.val 1 0 * pivot.inv) * diagonal pivot (GeneralLinearGroup.det matrix * pivot⁻¹) *
      binaryUnipotent (pivot.inv * matrix.val 0 1) := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [lower, diagonal, binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two,
      GeneralLinearGroup.det, Matrix.det_fin_two, ← pivotEntry]
  · calc
      _ = matrix.val 1 1 * (pivot.val * pivot.inv) := by simp
      _ = _ := by simp only [Units.inv_eq_val_inv]; ring

theorem adelic_decomposition (matrix : BinaryAdelicGL) :
    ∃ upperLeft lowerEntry upperRight : Adeles, ∃ first second : Adelesˣ,
      matrix = binaryUnipotent upperLeft * lower lowerEntry * diagonal first second * binaryUnipotent upperRight := by
  obtain ⟨shift, pivot, pivotEntry⟩ := AdelicPivot.matrix_unit_pivot matrix
  let changed := binaryUnipotent shift * matrix
  have changedPivot : pivot.val = changed.val 0 0 := by
    simpa [changed, binaryUnipotent, Matrix.mul_apply, Fin.sum_univ_two, mul_comm] using pivotEntry
  refine ⟨-shift, changed.val 1 0 * pivot.inv, pivot.inv * changed.val 0 1,
    pivot, GeneralLinearGroup.det changed * pivot⁻¹, ?_⟩
  have equality := congrArg (fun m => binaryUnipotent (-shift) * m)
    (pivot_decomposition changed pivot changedPivot)
  have cancelled : binaryUnipotent (-shift) * changed = matrix := by
    change binaryUnipotent (-shift) * (binaryUnipotent shift * matrix) = matrix
    rw [← mul_assoc, upper_neg_mul, one_mul]
  rw [cancelled] at equality
  simpa only [mul_assoc] using equality

def rowAction (matrix : GeneralLinearGroup (Fin 2) R) (coordinates : R × R) : R × R :=
  (coordinates.1 * matrix.val 0 0 + coordinates.2 * matrix.val 1 0,
    coordinates.1 * matrix.val 0 1 + coordinates.2 * matrix.val 1 1)

theorem rowAction_mul (first second : GeneralLinearGroup (Fin 2) R) (coordinates : R × R) :
    rowAction (first * second) coordinates = rowAction second (rowAction first coordinates) := by
  apply Prod.ext
  all_goals simp [rowAction, Matrix.mul_apply, Fin.sum_univ_two]; ring

theorem rowAction_one (coordinates : R × R) : rowAction (1 : GeneralLinearGroup (Fin 2) R) coordinates = coordinates := by
  simp [rowAction]

def rowEquiv [TopologicalSpace R] [IsTopologicalRing R] (matrix : GeneralLinearGroup (Fin 2) R) :
    (R × R) ≃ₜ+ (R × R) where
  toFun := rowAction matrix
  invFun := rowAction matrix⁻¹
  left_inv coordinates := by rw [← rowAction_mul, mul_inv_cancel, rowAction_one]
  right_inv coordinates := by rw [← rowAction_mul, inv_mul_cancel, rowAction_one]
  map_add' first second := by
    apply Prod.ext
    all_goals simp [rowAction]; ring
  continuous_toFun := by unfold rowAction; fun_prop
  continuous_invFun := by unfold rowAction; fun_prop

theorem rowEquiv_mul [TopologicalSpace R] [IsTopologicalRing R]
    (first second : GeneralLinearGroup (Fin 2) R) :
    rowEquiv (first * second) = (rowEquiv first).trans (rowEquiv second) := by
  apply DFunLike.ext
  intro coordinates
  exact rowAction_mul first second coordinates

theorem rowAction_upper (entry : R) (coordinates : R × R) :
    rowAction (binaryUnipotent entry) coordinates = (coordinates.1, coordinates.1 * entry + coordinates.2) := by
  simp [rowAction, binaryUnipotent]

theorem rowAction_lower (entry : R) (coordinates : R × R) :
    rowAction (lower entry) coordinates = (coordinates.1 + coordinates.2 * entry, coordinates.2) := by
  simp [rowAction, lower]

theorem rowAction_diagonal (first second : Rˣ) (coordinates : R × R) :
    rowAction (diagonal first second) coordinates = (first.val * coordinates.1, second.val * coordinates.2) := by
  simp [rowAction, diagonal, mul_comm]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.BinaryGaussian
