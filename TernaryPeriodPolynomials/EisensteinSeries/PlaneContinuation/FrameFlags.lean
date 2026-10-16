module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Rectangular.Frames

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames TernaryPeriodPolynomials.PlaneEisensteinContinuation.Parabolic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameFlags

theorem standard_right {ring : Type*} [CommRing ring] (matrix : GeneralLinearGroup (Fin 2) ring) :
    columns (planeLevi matrix 1).val = columns (1 : Matrix (Fin 3) (Fin 3) ring) * matrix.val := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [columns, planeLevi, planeBlock, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem columns_mul_parabolic {ring : Type*} [CommRing ring]
    (matrix : GeneralLinearGroup (Fin 3) ring) (parabolic : planeParabolic ring) :
    columns (matrix * parabolic.val).val = columns matrix.val * (planeBinaryBlock parabolic).val := by
  ext row column
  change (∑ index : Fin 3, matrix.val row index * parabolic.val.val index column.castSucc) =
    ∑ index : Fin 2, matrix.val row index.castSucc * parabolic.val.val index.castSucc column.castSucc
  fin_cases column <;>
    simp [Fin.sum_univ_three, Fin.sum_univ_two, parabolic.property.1, parabolic.property.2]

theorem columns_mul_levi {ring : Type*} [CommRing ring]
    (matrix : GeneralLinearGroup (Fin 3) ring) (binary : GeneralLinearGroup (Fin 2) ring) :
    columns (matrix * planeLevi binary 1).val = columns matrix.val * binary.val := by
  rw [Units.val_mul, columns_mul, standard_right, ← Matrix.mul_assoc, mul_standard]

theorem columns_right_cancel {field : Type*} [Field field]
    (matrix : GeneralLinearGroup (Fin 3) field) (first second : Matrix (Fin 2) (Fin 2) field)
    (equality : columns matrix.val * first = columns matrix.val * second) : first = second := by
  have multiplied := congrArg (fun frame : Rectangular field => matrix⁻¹.val * frame) equality
  have inverseProduct : matrix⁻¹.val * matrix.val = 1 := matrix.inv_val
  have inverseColumns : matrix⁻¹.val * columns matrix.val = columns (1 : Matrix (Fin 3) (Fin 3) field) := by
    rw [← columns_mul, inverseProduct]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, inverseColumns] at multiplied
  ext row column
  have entry := congrArg (fun frame : Rectangular field => frame row.castSucc column) multiplied
  fin_cases row <;> simpa [columns, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using entry

theorem flag_eq_iff (first second : RationalGL3) :
    (QuotientGroup.mk first : Flags .plane) = QuotientGroup.mk second ↔
      ∃ binary : BinaryRationalGL, columns second.val = columns first.val * binary.val := by
  constructor
  · intro equality
    let parabolic : planeParabolic ℚ := ⟨first⁻¹ * second, QuotientGroup.eq.mp equality⟩
    refine ⟨planeBinaryBlock parabolic, ?_⟩
    have columnsEquality := columns_mul_parabolic first parabolic
    simpa only [parabolic, mul_inv_cancel_left] using columnsEquality
  · rintro ⟨binary, equality⟩
    apply QuotientGroup.eq.mpr
    have inverseProduct : first⁻¹.val * first.val = 1 := first.inv_val
    have multiplied : columns (first⁻¹ * second).val =
        columns (1 : Matrix (Fin 3) (Fin 3) ℚ) * binary.val := by
      rw [Units.val_mul, columns_mul, equality, ← Matrix.mul_assoc, ← columns_mul, inverseProduct]
    constructor
    · have entry := congrArg (fun frame : Rectangular ℚ => frame 2 0) multiplied
      simpa [columns, Matrix.mul_apply, Fin.sum_univ_two] using entry
    · have entry := congrArg (fun frame : Rectangular ℚ => frame 2 1) multiplied
      simpa [columns, Matrix.mul_apply, Fin.sum_univ_two] using entry

theorem fullRank_right_mul (frame : Frame) (binary : BinaryRationalGL) :
    FullRank (frame.val * binary.val) := by
  rw [← complete_columns frame, ← columns_mul_levi]
  exact columns_fullRank _

def changeBasis (frame : Frame) (binary : BinaryRationalGL) : Frame :=
  ⟨frame.val * binary.val, fullRank_right_mul frame binary⟩

theorem changeBasis_one (frame : Frame) : changeBasis frame 1 = frame := by
  apply Subtype.ext
  exact Matrix.mul_one _

theorem changeBasis_mul (frame : Frame) (first second : BinaryRationalGL) :
    changeBasis frame (first * second) = changeBasis (changeBasis frame first) second := by
  apply Subtype.ext
  exact (Matrix.mul_assoc _ _ _).symm

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.FrameFlags
