module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.MellinNonvanishing
public import Mathlib.LinearAlgebra.CrossProduct

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames

abbrev Rectangular (ring : Type*) := Matrix (Fin 3) (Fin 2) ring

def columns {ring : Type*} (matrix : Matrix (Fin 3) (Fin 3) ring) : Rectangular ring :=
  fun row column => matrix row column.castSucc

def exterior {ring : Type*} [CommRing ring] (frame : Rectangular ring) : Fin 3 → ring :=
  crossProduct (fun row => frame row 0) (fun row => frame row 1)

def FullRank {field : Type*} [Field field] (frame : Rectangular field) : Prop := exterior frame ≠ 0

theorem fullRank_iff_linearIndependent {field : Type*} [Field field] (frame : Rectangular field) :
    FullRank frame ↔ LinearIndependent field (fun column row => frame row column) := by
  have equality : ![(fun row => frame row 0), (fun row => frame row 1)] =
      (fun column row => frame row column) := by
    funext column
    fin_cases column <;> rfl
  simpa only [FullRank, exterior, equality] using
    (crossProduct_ne_zero_iff_linearIndependent (v := fun row => frame row 0) (w := fun row => frame row 1))

theorem columns_mul {ring : Type*} [CommRing ring] (first second : Matrix (Fin 3) (Fin 3) ring) :
    columns (first * second) = first * columns second := rfl

theorem mul_standard {ring : Type*} [CommRing ring] (matrix : Matrix (Fin 3) (Fin 3) ring) :
    matrix * columns (1 : Matrix (Fin 3) (Fin 3) ring) = columns matrix := by
  rw [← columns_mul, mul_one]

theorem det_eq_exterior {ring : Type*} [CommRing ring] (matrix : Matrix (Fin 3) (Fin 3) ring) :
    matrix.det = ∑ row : Fin 3, exterior (columns matrix) row * matrix row 2 := by
  simp [Matrix.det_fin_three, exterior, columns, crossProduct, Fin.sum_univ_three]
  ring

theorem columns_fullRank {field : Type*} [Field field] (matrix : GeneralLinearGroup (Fin 3) field) :
    FullRank (columns matrix.val) := by
  intro vanishing
  apply GeneralLinearGroup.det_ne_zero matrix
  rw [det_eq_exterior, vanishing]
  simp

def completion {field : Type*} [Field field] (frame : Rectangular field) (pivot : Fin 3) :
    Matrix (Fin 3) (Fin 3) field :=
  fun row => ![frame row 0, frame row 1, if row = pivot then 1 else 0]

theorem completion_columns {field : Type*} [Field field] (frame : Rectangular field) (pivot : Fin 3) :
    columns (completion frame pivot) = frame := by
  ext row column
  fin_cases column <;> rfl

theorem completion_det {field : Type*} [Field field] (frame : Rectangular field) (pivot : Fin 3) :
    (completion frame pivot).det = exterior frame pivot := by
  rw [det_eq_exterior, completion_columns]
  simp [completion]

theorem exists_completion {field : Type*} [Field field] (frame : Rectangular field) (fullRank : FullRank frame) :
    ∃ matrix : GeneralLinearGroup (Fin 3) field, columns matrix.val = frame := by
  have nonzero : ∃ pivot, exterior frame pivot ≠ 0 := by
    by_contra vanishing
    push Not at vanishing
    exact fullRank (funext vanishing)
  obtain ⟨pivot, nonzero⟩ := nonzero
  refine ⟨GeneralLinearGroup.mkOfDetNeZero (completion frame pivot) ?_, completion_columns frame pivot⟩
  rw [completion_det]
  exact nonzero

abbrev Frame := {frame : Rectangular ℚ // FullRank frame}

def ofMatrix (matrix : RationalGL3) : Frame := ⟨columns matrix.val, columns_fullRank matrix⟩

noncomputable def complete (frame : Frame) : RationalGL3 := (exists_completion frame.val frame.property).choose

theorem complete_columns (frame : Frame) : columns (complete frame).val = frame.val :=
  (exists_completion frame.val frame.property).choose_spec

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RectangularFrames
