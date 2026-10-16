module

public import TernaryPeriodPolynomials.Building.BoundaryApartments.Good.RationalApartmentGeneration

@[expose] public section


open GeneralEisenstein

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers

open Matrix

abbrev AffinePoint := Fin 2 → ℚ

def affineVector (point : AffinePoint) : Fin 3 → ℚ := ![point 0, point 1, 1]

def affineFrame (point : AffinePoint) : RationalGL3 :=
  GeneralLinearGroup.mkOfDetNeZero !![point 0,1,0;point 1,0,1;1,0,0]
    (by simp [Matrix.det_fin_three])

def affineLine (point : AffinePoint) : Flags .line := QuotientGroup.mk (affineFrame point)

theorem affineFrame_firstColumn (point : AffinePoint) (row : Fin 3) :
    (affineFrame point).val row 0 = affineVector point row := by
  fin_cases row <;> rfl

theorem affineVector_injective : Function.Injective affineVector := by
  intro first second same
  ext index
  fin_cases index
  · exact congrFun same 0
  · exact congrFun same 1

theorem affineLine_injective : Function.Injective affineLine := by
  intro first second same
  obtain ⟨scalar, columns⟩ := firstColumn_multiple_of_line_eq (affineFrame first)
    (affineFrame second) same
  have scalar_one : scalar = 1 := by simpa [affineFrame] using (columns 2).symm
  apply affineVector_injective
  ext row
  simpa only [affineFrame_firstColumn, scalar_one, one_mul] using (columns row).symm

theorem good_line_affinePoint (line : Flags .line) (good : GoodFlag .line line) :
    ∃ point : AffinePoint, affineLine point = line := by
  induction line using Quotient.inductionOn with
  | _ frame =>
    obtain ⟨vector, scalar, _, columns, vector_good⟩ := good_line_integral_multiple frame good
    have last_nonzero : frame.val 2 0 ≠ 0 := by
      intro last_zero
      have vector_zero : (vector 2 : ℚ) = 0 := by rw [columns, last_zero, mul_zero]
      have integer_zero : vector 2 = 0 := by exact_mod_cast vector_zero
      exact vector_good (by rw [integer_zero, Int.cast_zero])
    refine ⟨![frame.val 0 0 / frame.val 2 0, frame.val 1 0 / frame.val 2 0], ?_⟩
    symm
    apply line_flag_eq_of_column (1 / frame.val 2 0)
    intro row
    fin_cases row <;> simp [affineFrame, div_eq_mul_inv, last_nonzero, mul_comm]

theorem affine_pair_frame_exists (first second : AffinePoint) (different : first ≠ second) :
    ∃ frame : RationalGL3, (∀ row, frame.val row 0 = affineVector first row) ∧
      (∀ row, frame.val row 1 = affineVector second row) := by
  by_cases second_different : first 1 ≠ second 1
  · refine ⟨GeneralLinearGroup.mkOfDetNeZero
      !![first 0,second 0,1;first 1,second 1,0;1,1,0] ?_, ?_, ?_⟩
    · simpa [Matrix.det_fin_three] using sub_ne_zero.mpr second_different
    · intro row
      fin_cases row <;> rfl
    · intro row
      fin_cases row <;> rfl
  · have first_different : first 0 ≠ second 0 := by
      intro same
      apply different
      ext index
      fin_cases index
      · exact same
      · exact not_ne_iff.mp second_different
    refine ⟨GeneralLinearGroup.mkOfDetNeZero
      !![first 0,second 0,0;first 1,second 1,1;1,1,0] ?_, ?_, ?_⟩
    · simpa [Matrix.det_fin_three, sub_eq_add_neg, add_comm] using
        sub_ne_zero.mpr first_different.symm
    · intro row
      fin_cases row <;> rfl
    · intro row
      fin_cases row <;> rfl

def affinePairFrame (first second : AffinePoint) (different : first ≠ second) : RationalGL3 :=
  Classical.choose (affine_pair_frame_exists first second different)

theorem affinePairFrame_columns (first second : AffinePoint) (different : first ≠ second) :
    (∀ row, (affinePairFrame first second different).val row 0 = affineVector first row) ∧
      (∀ row, (affinePairFrame first second different).val row 1 = affineVector second row) :=
  Classical.choose_spec (affine_pair_frame_exists first second different)

def affinePair (first second : AffinePoint) : EdgeChains :=
  if different : first ≠ second then framePair (affinePairFrame first second different) else 0

theorem affinePair_self (point : AffinePoint) : affinePair point point = 0 := by
  simp [affinePair]

theorem affinePair_reverse (first second : AffinePoint) :
    affinePair second first = -affinePair first second := by
  by_cases same : first = second
  · subst second
    simp only [affinePair_self, neg_zero]
  · rw [affinePair, dite_eq_left (Ne.symm same), affinePair, dite_eq_left same]
    apply framePair_reverse_of_columns
    · intro row
      rw [(affinePairFrame_columns _ _ _).1, (affinePairFrame_columns _ _ _).2]
    · intro row
      rw [(affinePairFrame_columns _ _ _).2, (affinePairFrame_columns _ _ _).1]

theorem affinePair_frame (frame : RationalGL3) (first second : AffinePoint)
    (first_column : ∀ row, frame.val row 0 = affineVector first row)
    (second_column : ∀ row, frame.val row 1 = affineVector second row) :
    affinePair first second = framePair frame := by
  have different : first ≠ second := by
    intro same
    have determinant_zero := Matrix.det_zero_of_column_eq (M := frame.val)
      (show (0 : Fin 3) ≠ 1 by decide)
      (fun row => by rw [first_column, second_column, same])
    exact rationalFrame_det_nonzero frame determinant_zero
  rw [affinePair, dite_eq_left different]
  apply framePair_eq_of_columns
  · intro row
    rw [first_column, (affinePairFrame_columns _ _ _).1]
  · intro row
    rw [second_column, (affinePairFrame_columns _ _ _).2]

end TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
