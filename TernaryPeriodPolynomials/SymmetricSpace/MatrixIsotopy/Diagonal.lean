module

public import TernaryPeriodPolynomials.SymmetricSpace.MatrixIsotopy.SpecialLinear

@[expose] public section


noncomputable section
namespace TernaryPoly.RealMatrixIsotopy
open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A genuine diagonal unit changing just one diagonal coordinate. -/
def diagonalUnit (i : ι) (u : ℝˣ) : GeneralLinearGroup ι ℝ where
  val := diagonal fun j => if j = i then (u : ℝ) else 1
  inv := diagonal fun j => if j = i then (↑(u⁻¹) : ℝ) else 1
  val_inv := by
    simp only [diagonal_mul_diagonal, diagonal_eq_one]
    funext j
    split_ifs <;> simp
  inv_val := by
    simp only [diagonal_mul_diagonal, diagonal_eq_one]
    funext j
    split_ifs <;> simp

@[simp] theorem diagonalUnit_one (i : ι) : diagonalUnit i 1 = 1 := by
  apply Units.ext
  simp [diagonalUnit]

@[simp] theorem det_diagonalUnit (i : ι) (u : ℝˣ) :
    GeneralLinearGroup.det (diagonalUnit i u) = u := by
  apply Units.ext
  simp [diagonalUnit, GeneralLinearGroup.det]

/-- Both the diagonal matrices and their inverse matrices vary continuously. -/
theorem continuous_diagonalUnit (i : ι) : Continuous (diagonalUnit i) := by
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro j k
    change Continuous (fun u : ℝˣ => (diagonal fun l => if l = i then (u : ℝ) else 1) j k)
    simp only [diagonal_apply]
    split_ifs <;> fun_prop
  · apply continuous_matrix
    intro j k
    change Continuous (fun u : ℝˣ => (diagonal fun l => if l = i then (↑(u⁻¹) : ℝ) else 1) j k)
    simp only [diagonal_apply]
    split_ifs <;> fun_prop

/-- The straight segment from one to a positive real number stays positive. -/
theorem positiveSegment_pos (a : ℝ) (ha : 0 < a) (t : unitInterval) :
    0 < (1 - (t : ℝ)) + (t : ℝ) * a := by
  have ht0 := t.property.1
  have ht1 := t.property.2
  by_cases ht : (t : ℝ) = 1
  · simp [ht, ha]
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne ht1 ht
    positivity

/-- A continuous path in the actual real unit group from one to a positive unit. -/
def positiveUnitPath (u : ℝˣ) (hu : 0 < (u : ℝ)) : Path 1 u where
  toFun t := Units.mk0 ((1 - (t : ℝ)) + (t : ℝ) * (u : ℝ))
    (ne_of_gt (positiveSegment_pos u hu t))
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun t : unitInterval => (1 - (t : ℝ)) + (t : ℝ) * (u : ℝ))
      fun_prop
    · change Continuous (fun t : unitInterval => ((1 - (t : ℝ)) + (t : ℝ) * (u : ℝ))⁻¹)
      exact Continuous.inv₀ (by fun_prop) (fun t => ne_of_gt (positiveSegment_pos u hu t))
  source' := by apply Units.ext; simp
  target' := by apply Units.ext; simp

/-- A positive diagonal correction is joined to the identity within actual invertible matrices. -/
theorem diagonalUnit_joined_one (i : ι) (u : ℝˣ) (hu : 0 < (u : ℝ)) :
    Joined 1 (diagonalUnit i u) := by
  simpa using (show Joined 1 u from ⟨positiveUnitPath u hu⟩).map (continuous_diagonalUnit i)

end TernaryPoly.RealMatrixIsotopy
