module

public import TernaryPeriodPolynomials.SymmetricSpace.MatrixIsotopy.Diagonal

@[expose] public section


noncomputable section
namespace TernaryPoly.RealMatrixIsotopy
open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every positive-determinant real invertible matrix is joined to identity in the actual unit group. -/
theorem positiveGL_joined_one (A : GeneralLinearGroup ι ℝ)
    (hA : 0 < (GeneralLinearGroup.det A : ℝ)) : Joined 1 A := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
      let := h
      simpa only [Subsingleton.elim A 1] using Joined.refl (1 : GeneralLinearGroup ι ℝ)
  | inr h =>
      let := h
      let i : ι := Classical.choice h
      let D := diagonalUnit i (GeneralLinearGroup.det A)
      let B := D⁻¹ * A
      have hB : GeneralLinearGroup.det B = 1 := by simp [B, D]
      let S : SpecialLinearGroup ι ℝ := ⟨B.val, congrArg Units.val hB⟩
      have hSB : SpecialLinearGroup.toGL S = B := by apply Units.ext; rfl
      have hjB : Joined 1 B := by
        simpa only [map_one, hSB] using
          (specialLinear_joined_one S).map SpecialLinearGroup.continuous_toGL
      have hjD : Joined 1 D := diagonalUnit_joined_one i _ hA
      simpa [B] using hjD.mul hjB

/-- A chosen genuine path of invertible matrices to a positive-determinant matrix. -/
def positiveGLPath (A : GeneralLinearGroup ι ℝ)
    (hA : 0 < (GeneralLinearGroup.det A : ℝ)) : Path 1 A :=
  (positiveGL_joined_one A hA).somePath

/-- Positive determinant constructs the actual matrix unit used by the path. -/
def positiveMatrixUnit (A : Matrix ι ι ℝ) (hA : 0 < A.det) : GeneralLinearGroup ι ℝ :=
  GeneralLinearGroup.mkOfDetNeZero A (ne_of_gt hA)

/-- Matrix-level input interface for the actual general-linear path. -/
def positiveMatrixPath (A : Matrix ι ι ℝ) (hA : 0 < A.det) :
    Path 1 (positiveMatrixUnit A hA) :=
  positiveGLPath (positiveMatrixUnit A hA) hA

/-- Every intermediate matrix is invertible, literally as a matrix unit. -/
theorem positiveMatrixPath_det_ne_zero (A : Matrix ι ι ℝ) (hA : 0 < A.det)
    (t : unitInterval) : ((positiveMatrixPath A hA t).val).det ≠ 0 :=
  GeneralLinearGroup.det_ne_zero _

/-- Matrix values along the constructed path vary continuously. -/
theorem continuous_positiveMatrixPath_val (A : Matrix ι ι ℝ) (hA : 0 < A.det) :
    Continuous (fun t => (positiveMatrixPath A hA t).val) :=
  Units.continuous_val.comp (positiveMatrixPath A hA).continuous

/-- Inverse matrix values along the constructed path vary continuously. -/
theorem continuous_positiveMatrixPath_inv (A : Matrix ι ι ℝ) (hA : 0 < A.det) :
    Continuous (fun t => ((positiveMatrixPath A hA t)⁻¹).val) :=
  Units.continuous_coe_inv.comp (positiveMatrixPath A hA).continuous

@[simp] theorem positiveMatrixPath_zero (A : Matrix ι ι ℝ) (hA : 0 < A.det) :
    (positiveMatrixPath A hA 0).val = 1 := by simp

@[simp] theorem positiveMatrixPath_one (A : Matrix ι ι ℝ) (hA : 0 < A.det) :
    (positiveMatrixPath A hA 1).val = A := by
  rw [(positiveMatrixPath A hA).target]
  rfl

end TernaryPoly.RealMatrixIsotopy
