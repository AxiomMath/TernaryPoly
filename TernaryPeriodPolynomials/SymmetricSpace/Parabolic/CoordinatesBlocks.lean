module

public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.CoordinatesActionAlgebra
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpaceParabolicCoordinates

/-- The explicit 2+1 block indexing of the actual three-coordinate matrix model. -/
def blockIndexEquiv : (Fin 2 ⊕ Fin 1) ≃ Fin 3 := finSumFinEquiv

@[simp] theorem blockIndexEquiv_left (i : Fin 2) :
    blockIndexEquiv (Sum.inl i)=topIndex i := rfl

@[simp] theorem blockIndexEquiv_right (i : Fin 1) :
    blockIndexEquiv (Sum.inr i)=2 := by fin_cases i; rfl

/-- The literal matrix used in the action is the standard 2+1 block parabolic matrix. -/
theorem blockMatrix_fromBlocks (A : Mat2) (u : Vec2) (d : ℝ) :
    (blockMatrix A u d).submatrix blockIndexEquiv blockIndexEquiv=
      Matrix.fromBlocks A (fun i (_ : Fin 1) => u i)
        (0 : Matrix (Fin 1) (Fin 2) ℝ) (fun (_ _ : Fin 1) => d) := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    fin_cases i <;> fin_cases j <;> rfl

/-- The inverse formula is literally the requested Schur-complement block assembly. -/
theorem assemble_fromBlocks (v : Vec2) (B : Mat2) :
    (assemble v B).submatrix blockIndexEquiv blockIndexEquiv=
      Matrix.fromBlocks (B+Matrix.vecMulVec v v)
        (fun i (_ : Fin 1) => v i) (fun (_ : Fin 1) j => v j)
        (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    fin_cases i <;> fin_cases j <;> rfl

theorem diagonalBlock_fromBlocks (B : Mat2) :
    (diagonalBlock B).submatrix blockIndexEquiv blockIndexEquiv=
      Matrix.fromBlocks B (0 : Matrix (Fin 2) (Fin 1) ℝ)
        (0 : Matrix (Fin 1) (Fin 2) ℝ) (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    fin_cases i <;> fin_cases j <;> rfl

end TernaryPoly.SymmetricSpaceParabolicCoordinates
