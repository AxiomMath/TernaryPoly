module

public import Mathlib

@[expose] public section


/-!
# The adjugate-transpose identity for column lattice representatives

Formalized by Claude Haiku 5.5.

For `A = [[a,0],[b,d]]` with `a, d ≠ 0` and `m = a d`, the paper's identity
`m A⁻¹ = S Aᵀ S⁻¹` with `S = [[0,-1],[1,0]]` holds over any field.
-/

open Matrix

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeMatrix

variable {K : Type*} [Field K]

/-- The inverse of a lower triangular column representative `[[a,0],[b,d]]`. -/
theorem inv_lowerTri (a b d : K) (ha : a ≠ 0) (hd : d ≠ 0) :
    (!![a, 0; b, d])⁻¹ = (a * d)⁻¹ • !![d, 0; -b, a] := by
  have hm : a * d ≠ 0 := mul_ne_zero ha hd
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals ring

/-- The matrix identity `m A⁻¹ = S Aᵀ S⁻¹` of the paper, with `m = a d`. -/
theorem smul_inv_eq_conj_transpose (a b d : K) (ha : a ≠ 0) (hd : d ≠ 0) :
    (a * d) • (!![a, 0; b, d])⁻¹ =
      !![0, -1; 1, 0] * (!![a, 0; b, d])ᵀ * !![0, -1; 1, 0]⁻¹ := by
  have hS : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) K)⁻¹ = !![0, 1; -1, 0] := by
    apply Matrix.inv_eq_right_inv
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [inv_lowerTri a b d ha hd, hS, smul_smul, mul_inv_cancel₀ (mul_ne_zero ha hd), one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.vecMul, dotProduct]

end TernaryPeriodPolynomials.Argument.LatticeCounts.HeckeMatrix
