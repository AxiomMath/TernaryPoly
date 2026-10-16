module

public import Mathlib

@[expose] public section


open Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FaceDescent

variable {R : Type} [CommRing R]

/-- Index type of the coordinates `(t11, t12, t22 | w0, w1 | s)` on symmetric `3 × 3` matrices. -/
abbrev SymIdx := Fin 3 ⊕ (Fin 2 ⊕ Fin 1)

/-- The symmetric matrix `[[s, wᵗ],[w, T]]` with `T = [[t11, t12],[t12, t22]]`. -/
def symMat (x : SymIdx → R) : Matrix (Fin 3) (Fin 3) R :=
  !![x (Sum.inr (Sum.inr 0)), x (Sum.inr (Sum.inl 0)), x (Sum.inr (Sum.inl 1));
     x (Sum.inr (Sum.inl 0)), x (Sum.inl 0), x (Sum.inl 1);
     x (Sum.inr (Sum.inl 1)), x (Sum.inl 1), x (Sum.inl 2)]

/-- The block-upper-triangular element `[[a, v],[0, A]]` of the line stabilizer. -/
def lineElt (a : R) (v : Fin 2 → R) (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  !![a, v 0, v 1; 0, A 0 0, A 0 1; 0, A 1 0, A 1 1]

/-- The action `T ↦ A T Aᵗ` on `(t11, t12, t22)`. -/
def sym2Act (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  !![A 0 0 * A 0 0, 2 * (A 0 0 * A 0 1), A 0 1 * A 0 1;
     A 0 0 * A 1 0, A 0 0 * A 1 1 + A 0 1 * A 1 0, A 0 1 * A 1 1;
     A 1 0 * A 1 0, 2 * (A 1 0 * A 1 1), A 1 1 * A 1 1]

theorem det_sym2Act (A : Matrix (Fin 2) (Fin 2) R) : (sym2Act A).det = A.det ^ 3 := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp only [sym2Act, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]
  ring

/-- The matrix of `x ↦ g x gᵗ` for `g = [[a, v],[0, A]]` in the coordinates `SymIdx`: block lower triangular for the filtration `T`, `w`, `s`. -/
def lineActMat (a : R) (v : Fin 2 → R) (A : Matrix (Fin 2) (Fin 2) R) : Matrix SymIdx SymIdx R :=
  Matrix.fromBlocks (sym2Act A) 0
    (Matrix.fromRows (Matrix.of fun (i : Fin 2) (j : Fin 3) => ![A i 0 * v 0, A i 0 * v 1 + A i 1 * v 0, A i 1 * v 1] j)
      (Matrix.of fun (_ : Fin 1) (j : Fin 3) => ![v 0 * v 0, 2 * (v 0 * v 1), v 1 * v 1] j))
    (Matrix.fromBlocks (a • A) 0 (Matrix.of fun (_ : Fin 1) (j : Fin 2) => ![2 * a * v 0, 2 * a * v 1] j)
      (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => a * a))

theorem lineActMat_spec (a : R) (v : Fin 2 → R) (A : Matrix (Fin 2) (Fin 2) R) (x : SymIdx → R) :
    symMat (lineActMat a v A *ᵥ x) = lineElt a v A * symMat x * (lineElt a v A)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symMat, lineElt, lineActMat, sym2Act, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_succ, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem det_lineActMat (a : R) (v : Fin 2 → R) (A : Matrix (Fin 2) (Fin 2) R) :
    (lineActMat a v A).det = A.det ^ 3 * ((a ^ 2 * A.det) * a ^ 2) := by
  unfold lineActMat
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₁₂, det_sym2Act, Matrix.det_smul]
  simp [Matrix.det_unique]
  ring

/-- Index type of the plane coordinates `(s | w0, w1 | t11, t12, t22)`. -/
abbrev SymIdxP := Fin 1 ⊕ (Fin 2 ⊕ Fin 3)

/-- The symmetric matrix `[[T, w],[wᵗ, s]]` adapted to the flag `(2,1)`. -/
def symMatP (x : SymIdxP → R) : Matrix (Fin 3) (Fin 3) R :=
  !![x (Sum.inr (Sum.inr 0)), x (Sum.inr (Sum.inr 1)), x (Sum.inr (Sum.inl 0));
     x (Sum.inr (Sum.inr 1)), x (Sum.inr (Sum.inr 2)), x (Sum.inr (Sum.inl 1));
     x (Sum.inr (Sum.inl 0)), x (Sum.inr (Sum.inl 1)), x (Sum.inl 0)]

/-- The block-upper-triangular element `[[A, v],[0, a]]` of the plane stabilizer. -/
def planeElt (a : R) (v : Fin 2 → R) (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 3) (Fin 3) R :=
  !![A 0 0, A 0 1, v 0; A 1 0, A 1 1, v 1; 0, 0, a]

/-- The matrix of `x ↦ g x gᵗ` for `g = [[A, v],[0, a]]` in the coordinates `SymIdxP`: block lower triangular for the filtration `s`, `w`, `T`. -/
def planeActMat (a : R) (v : Fin 2 → R) (A : Matrix (Fin 2) (Fin 2) R) : Matrix SymIdxP SymIdxP R :=
  Matrix.fromBlocks (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => a * a) 0
    (Matrix.fromRows (Matrix.of fun (i : Fin 2) (_ : Fin 1) => a * v i)
      (Matrix.of fun (j : Fin 3) (_ : Fin 1) => ![v 0 * v 0, v 0 * v 1, v 1 * v 1] j))
    (Matrix.fromBlocks (a • A) 0 (Matrix.of fun (i : Fin 3) (j : Fin 2) =>
      ![![2 * v 0 * A 0 0, 2 * v 0 * A 0 1], ![v 1 * A 0 0 + v 0 * A 1 0, v 1 * A 0 1 + v 0 * A 1 1],
        ![2 * v 1 * A 1 0, 2 * v 1 * A 1 1]] i j) (sym2Act A))

theorem planeActMat_spec (a : R) (v : Fin 2 → R) (A : Matrix (Fin 2) (Fin 2) R) (x : SymIdxP → R) :
    symMatP (planeActMat a v A *ᵥ x) = planeElt a v A * symMatP x * (planeElt a v A)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symMatP, planeElt, planeActMat, sym2Act, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_succ, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem det_planeActMat (a : R) (v : Fin 2 → R) (A : Matrix (Fin 2) (Fin 2) R) :
    (planeActMat a v A).det = (a * a) * ((a ^ 2 * A.det) * A.det ^ 3) := by
  unfold planeActMat
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₁₂, det_sym2Act, Matrix.det_smul]
  simp [Matrix.det_unique]

end TernaryPeriodPolynomials.Argument.FaceDescent
