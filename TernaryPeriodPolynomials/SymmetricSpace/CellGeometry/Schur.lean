module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Cells.WellRounded
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section


/-!
# Appendix B cell calculation: positive definiteness of `G(w,C)` through the Schur complement

Formalized by Claude Sonnet 5.5.  Paper: "Thus the Schur complement is positive."

* `posDef_fromBlocks_of_schur`: the strict Schur criterion for Mathlib's `Matrix.PosDef` (Mathlib has only the semidefinite version
  `Matrix.PosDef.fromBlocks₂₂`): `fromBlocks A B Bᴴ D` is positive definite when `D` and `A - B D⁻¹ Bᴴ` are.
* `Gblock w C`: `G(w,C) = [[1 + wᵗCw - δ², (Cw)ᵗ],[Cw, C]]` as a block matrix indexed by `Fin 1 ⊕ Fin 2`; `Gmat_eq_submatrix` identifies it with the library's `Gmat`.
* `schurComplement_Gblock`: the Schur complement of `C` in `G(w,C)` is the `1 × 1` matrix `1 - δ_C(w)²` (literally `A - B C⁻¹ Bᴴ`).
* `deltaSq_BinWR_le`: `δ_C(w)² ≤ 1/2` for every minimum-one well-rounded binary `C` (covering radius, via `C = DᵗC(t)D`), hence the Schur complement is `≥ 1/2`.
* `Gmat_matrixPosDef`: `Matrix.PosDef (Gmat w C)` for every `BinWR C`, proved from the Schur complement.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixBCellGeometry

open TernaryPeriodPolynomials.Argument.AppendixBResidue.Geometry Matrix

section Schur

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
/-- **Strict Schur criterion.** If `D` is positive definite and the Schur complement `A - B D⁻¹ Bᴴ` is positive definite, so is `fromBlocks A B Bᴴ D`. -/
theorem posDef_fromBlocks_of_schur (A : Matrix m m ℝ) (B : Matrix m n ℝ) {D : Matrix n n ℝ} (hD : D.PosDef)
    (hS : (A - B * D⁻¹ * Bᴴ).PosDef) : (fromBlocks A B Bᴴ D).PosDef := by
  have : Invertible D := Matrix.invertibleOfIsUnitDet D ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit)
  have hDh := hD.isHermitian
  have hSh := hS.isHermitian
  obtain ⟨-, hD2⟩ := Matrix.posDef_iff_dotProduct_mulVec.mp hD
  obtain ⟨-, hS2⟩ := Matrix.posDef_iff_dotProduct_mulVec.mp hS
  obtain ⟨-, hD3⟩ := Matrix.posSemidef_iff_dotProduct_mulVec.mp hD.posSemidef
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨(Matrix.IsHermitian.fromBlocks₂₂ A B hDh).mpr hSh, fun x hx => ?_⟩
  have hx' : x = (x ∘ Sum.inl) ⊕ᵥ (x ∘ Sum.inr) := (Sum.elim_comp_inl_inr x).symm
  rw [dotProduct_mulVec, hx', schur_complement_eq₂₂ A B (x ∘ Sum.inl) (x ∘ Sum.inr) hDh]
  rw [← dotProduct_mulVec, ← dotProduct_mulVec]
  by_cases h1 : (x ∘ Sum.inl) = 0
  · have h2 : (x ∘ Sum.inr) ≠ 0 := by
      intro h2
      apply hx
      rw [hx', h1, h2]
      funext i
      cases i <;> rfl
    rw [h1, Matrix.mulVec_zero, zero_add]
    have := hD2 h2
    simpa using this
  · have := hS2 h1
    have h4 := hD3 ((D⁻¹ * Bᴴ) *ᵥ (x ∘ Sum.inl) + (x ∘ Sum.inr))
    linarith

end Schur

/-- `G(w,C) = [[1 + wᵗCw - δ_C(w)², (Cw)ᵗ],[Cw, C]]` as a block matrix on `Fin 1 ⊕ Fin 2`. -/
def Gblock (w : Vec2) (C : Mat2) : Matrix (Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 2) ℝ :=
  fromBlocks (Matrix.of fun _ _ => 1 + quad C w - deltaSq C w) (Matrix.of fun _ j => (C *ᵥ w) j)
    (Matrix.of fun _ j => (C *ᵥ w) j)ᴴ C

theorem Gmat_eq_submatrix (w : Vec2) (C : Mat2) :
    Gmat w C = (Gblock w C).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gblock, Gmat, Matrix.fromBlocks, finSumFinEquiv, Fin.addCases]

theorem posDefQ_iff_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : PosDefQ A ↔ A.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  unfold PosDefQ
  simp only [star_trivial, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- A minimum-one well-rounded binary form is positive definite in Mathlib's sense. -/
theorem BinWR_posDef {C : Mat2} (hC : BinWR C) : C.PosDef := by
  rw [← posDefQ_iff_posDef]
  exact ⟨hC.1, fun v hv => hC.2.1 v hv⟩

/-- **Covering radius for every minimum-one well-rounded binary form**: `δ_C(w)² ≤ 1/2` (via `C = DᵗC(t)D`, `deltaSq_conj`). -/
theorem deltaSq_BinWR_le {C : Mat2} (hC : BinWR C) (w : Vec2) : deltaSq C w ≤ 1 / 2 := by
  obtain ⟨t, ht, D, D', h1, h2, rfl⟩ := BinWR_reduce hC
  have hw : castMat D *ᵥ w = intVec (0 : Fin 2 → ℤ) + ((1 : ℤ) : ℝ) • (castMat D *ᵥ w) := by
    funext i; simp [intVec]
  rw [deltaSq_conj (Ct t) D D' h1 h2 0 1 (Or.inl rfl) (castMat D *ᵥ w) w hw]
  refine le_trans (deltaSq_Ct_le ht _) ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [abs_nonneg t]

/-- The Schur complement of `C` in `G(w,C)`: `A - B C⁻¹ Bᴴ` is the `1 × 1` matrix `1 - δ_C(w)²`. -/
theorem schurComplement_Gblock {C : Mat2} (hC : BinWR C) (w : Vec2) :
    (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => 1 + quad C w - deltaSq C w) -
        (Matrix.of fun (_ : Fin 1) (j : Fin 2) => (C *ᵥ w) j) * C⁻¹ *
          (Matrix.of fun (_ : Fin 1) (j : Fin 2) => (C *ᵥ w) j)ᴴ =
      Matrix.of fun (_ : Fin 1) (_ : Fin 1) => 1 - deltaSq C w := by
  have hdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp (BinWR_posDef hC).isUnit
  have hinv : C⁻¹ *ᵥ (C *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hk : ∀ k, ∑ l, C⁻¹ k l * (C *ᵥ w) l = w k := fun k => by
    have := congrFun hinv k
    simpa [Matrix.mulVec, dotProduct] using this
  ext i j
  fin_cases i; fin_cases j
  have e0 := hk 0
  have e1 := hk 1
  simp only [Fin.sum_univ_two] at e0 e1
  have hq : quad C w = (C *ᵥ w) 0 * w 0 + (C *ᵥ w) 1 * w 1 := by
    simp [quad, dotProduct, Fin.sum_univ_two]
    ring
  simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Fin.sum_univ_two]
  linear_combination hq - (C *ᵥ w) 0 * e0 - (C *ᵥ w) 1 * e1

/-- The Schur complement `1 - δ_C(w)²` is at least `1/2`, in particular positive. -/
theorem schur_pos {C : Mat2} (hC : BinWR C) (w : Vec2) : 1 / 2 ≤ 1 - deltaSq C w := by
  linarith [deltaSq_BinWR_le hC w]

/-- **`G(w,C)` is positive definite (Mathlib's `Matrix.PosDef`), by the Schur complement**. -/
theorem Gmat_matrixPosDef {C : Mat2} (hC : BinWR C) (w : Vec2) : (Gmat w C).PosDef := by
  have hCp := BinWR_posDef hC
  have hS : ((Matrix.of fun (_ : Fin 1) (_ : Fin 1) => 1 + quad C w - deltaSq C w) -
        (Matrix.of fun (_ : Fin 1) (j : Fin 2) => (C *ᵥ w) j) * C⁻¹ *
          (Matrix.of fun (_ : Fin 1) (j : Fin 2) => (C *ᵥ w) j)ᴴ).PosDef := by
    rw [schurComplement_Gblock hC w, Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j; simp [Matrix.conjTranspose_apply]
    · have h0 : x 0 ≠ 0 := fun h => hx (by funext i; fin_cases i; exact h)
      have := schur_pos hC w
      simp [dotProduct, Matrix.mulVec]
      nlinarith [mul_self_pos.mpr h0]
  rw [Gmat_eq_submatrix]
  exact (posDef_fromBlocks_of_schur _ _ hCp hS).submatrix finSumFinEquiv.symm.injective

end TernaryPeriodPolynomials.Argument.AppendixBCellGeometry
