module

public import TernaryPeriodPolynomials.Building.RestrictedPresentation.Flat.Geometry

@[expose] public section

/-!
# Lemma 3.3: orientation characters of the flat and of the top cell

Proof of Lemma
`lem:apartment-boundary-pairing`: "The off-diagonal coordinates orient the cell, and the
two diagonal ratios orient the flat. A permutation has its permutation sign on the cell, while a
coordinate sign change has sign `+1`, exactly as in the top-cell model."

The signed permutations `g = (σ, s)`, `g e_j = s_j e_{σ j}` (`s_j = ±1`), the stabilizer of the
identity apartment, act by `R ↦ g R gᵀ` on the tangent space at the identity. The standard top cell
has tangent space the off-diagonal symmetric matrices, oriented by `(r₁₂, r₁₃, r₂₃)`
(`cellCoord`, `cellBasis`), and the flat the trace-zero diagonal matrices `diag(x₁, x₂, -x₁-x₂)`,
oriented by `(x₁, x₂)` (`flatCoord`, `flatBasis`). Both subspaces are invariant (`cell_action`,
`flat_action`), and the determinants of the actions are

* on the cell: `sgn σ` (`det_cellMatrix_eq_sign`), independent of the signs `s`;
* on the flat: `sgn σ` (`det_flatMatrix`).

Since the frame (cell, flat) is the normalization "local intersection number `+1`" at the identity,
the local intersection number of the flat with the oriented translate `g_* C` of the cell is
`det(C_g) = sgn σ`, and the total orientation of the 5-dimensional tangent space is preserved
(`cell_flat_frame_det`): the local intersections assemble with the permutation-sign character, as
in the top-cell model.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat

open Matrix

/-- The signed permutation matrix `g e_j = s_j e_{σ j}`. -/
def signedPerm (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ) : Mat3 :=
  Matrix.of fun i j => if i = σ j then s j else 0

/-- Coordinates `(r₁₂, r₁₃, r₂₃)` on the off-diagonal symmetric matrices (tangent space of the
standard top cell at the identity). -/
def cellCoord (R : Mat3) : Fin 3 → ℝ := ![R 0 1, R 0 2, R 1 2]

/-- The basis of the tangent space of the standard cell. -/
def cellBasis : Fin 3 → Mat3 :=
  ![Matrix.of fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0,
    Matrix.of fun i j => if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1 else 0,
    Matrix.of fun i j => if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1 else 0]

/-- The matrix, in the basis `cellBasis`, of `R ↦ g R gᵀ` on the cell tangent space. -/
def cellMatrix (g : Mat3) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun a b => cellCoord (g * cellBasis b * gᵀ) a

/-- Coordinates `(x₁, x₂)` on the trace-zero diagonal matrices `diag(x₁, x₂, -x₁-x₂)`. -/
def flatCoord (D : Mat3) : Fin 2 → ℝ := ![D 0 0, D 1 1]

def flatBasis : Fin 2 → Mat3 :=
  ![Matrix.diagonal ![1, 0, -1], Matrix.diagonal ![0, 1, -1]]

/-- The matrix of `D ↦ g D gᵀ` on the flat tangent space in the basis `flatBasis`. -/
def flatMatrix (g : Mat3) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun a b => flatCoord (g * flatBasis b * gᵀ) a

theorem perm_cases (σ : Equiv.Perm (Fin 3)) :
    σ = 1 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 0 2 ∨ σ = Equiv.swap 1 2 ∨
      σ = Equiv.swap 0 1 * Equiv.swap 1 2 ∨ σ = Equiv.swap 1 2 * Equiv.swap 0 1 := by
  revert σ; decide

theorem det_cellMatrix (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ) :
    (cellMatrix (signedPerm σ s)).det =
      (σ.sign : ℝ) * ((s 0 * s 1) * (s 0 * s 2) * (s 1 * s 2)) := by
  rcases perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | (simp [cellMatrix, cellCoord, cellBasis, signedPerm, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.det_fin_three, Matrix.transpose_apply, Equiv.swap_apply_def, 
        Equiv.Perm.sign_mul]; done)
    | (simp [cellMatrix, cellCoord, cellBasis, signedPerm, Matrix.mul_apply, Fin.sum_univ_three,
        Matrix.det_fin_three, Matrix.transpose_apply, Equiv.swap_apply_def, 
        Equiv.Perm.sign_mul]; ring)

/-- **The cell orientation character**: the signed permutation matrix `g = (σ, s)` acts on the
tangent space of the standard top cell (the off-diagonal symmetric matrices, oriented by the
coordinates `(r₁₂, r₁₃, r₂₃)`) with determinant `sgn σ`: the permutation sign, and `+1` on a
coordinate sign change. -/
theorem det_cellMatrix_eq_sign (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ)
    (hs : ∀ k, s k * s k = 1) : (cellMatrix (signedPerm σ s)).det = (σ.sign : ℝ) := by
  rw [det_cellMatrix]
  have : (s 0 * s 1) * (s 0 * s 2) * (s 1 * s 2) = (s 0 * s 0) * (s 1 * s 1) * (s 2 * s 2) := by
    ring
  rw [this, hs 0, hs 1, hs 2]
  ring

theorem det_flatMatrix (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ) (hs : ∀ k, s k * s k = 1) :
    (flatMatrix (signedPerm σ s)).det = (σ.sign : ℝ) := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  rcases perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [flatMatrix, flatCoord, flatBasis, signedPerm, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.det_fin_two, Matrix.transpose_apply, Equiv.swap_apply_def, Equiv.Perm.sign_mul] <;>
    nlinarith [h0, h1, h2]

/-- Entry formula for the conjugation action of a signed permutation matrix. -/
theorem signedPerm_conj_apply (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ) (R : Mat3) (i j : Fin 3) :
    (signedPerm σ s * R * (signedPerm σ s)ᵀ) i j =
      s (σ.symm i) * s (σ.symm j) * R (σ.symm i) (σ.symm j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, signedPerm, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ.symm j)]
  · rw [Finset.sum_eq_single (σ.symm i)]
    · simp
      ring
    · intro k _ hk
      have : i ≠ σ k := fun h => hk (by rw [h]; simp)
      simp [this]
    · simp
  · intro l _ hl
    have : j ≠ σ l := fun h => hl (by rw [h]; simp)
    simp [this]
  · simp

private theorem cell_action_one (s : Fin 3 → ℝ) (b : Fin 3) :
    signedPerm (1) s * cellBasis b * (signedPerm (1) s)ᵀ =
      ∑ a : Fin 3, cellMatrix (signedPerm (1) s) a b • cellBasis a := by
  ext i j
  rw [signedPerm_conj_apply]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [cellMatrix, cellCoord, cellBasis, signedPerm_conj_apply, Fin.sum_univ_three,
      Equiv.Perm.one_def] <;> ring

private theorem cell_action_s01 (s : Fin 3 → ℝ) (b : Fin 3) :
    signedPerm (Equiv.swap 0 1) s * cellBasis b * (signedPerm (Equiv.swap 0 1) s)ᵀ =
      ∑ a : Fin 3, cellMatrix (signedPerm (Equiv.swap 0 1) s) a b • cellBasis a := by
  ext i j
  rw [signedPerm_conj_apply]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [cellMatrix, cellCoord, cellBasis, signedPerm_conj_apply, Fin.sum_univ_three,
      Equiv.swap_apply_def, Equiv.symm_swap] <;> ring

private theorem cell_action_s02 (s : Fin 3 → ℝ) (b : Fin 3) :
    signedPerm (Equiv.swap 0 2) s * cellBasis b * (signedPerm (Equiv.swap 0 2) s)ᵀ =
      ∑ a : Fin 3, cellMatrix (signedPerm (Equiv.swap 0 2) s) a b • cellBasis a := by
  ext i j
  rw [signedPerm_conj_apply]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [cellMatrix, cellCoord, cellBasis, signedPerm_conj_apply, Fin.sum_univ_three,
      Equiv.swap_apply_def, Equiv.symm_swap] <;> ring

private theorem cell_action_s12 (s : Fin 3 → ℝ) (b : Fin 3) :
    signedPerm (Equiv.swap 1 2) s * cellBasis b * (signedPerm (Equiv.swap 1 2) s)ᵀ =
      ∑ a : Fin 3, cellMatrix (signedPerm (Equiv.swap 1 2) s) a b • cellBasis a := by
  ext i j
  rw [signedPerm_conj_apply]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [cellMatrix, cellCoord, cellBasis, signedPerm_conj_apply, Fin.sum_univ_three,
      Equiv.swap_apply_def, Equiv.symm_swap] <;> ring

private theorem cell_action_s01s12 (s : Fin 3 → ℝ) (b : Fin 3) :
    signedPerm (Equiv.swap 0 1 * Equiv.swap 1 2) s * cellBasis b * (signedPerm (Equiv.swap 0 1 * Equiv.swap 1 2) s)ᵀ =
      ∑ a : Fin 3, cellMatrix (signedPerm (Equiv.swap 0 1 * Equiv.swap 1 2) s) a b • cellBasis a := by
  ext i j
  rw [signedPerm_conj_apply]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [cellMatrix, cellCoord, cellBasis, signedPerm_conj_apply, Fin.sum_univ_three,
      Equiv.swap_apply_def, Equiv.Perm.mul_def, Equiv.symm_swap] <;> ring

private theorem cell_action_s12s01 (s : Fin 3 → ℝ) (b : Fin 3) :
    signedPerm (Equiv.swap 1 2 * Equiv.swap 0 1) s * cellBasis b * (signedPerm (Equiv.swap 1 2 * Equiv.swap 0 1) s)ᵀ =
      ∑ a : Fin 3, cellMatrix (signedPerm (Equiv.swap 1 2 * Equiv.swap 0 1) s) a b • cellBasis a := by
  ext i j
  rw [signedPerm_conj_apply]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [cellMatrix, cellCoord, cellBasis, signedPerm_conj_apply, Fin.sum_univ_three,
      Equiv.swap_apply_def, Equiv.Perm.mul_def, Equiv.symm_swap] <;> ring

/-- The cell tangent space is invariant under `g`, and `cellMatrix g` is the matrix of the
action. -/
theorem cell_action (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ) (b : Fin 3) :
    signedPerm σ s * cellBasis b * (signedPerm σ s)ᵀ =
      ∑ a : Fin 3, cellMatrix (signedPerm σ s) a b • cellBasis a := by
  rcases perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact cell_action_one s b
  · exact cell_action_s01 s b
  · exact cell_action_s02 s b
  · exact cell_action_s12 s b
  · exact cell_action_s01s12 s b
  · exact cell_action_s12s01 s b

private theorem flat_action_one (s : Fin 3 → ℝ) (hs : ∀ k, s k * s k = 1) (b : Fin 2) :
    signedPerm (1) s * flatBasis b * (signedPerm (1) s)ᵀ =
      ∑ a : Fin 2, flatMatrix (signedPerm (1) s) a b • flatBasis a := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  ext i j
  rw [signedPerm_conj_apply]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [flatMatrix, flatCoord, flatBasis, signedPerm_conj_apply, Fin.sum_univ_two,
      Equiv.Perm.one_def] <;>
    nlinarith [h0, h1, h2]

private theorem flat_action_s01 (s : Fin 3 → ℝ) (hs : ∀ k, s k * s k = 1) (b : Fin 2) :
    signedPerm (Equiv.swap 0 1) s * flatBasis b * (signedPerm (Equiv.swap 0 1) s)ᵀ =
      ∑ a : Fin 2, flatMatrix (signedPerm (Equiv.swap 0 1) s) a b • flatBasis a := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  ext i j
  rw [signedPerm_conj_apply]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [flatMatrix, flatCoord, flatBasis, signedPerm_conj_apply, Fin.sum_univ_two,
      Equiv.swap_apply_def, Equiv.symm_swap] <;>
    nlinarith [h0, h1, h2]

private theorem flat_action_s02 (s : Fin 3 → ℝ) (hs : ∀ k, s k * s k = 1) (b : Fin 2) :
    signedPerm (Equiv.swap 0 2) s * flatBasis b * (signedPerm (Equiv.swap 0 2) s)ᵀ =
      ∑ a : Fin 2, flatMatrix (signedPerm (Equiv.swap 0 2) s) a b • flatBasis a := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  ext i j
  rw [signedPerm_conj_apply]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [flatMatrix, flatCoord, flatBasis, signedPerm_conj_apply, Fin.sum_univ_two,
      Equiv.swap_apply_def, Equiv.symm_swap] <;>
    nlinarith [h0, h1, h2]

private theorem flat_action_s12 (s : Fin 3 → ℝ) (hs : ∀ k, s k * s k = 1) (b : Fin 2) :
    signedPerm (Equiv.swap 1 2) s * flatBasis b * (signedPerm (Equiv.swap 1 2) s)ᵀ =
      ∑ a : Fin 2, flatMatrix (signedPerm (Equiv.swap 1 2) s) a b • flatBasis a := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  ext i j
  rw [signedPerm_conj_apply]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [flatMatrix, flatCoord, flatBasis, signedPerm_conj_apply, Fin.sum_univ_two,
      Equiv.swap_apply_def, Equiv.symm_swap] <;>
    nlinarith [h0, h1, h2]

private theorem flat_action_s01s12 (s : Fin 3 → ℝ) (hs : ∀ k, s k * s k = 1) (b : Fin 2) :
    signedPerm (Equiv.swap 0 1 * Equiv.swap 1 2) s * flatBasis b * (signedPerm (Equiv.swap 0 1 * Equiv.swap 1 2) s)ᵀ =
      ∑ a : Fin 2, flatMatrix (signedPerm (Equiv.swap 0 1 * Equiv.swap 1 2) s) a b • flatBasis a := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  ext i j
  rw [signedPerm_conj_apply]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [flatMatrix, flatCoord, flatBasis, signedPerm_conj_apply, Fin.sum_univ_two,
      Equiv.swap_apply_def, Equiv.Perm.mul_def, Equiv.symm_swap] <;>
    nlinarith [h0, h1, h2]

private theorem flat_action_s12s01 (s : Fin 3 → ℝ) (hs : ∀ k, s k * s k = 1) (b : Fin 2) :
    signedPerm (Equiv.swap 1 2 * Equiv.swap 0 1) s * flatBasis b * (signedPerm (Equiv.swap 1 2 * Equiv.swap 0 1) s)ᵀ =
      ∑ a : Fin 2, flatMatrix (signedPerm (Equiv.swap 1 2 * Equiv.swap 0 1) s) a b • flatBasis a := by
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  ext i j
  rw [signedPerm_conj_apply]
  fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [flatMatrix, flatCoord, flatBasis, signedPerm_conj_apply, Fin.sum_univ_two,
      Equiv.swap_apply_def, Equiv.Perm.mul_def, Equiv.symm_swap] <;>
    nlinarith [h0, h1, h2]

/-- The flat tangent space is invariant under `g`, and `flatMatrix g` is the matrix of the action
(`s_k² = 1`: sign changes act trivially on diagonal matrices). -/
theorem flat_action (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ) (hs : ∀ k, s k * s k = 1)
    (b : Fin 2) :
    signedPerm σ s * flatBasis b * (signedPerm σ s)ᵀ =
      ∑ a : Fin 2, flatMatrix (signedPerm σ s) a b • flatBasis a := by
  rcases perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact flat_action_one s hs b
  · exact flat_action_s01 s hs b
  · exact flat_action_s02 s hs b
  · exact flat_action_s12 s hs b
  · exact flat_action_s01s12 s hs b
  · exact flat_action_s12s01 s hs b

/-- The matrix of the action on the oriented 5-dimensional tangent space (cell frame, then flat
frame) is block diagonal with determinant `sgn σ · sgn σ = 1`: the translates preserve the total
orientation, so the intersection sign is carried by the cell alone. -/
theorem cell_flat_frame_det (σ : Equiv.Perm (Fin 3)) (s : Fin 3 → ℝ) (hs : ∀ k, s k * s k = 1) :
    (cellMatrix (signedPerm σ s)).det * (flatMatrix (signedPerm σ s)).det = 1 := by
  rw [det_cellMatrix_eq_sign σ s hs, det_flatMatrix σ s hs]
  rcases Int.units_eq_one_or σ.sign with h | h <;> simp [h]

end TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat
