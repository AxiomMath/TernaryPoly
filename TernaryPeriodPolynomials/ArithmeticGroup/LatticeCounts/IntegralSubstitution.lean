module

public import Mathlib

@[expose] public section


/-!
# The integral substitution matrix for a primitive pair

Formalized by Claude Haiku 5.5.

Formulation. `K = ℚ_[p]` (`Padic p`). `p`-integrality of `x ∈ K` is `‖x‖ ≤ 1`.
`Λ_{s,t} ⊆ K²` is `latSubst s t = {(u,v) | ‖u‖ ≤ 1, ‖v‖ ≤ 1, ‖s u + t v‖ ≤ 1}`.
The matrix `L(s,t) = [[0,1,0],[0,0,1],[1,s,t]]` is `substL s t`.
For a `2 × 2` matrix `A` with columns `(u_j, v_j) = (A 0 j, A 1 j)`, `substK s t A w₀ x y` has
first column `(-(s u_0 + t v_0), u_0, v_0)`, second column `(-(s u_1 + t v_1), u_1, v_1)`, and
third column `(w₀, x, y)`.

The basis hypothesis of the paper is replaced by "columns of `A` lie in `Λ_{s,t}` and
`det A = p^r`". This is stronger: a basis of `Λ_{s,t}` with determinant `p^r` satisfies it.
Integrality of the third column is `‖w₀‖, ‖x‖, ‖y‖ ≤ 1`, and the Bézout normalisation is
`w₀ + s x + t y = (p^r)⁻¹`. The lemmas hold for every `r`, in particular for `r ≥ 1`.
-/

namespace TernaryPeriodPolynomials.Argument.LatticeCounts

variable {p : ℕ} [hp : Fact p.Prime]

/-- `Λ_{s,t} ⊆ ℚ_p²`: pairs `(u, v)` of `p`-integers with `s u + t v` a `p`-integer. -/
def latSubst (s t : Padic p) : Set (Padic p × Padic p) :=
  {w | ‖w.1‖ ≤ 1 ∧ ‖w.2‖ ≤ 1 ∧ ‖s * w.1 + t * w.2‖ ≤ 1}

/-- The matrix `L(s,t) = [[0,1,0],[0,0,1],[1,s,t]]`. -/
noncomputable def substL (s t : Padic p) : Matrix (Fin 3) (Fin 3) (Padic p) :=
  !![0, 1, 0; 0, 0, 1; 1, s, t]

/-- The matrix `k₀` with columns `(-(s u_j + t v_j), u_j, v_j)` for `j = 0, 1` (where
`(u_j, v_j) = (A 0 j, A 1 j)`) and third column `(w₀, x, y)`. -/
noncomputable def substK (s t : Padic p) (A : Matrix (Fin 2) (Fin 2) (Padic p)) (w₀ x y : Padic p) :
    Matrix (Fin 3) (Fin 3) (Padic p) :=
  !![-(s * A 0 0 + t * A 1 0), -(s * A 0 1 + t * A 1 1), w₀;
     A 0 0, A 0 1, x;
     A 1 0, A 1 1, y]

theorem padic_p_pow_ne_zero (r : ℕ) : (p : Padic p) ^ r ≠ 0 :=
  pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)

theorem norm_p_pow_nat (r : ℕ) : ‖(p : Padic p) ^ r‖ = ((p : ℝ) ^ r)⁻¹ := by
  rw [Padic.norm_p_pow, zpow_neg, zpow_natCast]

/-- Bézout step: if `max(‖s‖, ‖t‖) = p^r`, there are `p`-integers `w₀, x, y` with
`w₀ + s x + t y = p^{-r}`. -/
theorem exists_bezout_of_max {s t : Padic p} {r : ℕ}
    (hmax : max ‖s‖ ‖t‖ = (p : ℝ) ^ r) :
    ∃ w₀ x y : Padic p, ‖w₀‖ ≤ 1 ∧ ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1 ∧
      w₀ + s * x + t * y = ((p : Padic p) ^ r)⁻¹ := by
  have hpR : (p : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hpK : (p : Padic p) ^ r ≠ 0 := padic_p_pow_ne_zero r
  rcases max_choice ‖s‖ ‖t‖ with h | h
  · -- `‖s‖ = p^r`: take `x = (p^r s)⁻¹`, `w₀ = y = 0`.
    rw [hmax] at h
    have hs0 : s ≠ 0 := by
      intro h0
      apply hpR
      rw [h, h0, norm_zero]
    refine ⟨0, ((p : Padic p) ^ r * s)⁻¹, 0, by simp, ?_, by simp, ?_⟩
    · rw [norm_inv, norm_mul, norm_p_pow_nat, ← h, inv_mul_cancel₀ hpR]
      exact le_of_eq inv_one
    · field_simp
      ring
  · -- `‖t‖ = p^r`: take `y = (p^r t)⁻¹`, `w₀ = x = 0`.
    rw [hmax] at h
    have ht0 : t ≠ 0 := by
      intro h0
      apply hpR
      rw [h, h0, norm_zero]
    refine ⟨0, 0, ((p : Padic p) ^ r * t)⁻¹, by simp, by simp, ?_, ?_⟩
    · rw [norm_inv, norm_mul, norm_p_pow_nat, ← h, inv_mul_cancel₀ hpR]
      exact le_of_eq inv_one
    · field_simp
      ring

/-- `p`-integrality of `k₀` when the columns of `A` lie in `Λ_{s,t}` and the third column is
`p`-integral. -/
theorem substK_integral {s t : Padic p} {A : Matrix (Fin 2) (Fin 2) (Padic p)} {w₀ x y : Padic p}
    (hA : ∀ j : Fin 2, (A 0 j, A 1 j) ∈ latSubst s t)
    (hw₀ : ‖w₀‖ ≤ 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ∀ i j : Fin 3, ‖substK s t A w₀ x y i j‖ ≤ 1 := by
  have h0 : ‖A 0 0‖ ≤ 1 ∧ ‖A 1 0‖ ≤ 1 ∧ ‖s * A 0 0 + t * A 1 0‖ ≤ 1 := hA 0
  have h1 : ‖A 0 1‖ ≤ 1 ∧ ‖A 1 1‖ ≤ 1 ∧ ‖s * A 0 1 + t * A 1 1‖ ≤ 1 := hA 1
  obtain ⟨a0, b0, c0⟩ := h0
  obtain ⟨a1, b1, c1⟩ := h1
  have e00 : ‖-(s * A 0 0 + t * A 1 0)‖ ≤ 1 := by rw [norm_neg]; exact c0
  have e01 : ‖-(s * A 0 1 + t * A 1 1)‖ ≤ 1 := by rw [norm_neg]; exact c1
  intro i j
  fin_cases i <;> fin_cases j <;>
    first
    | exact e00 | exact e01 | exact hw₀ | exact a0 | exact b0 | exact a1 | exact b1
    | exact hx | exact hy

/-- Determinant of `k₀`: `det k₀ = det A · (w₀ + s x + t y)`, as a polynomial identity. -/
theorem substK_det (s t : Padic p) (A : Matrix (Fin 2) (Fin 2) (Padic p)) (w₀ x y : Padic p) :
    (substK s t A w₀ x y).det = A.det * (w₀ + s * x + t * y) := by
  rw [Matrix.det_fin_three, Matrix.det_fin_two]
  simp [substK]
  ring

/-- `L(s,t) k₀ = [[A, (x,y)^T], [0, 0, p^{-r}]]` when `w₀ + s x + t y = p^{-r}`. -/
theorem substL_mul_substK (s t : Padic p) (A : Matrix (Fin 2) (Fin 2) (Padic p))
    (w₀ x y : Padic p) (r : ℕ) (hsum : w₀ + s * x + t * y = ((p : Padic p) ^ r)⁻¹) :
    substL s t * substK s t A w₀ x y =
      !![A 0 0, A 0 1, x; A 1 0, A 1 1, y; 0, 0, ((p : Padic p) ^ r)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [substL, substK, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals first
    | linear_combination hsum

/-- The substitution matrix for a primitive pair. Given `A` with columns in `Λ_{s,t}`,
`det A = p^r`, and a third column `(w₀, x, y)` that is `p`-integral with
`w₀ + s x + t y = p^{-r}`, the matrix `k₀` is `p`-integral, has determinant `1`, and
`L(s,t) k₀ = [[A, (x,y)^T], [0, 0, p^{-r}]]`. -/
theorem substitution_matrix {s t : Padic p} {r : ℕ} {A : Matrix (Fin 2) (Fin 2) (Padic p)}
    (hA : ∀ j : Fin 2, (A 0 j, A 1 j) ∈ latSubst s t)
    (hdet : A.det = (p : Padic p) ^ r)
    {w₀ x y : Padic p} (hw₀ : ‖w₀‖ ≤ 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (hsum : w₀ + s * x + t * y = ((p : Padic p) ^ r)⁻¹) :
    (∀ i j : Fin 3, ‖substK s t A w₀ x y i j‖ ≤ 1) ∧
    (substK s t A w₀ x y).det = 1 ∧
    substL s t * substK s t A w₀ x y =
      !![A 0 0, A 0 1, x; A 1 0, A 1 1, y; 0, 0, ((p : Padic p) ^ r)⁻¹] := by
  refine ⟨substK_integral hA hw₀ hx hy, ?_, substL_mul_substK s t A w₀ x y r hsum⟩
  rw [substK_det, hdet, hsum, mul_inv_cancel₀ (padic_p_pow_ne_zero r)]

/-- Existence form: for `max(‖s‖,‖t‖) = p^r` and `A` as above, a third column exists making
`k₀` integral with `det k₀ = 1` and `L(s,t) k₀` of the stated block shape. -/
theorem exists_substitution_matrix {s t : Padic p} {r : ℕ} {A : Matrix (Fin 2) (Fin 2) (Padic p)}
    (hA : ∀ j : Fin 2, (A 0 j, A 1 j) ∈ latSubst s t)
    (hdet : A.det = (p : Padic p) ^ r)
    (hmax : max ‖s‖ ‖t‖ = (p : ℝ) ^ r) :
    ∃ w₀ x y : Padic p, (∀ i j : Fin 3, ‖substK s t A w₀ x y i j‖ ≤ 1) ∧
      (substK s t A w₀ x y).det = 1 ∧
      substL s t * substK s t A w₀ x y =
        !![A 0 0, A 0 1, x; A 1 0, A 1 1, y; 0, 0, ((p : Padic p) ^ r)⁻¹] := by
  obtain ⟨w₀, x, y, hw₀, hx, hy, hsum⟩ := exists_bezout_of_max (s := s) (t := t) hmax
  exact ⟨w₀, x, y, substitution_matrix hA hdet hw₀ hx hy hsum⟩

end TernaryPeriodPolynomials.Argument.LatticeCounts
