module

public import Mathlib

@[expose] public section


/-!
# Lemma 3.3: the local geometry of the diagonal flat

Proof of Lemma
`lem:apartment-boundary-pairing` (`eq:apartment-boundary-diagram`): "The diagonal flat
meets this cell at the identity, transversely. It meets no other open top cell: a diagonal form is
well rounded only when all three diagonal entries agree, and at that form the shortest primitive
vectors are precisely `±e_i`."

The library's chain model (`Exports/AppendixLemmas.lean`) replaces the geometric flat by the
relative apartment class; the following statements formalize the geometric facts of the paper's
calculation, for the determinant-one diagonal forms `diag(a, b, c)`, `abc = 1` (`OnFlat`) and the
top cell `TopCellOf u` of an integral basis `u` (forms of minimum one attained on `u₁, u₂, u₃`,
the unit-diagonal cell `Tcell` of the standard basis):

* `flat_cell_eq_identity`, `flat_meets_cells_iff`: the flat meets the top cell of any basis only at
  the identity, so it meets the union of all top cells exactly at the identity form;
* `identity_minimal_vectors`: the shortest nonzero integral vectors of the identity form are
  exactly `±e_k`; `identity_mem_standard_cell`: the identity lies in the standard cell;
* `flat_cell_transverse`: at the identity the tangent spaces of the flat (trace-zero diagonal
  matrices, `dim 2`) and of the standard cell (off-diagonal symmetric matrices `r₁₂, r₁₃, r₂₃`,
  `dim 3`) are complementary in the tangent space (symmetric, trace zero) of the symmetric space
  of determinant-one forms; this is the transversality of the intersection.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat

open Matrix

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

/-- The real vector underlying an integral vector. -/
def castVec (v : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => (v i : ℝ)

/-- The quadratic form `v ↦ vᵗ A v`. -/
def qf (A : Mat3) (v : Fin 3 → ℝ) : ℝ := v ⬝ᵥ (A *ᵥ v)

/-- The diagonal form `diag(a, b, c)`. -/
def diagForm (a b c : ℝ) : Mat3 := Matrix.diagonal ![a, b, c]

theorem qf_diag (a b c : ℝ) (v : Fin 3 → ℝ) :
    qf (diagForm a b c) v = a * v 0 ^ 2 + b * v 1 ^ 2 + c * v 2 ^ 2 := by
  simp [qf, diagForm, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- The determinant-one diagonal forms `diag(a, b, (ab)⁻¹)`, `a, b > 0`, i.e. the flat. -/
def OnFlat (a b c : ℝ) : Prop := 0 < a ∧ 0 < b ∧ 0 < c ∧ a * b * c = 1

/-- The (closed) top cell of the well-rounded retract attached to an integral basis `u`: the
forms of minimum one that attain it on the basis vectors `u₁, u₂, u₃`. -/
def TopCellOf (u : Fin 3 → Fin 3 → ℤ) : Set Mat3 :=
  {A | (∀ i, qf A (castVec (u i)) = 1) ∧ ∀ v : Fin 3 → ℤ, v ≠ 0 → 1 ≤ qf A (castVec v)}

/-- **The flat meets a top cell only at the identity.** If a determinant-one diagonal form
`diag(a, b, c)` lies in the top cell of an integral basis `u` (it has minimum one, attained on
`u₁, u₂, u₃`), then it is the identity. (A diagonal form is well rounded only when its three
diagonal entries agree.) -/
theorem flat_cell_eq_identity {a b c : ℝ} (u : Fin 3 → Fin 3 → ℤ)
    (hdet : (Matrix.of u).det = 1 ∨ (Matrix.of u).det = -1)
    (hA : diagForm a b c ∈ TopCellOf u) : a = 1 ∧ b = 1 ∧ c = 1 := by
  obtain ⟨hu, hmin⟩ := hA
  have hdet0 : (Matrix.of u).det ≠ 0 := by rcases hdet with h | h <;> simp [h]
  have ea : (1 : ℝ) ≤ a := by
    have := hmin ![1, 0, 0] (by simp)
    simpa [qf_diag, castVec] using this
  have eb : (1 : ℝ) ≤ b := by
    have := hmin ![0, 1, 0] (by simp)
    simpa [qf_diag, castVec] using this
  have ec : (1 : ℝ) ≤ c := by
    have := hmin ![0, 0, 1] (by simp)
    simpa [qf_diag, castVec] using this
  -- every basis vector forces the entries on its support to be one
  have key : ∀ i j, u i j ≠ 0 → ![a, b, c] j = 1 := by
    intro i j hij
    have hne : u i ≠ 0 := by
      intro h0
      apply hdet0
      apply Matrix.det_eq_zero_of_row_eq_zero i
      intro k
      simp [h0]
    have hq := hu i
    rw [qf_diag] at hq
    set x0 : ℝ := castVec (u i) 0 ^ 2 with hx0
    set x1 : ℝ := castVec (u i) 1 ^ 2 with hx1
    set x2 : ℝ := castVec (u i) 2 ^ 2 with hx2
    have n0 : 0 ≤ x0 := sq_nonneg _
    have n1 : 0 ≤ x1 := sq_nonneg _
    have n2 : 0 ≤ x2 := sq_nonneg _
    have hone : ∀ l, u i l ≠ 0 → (1 : ℝ) ≤ castVec (u i) l ^ 2 := by
      intro l hl
      have h1 : (1 : ℤ) ≤ (u i l) ^ 2 := by
        have := Int.one_le_abs hl
        nlinarith [sq_abs (u i l)]
      have h' : ((1 : ℤ) : ℝ) ≤ (((u i l) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
      simpa [castVec] using h'
    have hsum : 1 ≤ x0 + x1 + x2 := by
      by_cases h0 : u i 0 = 0
      · by_cases h1 : u i 1 = 0
        · by_cases h2 : u i 2 = 0
          · exfalso
            apply hne
            funext l
            fin_cases l
            · exact h0
            · exact h1
            · exact h2
          · have := hone 2 h2; linarith
        · have := hone 1 h1; linarith
      · have := hone 0 h0; linarith
    have hle : (a - 1) * x0 + (b - 1) * x1 + (c - 1) * x2 ≤ 0 := by
      have : (a - 1) * x0 + (b - 1) * x1 + (c - 1) * x2 = 1 - (x0 + x1 + x2) := by
        linear_combination hq
      linarith
    have p0 : 0 ≤ (a - 1) * x0 := mul_nonneg (sub_nonneg.2 ea) n0
    have p1 : 0 ≤ (b - 1) * x1 := mul_nonneg (sub_nonneg.2 eb) n1
    have p2 : 0 ≤ (c - 1) * x2 := mul_nonneg (sub_nonneg.2 ec) n2
    have t0 : (a - 1) * x0 = 0 := by linarith
    have t1 : (b - 1) * x1 = 0 := by linarith
    have t2 : (c - 1) * x2 = 0 := by linarith
    fin_cases j
    · have hx : x0 ≠ 0 := by have := hone 0 hij; linarith
      have := (mul_eq_zero.1 t0).resolve_right hx
      change a = 1
      linarith
    · have hx : x1 ≠ 0 := by have := hone 1 hij; linarith
      have := (mul_eq_zero.1 t1).resolve_right hx
      change b = 1
      linarith
    · have hx : x2 ≠ 0 := by have := hone 2 hij; linarith
      have := (mul_eq_zero.1 t2).resolve_right hx
      change c = 1
      linarith
  -- every coordinate occurs in some basis vector
  have cover : ∀ j, ∃ i, u i j ≠ 0 := by
    intro j
    by_contra hcon
    exact hdet0 (Matrix.det_eq_zero_of_column_eq_zero j fun i => by
      by_contra h
      exact hcon ⟨i, h⟩)
  obtain ⟨i0, h0⟩ := cover 0
  obtain ⟨i1, h1⟩ := cover 1
  obtain ⟨i2, h2⟩ := cover 2
  exact ⟨by simpa using key i0 0 h0, by simpa using key i1 1 h1, by simpa using key i2 2 h2⟩

/-- The identity form is the only point of the flat in any top cell, and it lies in the top cell of
every signed-permutation basis: the shortest nonzero integral vectors of the identity form are
exactly `±e_k`. -/
theorem identity_minimal_vectors (v : Fin 3 → ℤ) (hv : v ≠ 0) :
    qf (diagForm 1 1 1) (castVec v) = 1 ↔
      ∃ k : Fin 3, v = Pi.single k 1 ∨ v = -Pi.single k 1 := by
  rw [qf_diag]
  simp only [one_mul, castVec]
  constructor
  · intro h
    have h' : (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 = 1 := by exact_mod_cast h
    have a0 : (v 0) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
    have a1 : (v 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 2)]
    have a2 : (v 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have b0 : v 0 = -1 ∨ v 0 = 0 ∨ v 0 = 1 := by
      have := abs_le.1 (abs_le_one_iff_mul_self_le_one.2 (by nlinarith) : |v 0| ≤ 1)
      omega
    have b1 : v 1 = -1 ∨ v 1 = 0 ∨ v 1 = 1 := by
      have := abs_le.1 (abs_le_one_iff_mul_self_le_one.2 (by nlinarith) : |v 1| ≤ 1)
      omega
    have b2 : v 2 = -1 ∨ v 2 = 0 ∨ v 2 = 1 := by
      have := abs_le.1 (abs_le_one_iff_mul_self_le_one.2 (by nlinarith) : |v 2| ≤ 1)
      omega
    rcases b0 with h0 | h0 | h0 <;> rcases b1 with h1 | h1 | h1 <;>
      rcases b2 with h2 | h2 | h2 <;>
      first
      | (exfalso; rw [h0, h1, h2] at h'; norm_num at h'; done)
      | (refine ⟨0, Or.inl ?_⟩; funext l; fin_cases l <;> simp [h0, h1, h2]; done)
      | (refine ⟨0, Or.inr ?_⟩; funext l; fin_cases l <;> simp [h0, h1, h2]; done)
      | (refine ⟨1, Or.inl ?_⟩; funext l; fin_cases l <;> simp [h0, h1, h2]; done)
      | (refine ⟨1, Or.inr ?_⟩; funext l; fin_cases l <;> simp [h0, h1, h2]; done)
      | (refine ⟨2, Or.inl ?_⟩; funext l; fin_cases l <;> simp [h0, h1, h2]; done)
      | (refine ⟨2, Or.inr ?_⟩; funext l; fin_cases l <;> simp [h0, h1, h2])
  · rintro ⟨k, hk | hk⟩ <;> subst hk <;> fin_cases k <;> simp

/-- The identity form is in the standard top cell (the cell of the standard basis). -/
theorem identity_mem_standard_cell :
    diagForm 1 1 1 ∈ TopCellOf (fun i => Pi.single i 1) := by
  refine ⟨fun i => by fin_cases i <;> simp [qf_diag, castVec], fun v hv => ?_⟩
  rw [qf_diag]
  simp only [one_mul, castVec]
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · have h2 : v 2 ≠ 0 := fun h2 => hv (funext fun l => by fin_cases l <;> simp [h0, h1, h2])
      have : (1 : ℤ) ≤ v 2 ^ 2 := by
        have := Int.one_le_abs h2
        nlinarith [sq_abs (v 2)]
      have h' : ((1 : ℤ) : ℝ) ≤ ((v 2 ^ 2 : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      nlinarith [sq_nonneg ((v 0 : ℝ)), sq_nonneg ((v 1 : ℝ))]
    · have : (1 : ℤ) ≤ v 1 ^ 2 := by
        have := Int.one_le_abs h1
        nlinarith [sq_abs (v 1)]
      have h' : ((1 : ℤ) : ℝ) ≤ ((v 1 ^ 2 : ℤ) : ℝ) := by exact_mod_cast this
      push_cast at h'
      nlinarith [sq_nonneg ((v 0 : ℝ)), sq_nonneg ((v 2 : ℝ))]
  · have : (1 : ℤ) ≤ v 0 ^ 2 := by
      have := Int.one_le_abs h0
      nlinarith [sq_abs (v 0)]
    have h' : ((1 : ℤ) : ℝ) ≤ ((v 0 ^ 2 : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    nlinarith [sq_nonneg ((v 1 : ℝ)), sq_nonneg ((v 2 : ℝ))]

/-- The tangent space at the identity of the flat: trace-zero diagonal matrices. -/
def TangentFlat (D : Mat3) : Prop := ∃ x y z : ℝ, D = Matrix.diagonal ![x, y, z] ∧ x + y + z = 0

/-- The tangent space at the identity of the standard top cell: the off-diagonal symmetric
matrices `(r₁₂, r₁₃, r₂₃)`. -/
def TangentCell (R : Mat3) : Prop := Rᵀ = R ∧ ∀ i, R i i = 0

/-- The tangent space at the identity of the symmetric space `{symmetric, det 1}`: symmetric
matrices of trace zero. -/
def TangentSpace (X : Mat3) : Prop := Xᵀ = X ∧ X.trace = 0

/-- **Transversality.** At the identity the tangent spaces of the flat and of the standard top cell
are complementary in the tangent space of the symmetric space (`2 + 3 = 5`): every tangent vector
is uniquely the sum of a tangent vector of the flat and one of the cell. -/
theorem flat_cell_transverse (X : Mat3) (hX : TangentSpace X) :
    ∃! p : Mat3 × Mat3, TangentFlat p.1 ∧ TangentCell p.2 ∧ X = p.1 + p.2 := by
  refine ⟨(Matrix.diagonal (fun i => X i i), X - Matrix.diagonal (fun i => X i i)),
    ⟨?_, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · refine ⟨X 0 0, X 1 1, X 2 2, ?_, ?_⟩
    · funext i
      fin_cases i <;> rfl
    · have := hX.2
      simp [Matrix.trace, Fin.sum_univ_three] at this
      linarith
  · rw [Matrix.transpose_sub, Matrix.diagonal_transpose, hX.1]
  · intro i
    simp
  · exact (add_sub_cancel _ _).symm
  · rintro ⟨D, R⟩ ⟨⟨x, y, z, hD, -⟩, ⟨hR1, hR2⟩, hXDR⟩
    simp only at hD hR1 hR2 hXDR
    have hXii : ∀ i, X i i = ![x, y, z] i := by
      intro i
      have h := congrFun (congrFun hXDR i) i
      rw [hD] at h
      simpa [Matrix.add_apply, hR2 i] using h
    have hDd : D = Matrix.diagonal (fun i => X i i) := by
      rw [hD]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hXii i]
      · simp [hij]
    refine Prod.ext hDd ?_
    simp only
    rw [eq_sub_iff_add_eq', ← hDd, ← hXDR]

/-- **The flat meets the union of the top cells exactly at the identity.** For a point
`diag(a, b, (ab)⁻¹)` of the flat: it lies in the top cell of some integral basis iff it is the
identity form. -/
theorem flat_meets_cells_iff {a b c : ℝ} (hf : OnFlat a b c) :
    (∃ u : Fin 3 → Fin 3 → ℤ, ((Matrix.of u).det = 1 ∨ (Matrix.of u).det = -1) ∧
        diagForm a b c ∈ TopCellOf u) ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · rintro ⟨u, hu, hA⟩
    exact flat_cell_eq_identity u hu hA
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨fun i => Pi.single i 1, Or.inl ?_, identity_mem_standard_cell⟩
    have : (Matrix.of fun (i : Fin 3) => (Pi.single i 1 : Fin 3 → ℤ)) = 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [this, Matrix.det_one]

end TernaryPeriodPolynomials.Argument.AppendixLemmas.Flat
