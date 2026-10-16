module

public import Mathlib

@[expose] public section


/-!
# Matrices of positive determinant are path connected to the identity (`3 × 3` real case)

`Conn A`: `A` is joined to the identity by a path of real `3 × 3` matrices of positive determinant.
`conn_of_det_pos`: every matrix of positive determinant is so connected.  Proof: Mathlib's generation
of `GLₙ` by transvections and diagonal matrices; transvections `1 + s c E_{ij}` and positive
diagonal matrices are joined to `1` by straight lines, and the diagonal matrices with two negative
entries by a half-turn rotation in a coordinate plane.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma33.Orient

/-- A real `3 × 3` matrix joined to the identity by a path of matrices of positive determinant. -/
def Conn (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∃ γ : unitInterval → Matrix (Fin 3) (Fin 3) ℝ, Continuous γ ∧ γ 0 = 1 ∧ γ 1 = A ∧
    ∀ s, 0 < (γ s).det

theorem Conn.mul {A B : Matrix (Fin 3) (Fin 3) ℝ} (hA : Conn A) (hB : Conn B) : Conn (A * B) := by
  obtain ⟨a, ha, ha0, ha1, had⟩ := hA
  obtain ⟨b, hb, hb0, hb1, hbd⟩ := hB
  refine ⟨fun s => a s * b s, ha.matrix_mul hb, by simp [ha0, hb0], by simp [ha1, hb1], fun s => ?_⟩
  rw [Matrix.det_mul]
  exact mul_pos (had s) (hbd s)

theorem conn_one : Conn 1 := ⟨fun _ => 1, continuous_const, rfl, rfl, fun _ => by simp⟩

theorem conn_transvection (t : Matrix.TransvectionStruct (Fin 3) ℝ) : Conn t.toMatrix := by
  refine ⟨fun s => Matrix.transvection t.i t.j ((s : ℝ) * t.c), ?_, ?_, ?_, ?_⟩
  · refine continuous_matrix fun i' j' => ?_
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    by_cases h : t.i = i' ∧ t.j = j'
    · simp only [h, and_self, ite_true]
      exact continuous_const.add (continuous_subtype_val.mul continuous_const)
    · simp only [h, ite_false]
      exact continuous_const.add continuous_const
  · simp [Matrix.transvection]
  · simp [Matrix.TransvectionStruct.toMatrix]
  · intro s
    rw [Matrix.det_transvection_of_ne _ _ t.hij]
    exact one_pos

theorem conn_diag_pos (D : Fin 3 → ℝ) (hD : ∀ i, 0 < D i) : Conn (Matrix.diagonal D) := by
  refine ⟨fun s => Matrix.diagonal (fun i => (1 - (s : ℝ)) + (s : ℝ) * D i), ?_, ?_, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    by_cases h : i = j
    · subst h
      simp only [Matrix.diagonal_apply_eq]
      exact (continuous_const.sub continuous_subtype_val).add (continuous_subtype_val.mul continuous_const)
    · simp only [Matrix.diagonal_apply_ne _ h]
      exact continuous_const
  · ext i j; simp [Matrix.diagonal_apply, Matrix.one_apply]
  · ext i j; simp [Matrix.diagonal_apply]
  · intro s
    rw [Matrix.det_diagonal]
    apply Finset.prod_pos
    intro i _
    have h1 := s.2.1
    have h2 := s.2.2
    have h3 := hD i
    have hm := lt_min one_pos h3
    have a : min 1 (D i) ≤ 1 := min_le_left _ _
    have b : min 1 (D i) ≤ D i := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_left a (sub_nonneg.2 h2), mul_le_mul_of_nonneg_left b h1]

/-- Rotation in the plane of coordinates `0,1`. -/
def R01 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]

/-- Rotation in the plane of coordinates `0,2`. -/
def R02 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, 0, -Real.sin θ; 0, 1, 0; Real.sin θ, 0, Real.cos θ]

/-- Rotation in the plane of coordinates `1,2`. -/
def R12 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Real.cos θ, -Real.sin θ; 0, Real.sin θ, Real.cos θ]

theorem conn_R (R : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (hc : Continuous R) (h0 : R 0 = 1)
    (hd : ∀ θ, 0 < (R θ).det) : Conn (R Real.pi) :=
  ⟨fun s => R (Real.pi * (s : ℝ)), hc.comp (continuous_const.mul continuous_subtype_val),
    by simpa using h0, by simp, fun s => hd _⟩

theorem conn_N01 : Conn (Matrix.diagonal ![-1, -1, 1]) := by
  have : R01 Real.pi = Matrix.diagonal ![-1, -1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [R01, ]
  rw [← this]
  refine conn_R R01 ?_ ?_ ?_
  · unfold R01
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · ext i j; fin_cases i <;> fin_cases j <;> simp [R01]
  · intro θ
    simp [R01, Matrix.det_fin_three]
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem conn_N02 : Conn (Matrix.diagonal ![-1, 1, -1]) := by
  have : R02 Real.pi = Matrix.diagonal ![-1, 1, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [R02, ]
  rw [← this]
  refine conn_R R02 ?_ ?_ ?_
  · unfold R02
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · ext i j; fin_cases i <;> fin_cases j <;> simp [R02]
  · intro θ
    simp [R02, Matrix.det_fin_three]
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem conn_N12 : Conn (Matrix.diagonal ![1, -1, -1]) := by
  have : R12 Real.pi = Matrix.diagonal ![1, -1, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [R12, ]
  rw [← this]
  refine conn_R R12 ?_ ?_ ?_
  · unfold R12
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · ext i j; fin_cases i <;> fin_cases j <;> simp [R12]
  · intro θ
    simp [R12, Matrix.det_fin_three]
    nlinarith [Real.sin_sq_add_cos_sq θ]

theorem conn_diagonal (D : Fin 3 → ℝ) (h : 0 < ∏ i, D i) : Conn (Matrix.diagonal D) := by
  rw [Fin.prod_univ_three] at h
  have n0 : D 0 ≠ 0 := by intro e; rw [e] at h; simp at h
  have n1 : D 1 ≠ 0 := by intro e; rw [e] at h; simp at h
  have n2 : D 2 ≠ 0 := by intro e; rw [e] at h; simp at h
  have hne : ∀ i, D i ≠ 0 := by
    intro i; fin_cases i
    · exact n0
    · exact n1
    · exact n2
  have key : ∀ s : Fin 3 → ℝ, (D = fun i => |D i| * s i) →
      Conn (Matrix.diagonal s) → Conn (Matrix.diagonal D) := by
    intro s hs hconn
    have hpos : Conn (Matrix.diagonal (fun i => |D i|)) :=
      conn_diag_pos _ (fun i => abs_pos.mpr (hne i))
    have := hpos.mul hconn
    rw [Matrix.diagonal_mul_diagonal] at this
    have e : (fun i => |D i| * s i) = D := hs.symm
    rw [e] at this
    exact this
  rcases lt_or_gt_of_ne (hne 0) with h0 | h0 <;> rcases lt_or_gt_of_ne (hne 1) with h1 | h1 <;>
    rcases lt_or_gt_of_ne (hne 2) with h2 | h2
  · exfalso; nlinarith [mul_pos_of_neg_of_neg h0 h1]
  · refine key ![-1, -1, 1] ?_ conn_N01
    funext i; fin_cases i <;> simp [abs_of_neg, abs_of_pos, *]
  · refine key ![-1, 1, -1] ?_ conn_N02
    funext i; fin_cases i <;> simp [abs_of_neg, abs_of_pos, *]
  · exfalso; nlinarith [mul_pos_of_neg_of_neg h0 h0, mul_pos h1 h2]
  · refine key ![1, -1, -1] ?_ conn_N12
    funext i; fin_cases i <;> simp [abs_of_neg, abs_of_pos, *]
  · exfalso; nlinarith [mul_pos_of_neg_of_neg h1 h1, mul_pos h0 h2]
  · exfalso; nlinarith [mul_pos_of_neg_of_neg h2 h2, mul_pos h0 h1]
  · refine key ![1, 1, 1] ?_ (by
    have e : Matrix.diagonal (![1, 1, 1] : Fin 3 → ℝ) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [e]; exact conn_one)
    funext i; fin_cases i <;> simp [abs_of_pos, *]

theorem conn_of_det_pos (A : Matrix (Fin 3) (Fin 3) ℝ) (h : 0 < A.det) : Conn A := by
  refine Matrix.diagonal_transvection_induction (fun M => Conn M) A ?_ ?_ ?_
  · intro D hD
    rw [Matrix.det_diagonal, Fin.prod_univ_three] at hD
    apply conn_diagonal
    rw [Fin.prod_univ_three, hD]
    exact h
  · exact conn_transvection
  · intro A B hA hB
    exact hA.mul hB

end TernaryPeriodPolynomials.Argument.Lemma33.Orient
