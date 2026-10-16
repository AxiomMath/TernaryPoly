module

public import TernaryPeriodPolynomials.SymmetricSpace.MatrixIsotopy.Transvections

@[expose] public section

noncomputable section
namespace TernaryPoly.RealMatrixIsotopy
open Matrix Matrix.SpecialLinearGroup

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Products of matrices joined to identity remain joined to identity. -/
theorem joined_one_mul {A B : SpecialLinearGroup ι ℝ}
    (hA : Joined 1 A) (hB : Joined 1 B) : Joined 1 (A * B) := by
  simpa using hA.mul hB

/-- Every real special-linear matrix is joined to identity by an actual continuous path. -/
theorem specialLinear_joined_one (A : SpecialLinearGroup ι ℝ) : Joined 1 A := by
  cases subsingleton_or_nontrivial ι with
  | inl h =>
      let := h
      simpa only [Subsingleton.elim A 1] using Joined.refl (1 : SpecialLinearGroup ι ℝ)
  | inr h =>
      let := h
      apply diagonal_transvection_induction' (fun A => Joined 1 A) A
      · intro i j hij a ha
        rw [diag2n_decompose hij a ha]
        apply joined_one_mul
        · apply joined_one_mul
          · apply joined_one_mul
            · apply joined_one_mul
              · apply joined_one_mul
                · exact ⟨transvectionPath hij a⟩
                · exact ⟨transvectionPath hij.symm (-a⁻¹)⟩
              · exact ⟨transvectionPath hij a⟩
            · exact ⟨transvectionPath hij (-1)⟩
          · exact ⟨transvectionPath hij.symm 1⟩
        · exact ⟨transvectionPath hij (-1)⟩
      · intro i j hij a
        exact ⟨transvectionPath hij a⟩
      · intro A B hA hB
        exact joined_one_mul hA hB

/-- Real special-linear groups in all finite dimensions are path connected. -/
instance specialLinear_pathConnectedSpace : PathConnectedSpace (SpecialLinearGroup ι ℝ) where
  nonempty := ⟨1⟩
  joined A B := (specialLinear_joined_one A).symm.trans (specialLinear_joined_one B)

/-- A chosen genuine special-linear path, with every value still determinant one. -/
def specialLinearPath (A : SpecialLinearGroup ι ℝ) : Path 1 A :=
  (specialLinear_joined_one A).somePath

end TernaryPoly.RealMatrixIsotopy
