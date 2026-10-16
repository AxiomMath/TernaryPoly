module

public import TernaryPeriodPolynomials.SymmetricSpace.Parabolic.CoordinatesBasic

@[expose] public section


open Matrix
noncomputable section
namespace TernaryPoly.SymmetricSpaceParabolicCoordinates
open SymmetricSpacePositive

/-- The actual block diagonal matrix is strictly positive, including the complementary direction. -/
theorem diagonalBlock_positive (B : Mat2) (hB : B.PosDef) : (diagonalBlock B).PosDef := by
  have hsym : B.IsSymm := Matrix.isHermitian_iff_isSymm.mp hB.isHermitian
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j
    all_goals first | rfl | exact hsym.apply _ _
  · intro x hx
    let w : Vec2 := ![x 0,x 1]
    have hform : star x ⬝ᵥ (diagonalBlock B *ᵥ x)=
        star w ⬝ᵥ (B *ᵥ w)+(x 2)^2 := by
      simp [diagonalBlock,w,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,pow_two]
      ring
    rw [hform]
    by_cases hw : w=0
    · have hx0 : x 0=0 := congrFun hw 0
      have hx1 : x 1=0 := congrFun hw 1
      have hx2 : x 2≠0 := by
        intro h2
        apply hx
        ext i
        fin_cases i <;> assumption
      simpa [hw] using sq_pos_of_ne_zero hx2
    · exact add_pos_of_pos_of_nonneg (hB.dotProduct_mulVec_pos hw) (sq_nonneg _)

/-- The proposed inverse coordinate matrix is genuinely positive definite. -/
theorem assemble_positive (v : Vec2) (B : Mat2) (hB : B.PosDef) :
    (assemble v B).PosDef := by
  have h := conjugate_positive (shearGL v) (diagonalBlock B) (diagonalBlock_positive B hB)
  change (shearMatrix v*diagonalBlock B*star (shearMatrix v)).PosDef at h
  rw [shear_diagonalBlock] at h
  exact h

theorem height_pos (S : Mat) (hS : S.PosDef) : 0<height S := hS.diag_pos

/-- Strict Schur positivity follows from actual unipotent congruence and a principal submatrix. -/
theorem schur_positive (S : Mat) (hS : S.PosDef) : (schur S).PosDef := by
  have ha := height_pos S hS
  have hlift : (assemble (unipotent S) (schur S)).PosDef := by
    rw [assemble_coordinates S (Matrix.isHermitian_iff_isSymm.mp hS.isHermitian) (ne_of_gt ha)]
    exact hS.smul (inv_pos.mpr ha)
  have hc := conjugate_positive (shearGL (-unipotent S)) _ hlift
  change (shearMatrix (-unipotent S)*assemble (unipotent S) (schur S)*
    star (shearMatrix (-unipotent S))).PosDef at hc
  rw [unshear_assemble] at hc
  simpa using hc.submatrix topIndex_injective

/-- The inverse formula recovers the original trace-one representative exactly. -/
theorem normalize_assemble_coordinates (S : Space) :
    normalize (assemble (unipotent S.val) (schur S.val))=S.val := by
  rw [assemble_coordinates S.val
    (Matrix.isHermitian_iff_isSymm.mp S.property.1.isHermitian)
    (ne_of_gt (height_pos S.val S.property.1)),
    normalize_smul _ (inv_ne_zero (ne_of_gt (height_pos S.val S.property.1))),
    normalize_of_trace_one _ S.property.2]

theorem unipotent_normalize (S : Mat) (hS : S.PosDef) :
    unipotent (normalize S)=unipotent S :=
  unipotent_smul _ (inv_ne_zero (ne_of_gt hS.trace_pos)) S

theorem schur_normalize (S : Mat) (hS : S.PosDef) : schur (normalize S)=schur S :=
  schur_smul _ (inv_ne_zero (ne_of_gt hS.trace_pos)) S

@[simp] theorem unipotent_normalize_assemble (v : Vec2) (B : Mat2) (hB : B.PosDef) :
    unipotent (normalize (assemble v B))=v := by
  rw [unipotent_normalize _ (assemble_positive v B hB),unipotent_assemble]

@[simp] theorem schur_normalize_assemble (v : Vec2) (B : Mat2) (hB : B.PosDef) :
    schur (normalize (assemble v B))=B := by
  rw [schur_normalize _ (assemble_positive v B hB),schur_assemble]

end TernaryPoly.SymmetricSpaceParabolicCoordinates
