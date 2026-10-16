module

public import TernaryPeriodPolynomials.GroupCohomology.Relative.Vertex.CohomologyGroups
public import TernaryPeriodPolynomials.GroupCohomology.Radical.TopCohomologySubgroups

@[expose] public section


open CategoryTheory Matrix
noncomputable section
namespace TernaryPoly.RelativeVertexCohomology
open ModThreeGoodAction RelativeStabilizerParameters RelativeStabilizerMatrices
open RadicalFirstCohomologyLattice RadicalTopCohomology

/-- The lower diagonal sign, with last coordinate fixed, belongs to the exact line Levi. -/
def lowerDiagonal (ε : ℤˣ) : Gamma :=
  ⟨⟨!![ε.val,0;0,1], !![(ε⁻¹).val,0;0,1], by
      ext i j
      rw [Matrix.mul_apply]
      fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two], by
      ext i j
      rw [Matrix.mul_apply]
      fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two]⟩,
    (mem_Gamma_iff _).mpr (by simp [GammaEntries])⟩

/-- The two actual independent signs embedded in the full line Levi. -/
def lineDiagonal (ε : ℤˣ × ℤˣ) : ℤˣ × Gamma := (ε.1,lowerDiagonal ε.2)

theorem lineLevi_diagonal (ε : ℤˣ × ℤˣ) : lineLevi (lineDiagonal ε) = diagonalHom ε := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineLevi,lineDiagonal,lowerDiagonal,lineElement_val,lineMatrix,diagonalHom,bbElement_val,bbMatrix]

theorem lineDiagonal_sign : lineDiagonal (-1,1) = (-1,1) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lineDiagonal,lowerDiagonal]

/-- Actual HS inverse conjugation agrees with the plane normalizer map. -/
theorem planeAction_inverse (M : GL2) : planeAction M⁻¹ = planeSubgroupChange M := by
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  rw [planeAction_val,planeSubgroupChange_conjugation,map_inv,inv_inv]
  rfl

/-- The full line Levi action restricts to the independent diagonal action. -/
theorem lineAction_inverse_diagonal (ε : ℤˣ × ℤˣ) :
    lineAction (lineDiagonal ε)⁻¹ = lineSubgroupChange ε := by
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  rw [lineAction_val,lineSubgroupChange_conjugation,map_inv,inv_inv,lineLevi_diagonal]

end TernaryPoly.RelativeVertexCohomology
