module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.SymbolRows
public import TernaryPeriodPolynomials.Polynomial.CharTwo.OrbitFrames
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrbitSymbolSystem
open CharTwoToddSymbol CharTwoSymbolRows

/-- The exact enumeration of the complete polynomial source. -/
def sourceEquiv : Fin 32 ≃ Fin 8 × Fin 2 × Fin 2 where
  toFun := sourceIndex
  invFun := fun i => ⟨4*i.1.val+2*i.2.1.val+i.2.2.val, by omega⟩
  left_inv := by
    intro i
    apply Fin.ext
    dsimp [sourceIndex]
    omega
  right_inv := by
    rintro ⟨a,b,c⟩
    apply Prod.ext
    · apply Fin.ext
      dsimp [sourceIndex]
      omega
    · apply Prod.ext <;> apply Fin.ext <;> dsimp [sourceIndex] <;> omega

/-- A literal root-row matrix in the target polynomial ring. -/
def rootMatrix : Matrix (Fin 32) (Fin 32) Poly :=
  fun i j => CharTwoOrbitFrames.frame ⟨i.val/2, by omega⟩
    (if i.val % 2 = 0 then rootP j else rootQ j)

/-- The matrix of actual derivative rows, obtained by squaring the root rows. -/
def differentialMatrix : Matrix (Fin 32) (Fin 32) Poly :=
  fun i j => (rootMatrix i j)^2

/-- The full source expansion, reindexed without changing its order. -/
theorem reindex_expansion {H : Poly}
    (q : Fin 8 × Fin 2 × Fin 2 → Poly)
    (he : H = ∑ i, formalSquaredInvariantEval (q i)*CharTwoFormal.source32 i) :
    H = ∑ i : Fin 32, formalSquaredInvariantEval (q (sourceIndex i))*
      CharTwoFormal.source32 (sourceIndex i) := by
  rw [he]
  exact (Equiv.sum_comp sourceEquiv _).symm

/-- Vanishing of the Todd symbol supplies all32 homogeneous linear equations. -/
theorem source_system {H : Poly} (q : Fin 32 → Poly)
    (he : H = ∑ i, formalSquaredInvariantEval (q i)*CharTwoFormal.source32 (sourceIndex i))
    (hz : jSymbol H = 0) :
    differentialMatrix.mulVec (fun i => CharTwoNorm.squaredInvariantEval (q i)) = 0 := by
  obtain ⟨hp,hq⟩ := rows_zero_of_jSymbol_zero hz
  rw [he,symbolP_sum] at hp
  rw [he,symbolQ_sum] at hq
  simp only [symbolP_squaredInvariant_mul,symbolP_source] at hp
  simp only [symbolQ_squaredInvariant_mul,symbolQ_source] at hq
  funext i
  have hp' := congrArg (CharTwoOrbitFrames.frame ⟨i.val/2, by omega⟩) hp
  have hq' := congrArg (CharTwoOrbitFrames.frame ⟨i.val/2, by omega⟩) hq
  simp only [map_sum,map_mul,map_pow,map_zero,CharTwoOrbitFrames.frame_squaredInvariantEval] at hp' hq'
  simp only [Matrix.mulVec, dotProduct, differentialMatrix, rootMatrix, Pi.zero_apply]
  split_ifs with hi
  · simpa only [mul_comm] using hp'
  · simpa only [mul_comm] using hq'

/-- A nonzero literal determinant annihilates every complete-source Todd kernel. -/
theorem source_zero_of_det_ne_zero (hd : differentialMatrix.det ≠ 0)
    {H : Poly} (q : Fin 8 × Fin 2 × Fin 2 → Poly)
    (he : H = ∑ i, formalSquaredInvariantEval (q i)*CharTwoFormal.source32 i)
    (hz : jSymbol H = 0) : H = 0 := by
  have hs := source_system (fun i => q (sourceIndex i)) (reindex_expansion q he) hz
  have hc : (fun i => CharTwoNorm.squaredInvariantEval (q (sourceIndex i))) = 0 := by
    apply Matrix.mulVec_injective_of_det_ne_zero hd
    simpa using hs
  rw [reindex_expansion q he]
  apply Finset.sum_eq_zero
  intro i _
  have hi : formalSquaredInvariantEval (q (sourceIndex i)) = 0 := by
    apply CharTwoNorm.elementaryEval_injective
    rw [CharTwoFormal.elementary_formalSquaredInvariantEval,map_zero]
    exact congrFun hc i
  rw [hi,zero_mul]

end TernaryPoly.OrbitSymbolSystem
