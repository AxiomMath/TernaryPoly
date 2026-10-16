module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.ArithmeticLevel
public import Mathlib.LinearAlgebra.FreeModule.PID

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SmithMatrices

def basisUnit {R : Type} [CommRing R] {size : ℕ}
    (basis : Module.Basis (Fin size) R (Fin size → R)) : GeneralLinearGroup (Fin size) R where
  val := (Pi.basisFun R (Fin size)).toMatrix basis
  inv := basis.toMatrix (Pi.basisFun R (Fin size))
  val_inv := by rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
  inv_val := by rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]

theorem basisUnit_entry {R : Type} [CommRing R] {size : ℕ}
    (basis : Module.Basis (Fin size) R (Fin size → R)) (row column : Fin size) :
    (basisUnit basis).val row column = basis column row := by
  rfl

theorem mul_basisUnit_entry {R : Type} [CommRing R] {size : ℕ}
    (matrix : Matrix (Fin size) (Fin size) R)
    (basis : Module.Basis (Fin size) R (Fin size → R)) (row column : Fin size) :
    (matrix * (basisUnit basis).val) row column = (matrix.mulVecLin (basis column)) row := by
  rfl

theorem basisUnit_mul_diagonal_entry {R : Type} [CommRing R] {size : ℕ}
    (basis : Module.Basis (Fin size) R (Fin size → R)) (diagonal : Fin size → R)
    (row column : Fin size) :
    ((basisUnit basis).val * Matrix.diagonal diagonal) row column =
      (diagonal column • basis column) row := by
  simp [Matrix.mul_diagonal, basisUnit_entry, mul_comm]

theorem full_rank_smith {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {size : ℕ} (matrix : Matrix (Fin size) (Fin size) R) (nonzero : matrix.det ≠ 0) :
    ∃ left right : GeneralLinearGroup (Fin size) R, ∃ diagonal : Fin size → R,
      (∀ index, diagonal index ≠ 0) ∧ matrix * right.val = left.val * Matrix.diagonal diagonal := by
  let linear := matrix.mulVecLin
  have injective : Function.Injective linear := Matrix.mulVec_injective_of_det_ne_zero nonzero
  let equivalence := LinearEquiv.ofInjective linear injective
  have rank : Module.finrank R linear.range = Module.finrank R (Fin size → R) :=
    LinearMap.finrank_range_of_inj injective
  let topBasis := Submodule.smithNormalFormTopBasis (Pi.basisFun R (Fin size)) rank
  let bottomBasis := Submodule.smithNormalFormBotBasis (Pi.basisFun R (Fin size)) rank
  let domainBasis := bottomBasis.map equivalence.symm
  let diagonal := Submodule.smithNormalFormCoeffs (Pi.basisFun R (Fin size)) rank
  refine ⟨basisUnit topBasis, basisUnit domainBasis, diagonal, ?_, ?_⟩
  · exact Submodule.smithNormalFormCoeffs_ne_zero (Pi.basisFun R (Fin size)) rank
  · ext row column
    rw [mul_basisUnit_entry, basisUnit_mul_diagonal_entry]
    have image : linear (domainBasis column) = (bottomBasis column).val :=
      LinearEquiv.ofInjective_symm_apply linear (h := injective) (bottomBasis column)
    change linear (domainBasis column) row = (diagonal column • topBasis column) row
    rw [image]
    exact congrFun (Submodule.smithNormalFormBotBasis_def (Pi.basisFun R (Fin size)) rank column) row

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SmithMatrices
