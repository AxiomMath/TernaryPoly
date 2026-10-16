module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.TopCohomologyNaturality
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Pi

@[expose] public section


open CategoryTheory Matrix
noncomputable section
namespace TernaryPoly.LatticeTopCohomology

/-- An actual integral change of the ordered lattice basis. -/
def matrixLattice (M : GeneralLinearGroup (Fin 2) ℤ) : Lattice ≃* Lattice :=
  AddEquiv.toMultiplicative (((LinearEquiv.finTwoArrow ℤ ℤ).symm.trans
    (GeneralLinearGroup.toLin M).toLinearEquiv).trans (LinearEquiv.finTwoArrow ℤ ℤ)).toAddEquiv

@[simp] theorem matrixLattice_coordinates (M : GeneralLinearGroup (Fin 2) ℤ) (g : Lattice) :
    (matrixLattice M g).toAdd =
      ((M.val.mulVec ![g.toAdd.1,g.toAdd.2]) 0, (M.val.mulVec ![g.toAdd.1,g.toAdd.2]) 1) := rfl

@[simp] theorem matrixLattice_vector (M : GeneralLinearGroup (Fin 2) ℤ) (g : Lattice) :
    ![(matrixLattice M g).toAdd.1,(matrixLattice M g).toAdd.2] =
      M.val.mulVec ![g.toAdd.1,g.toAdd.2] := by
  funext i
  fin_cases i <;> rfl

/-- The cocycle determinant agrees with the literal determinant of an integral basis change. -/
@[simp] theorem latticeDeterminant_matrixLattice (M : GeneralLinearGroup (Fin 2) ℤ) :
    latticeDeterminant (matrixLattice M) = M.val.det := by
  simp [latticeDeterminant, matrixLattice_coordinates, first, second,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two, mul_comm]

end TernaryPoly.LatticeTopCohomology
