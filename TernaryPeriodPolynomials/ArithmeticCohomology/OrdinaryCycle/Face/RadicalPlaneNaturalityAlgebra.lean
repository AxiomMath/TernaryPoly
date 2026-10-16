module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalLatticeEvaluation
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalBinaryTransvections

@[expose] public section


open CategoryTheory MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice LatticeTopCohomology
open RelativeStabilizerParameters groupCohomology

/-- Actual matrix pullback at the first generator after binary face evaluation. -/
theorem planeEval_cocycle_matrix_first (n : ℕ) (c : cocycles₁ (planeRep n)) (M : GL2) :
    planeEval n (c (matrixLattice M first))=
      M.val 0 0 • planeEval n (c first)+M.val 1 0 • planeEval n (c second) := by
  rw [planeEval_cocycle_coordinates]
  simp [matrixLattice_coordinates,first,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

/-- Actual matrix pullback at the second generator after binary face evaluation. -/
theorem planeEval_cocycle_matrix_second (n : ℕ) (c : cocycles₁ (planeRep n)) (M : GL2) :
    planeEval n (c (matrixLattice M second))=
      M.val 0 1 • planeEval n (c first)+M.val 1 1 • planeEval n (c second) := by
  rw [planeEval_cocycle_coordinates]
  simp [matrixLattice_coordinates,second,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

/-- Binary contraction intertwines the literal column pullback and polynomial substitution. -/
theorem binary_matrix_contraction (M : GL2) (a b : MvPolynomial (Fin 2) ℚ) :
    X 0*binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) M).val
        (M.val 0 0 • a+M.val 1 0 • b)+
      X 1*binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) M).val
        (M.val 0 1 • a+M.val 1 1 • b)=
      binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) M).val (X 0*a+X 1*b) := by
  have h0 : binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) M).val (X 0)=
      MvPolynomial.C (M.val 0 0 : ℚ)*X 0+MvPolynomial.C (M.val 0 1 : ℚ)*X 1 := by
    simp [binaryMatrixSubst,GeneralLinearGroup.map_apply,Fin.sum_univ_two]
  have h1 : binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) M).val (X 1)=
      MvPolynomial.C (M.val 1 0 : ℚ)*X 0+MvPolynomial.C (M.val 1 1 : ℚ)*X 1 := by
    simp [binaryMatrixSubst,GeneralLinearGroup.map_apply,Fin.sum_univ_two]
  have hc (r : ℚ) : binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) M).val
      (MvPolynomial.C r)=MvPolynomial.C r := by simp [binaryMatrixSubst]
  simp only [map_add,map_mul,h0,h1,hc,←Int.cast_smul_eq_zsmul ℚ,
    Algebra.smul_def,MvPolynomial.algebraMap_eq]
  ring

end TernaryPoly.OrdinaryFaceRadical
