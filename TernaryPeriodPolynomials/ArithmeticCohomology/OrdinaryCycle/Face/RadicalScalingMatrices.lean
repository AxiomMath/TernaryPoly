module

public import TernaryPeriodPolynomials.SymmetricSolution.LineCohomology.Levi
public import TernaryPeriodPolynomials.GroupCohomology.Radical.TopCohomologyPlane

@[expose] public section


open CategoryTheory MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.OrdinaryFaceRadical
open RadicalCoinvariantAlgebra RadicalFirstCohomologyLattice LatticeTopCohomology
open RelativeStabilizerParameters RelativeStabilizerMatrices PolynomialGLAction
open SymmetricLineCohomology

/-- Multiplication of both actual integral radical parameters by the same integer. -/
def scaleLattice (k : ℤ) : Lattice →* Lattice where
  toFun g := Multiplicative.ofAdd (k*g.toAdd.1,k*g.toAdd.2)
  map_one' := by simp
  map_mul' g h := by change (_,_) = (_,_); congr 1 <;> dsimp <;> ring

theorem scaleLattice_matrix (k : ℤ) (M : GL2) (g : Lattice) :
    scaleLattice k (matrixLattice M g)=matrixLattice M (scaleLattice k g) := by
  change (k*(matrixLattice M g).toAdd.1,k*(matrixLattice M g).toAdd.2)=
    (matrixLattice M (scaleLattice k g)).toAdd
  simp only [matrixLattice_coordinates]
  simp [scaleLattice,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  constructor <;> ring

theorem scaleLattice_lineLevi (k : ℤ) (t : ℤˣ) (M : GL2) (g : Lattice) :
    scaleLattice k (leviLatticeChange t M g)=leviLatticeChange t M (scaleLattice k g) := by
  change (scaleLattice k (leviLatticeChange t M g)).toAdd=
    (leviLatticeChange t M (scaleLattice k g)).toAdd
  dsimp [scaleLattice,leviLatticeChange]
  congr 1 <;> ring

/-- Rational plane normal-coordinate scaling conjugates the step-three lattice to the original lattice. -/
def planeScale : GL3 where
  val := Matrix.diagonal (![1,1,3] : Fin 3 → ℚ)
  inv := Matrix.diagonal (![1,1,1/3] : Fin 3 → ℚ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]

/-- Rational scaling of the lower plane conjugates the step-three line lattice to the original lattice. -/
def lineScale : GL3 where
  val := Matrix.diagonal (![1,3,3] : Fin 3 → ℚ)
  inv := Matrix.diagonal (![1,1/3,1/3] : Fin 3 → ℚ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal]

theorem planeScale_radical (g : Lattice) :
    planeScale*GeneralLinearGroup.map (Int.castRingHom ℚ) (planeHom (scaleLattice 3 g))=
      GeneralLinearGroup.map (Int.castRingHom ℚ) (planeHom g)*planeScale := by
  apply Units.ext
  rw [Units.val_mul,Units.val_mul]
  ext i j
  rw [Matrix.mul_apply,Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [planeScale,GeneralLinearGroup.map_apply,planeHom,planeElement_val,planeMatrix,
      scaleLattice,Fin.sum_univ_three] <;> ring

theorem lineScale_radical (g : Lattice) :
    lineScale*GeneralLinearGroup.map (Int.castRingHom ℚ) (lineHom (scaleLattice 3 g))=
      GeneralLinearGroup.map (Int.castRingHom ℚ) (lineHom g)*lineScale := by
  apply Units.ext
  rw [Units.val_mul,Units.val_mul]
  ext i j
  rw [Matrix.mul_apply,Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [lineScale,GeneralLinearGroup.map_apply,lineHom,lineElement_val,lineMatrix,
      scaleLattice,Fin.sum_univ_three] <;> ring

theorem planeScale_Levi (M : GL2) :
    planeScale*GeneralLinearGroup.map (Int.castRingHom ℚ) (planeElement M 0)=
      GeneralLinearGroup.map (Int.castRingHom ℚ) (planeElement M 0)*planeScale := by
  apply Units.ext
  rw [Units.val_mul,Units.val_mul]
  ext i j
  rw [Matrix.mul_apply,Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [planeScale,GeneralLinearGroup.map_apply,planeElement_val,planeMatrix,Fin.sum_univ_three]

theorem lineScale_Levi (t : ℤˣ) (M : GL2) :
    lineScale*GeneralLinearGroup.map (Int.castRingHom ℚ) (lineElement t 0 M)=
      GeneralLinearGroup.map (Int.castRingHom ℚ) (lineElement t 0 M)*lineScale := by
  apply Units.ext
  rw [Units.val_mul,Units.val_mul]
  ext i j
  rw [Matrix.mul_apply,Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [lineScale,GeneralLinearGroup.map_apply,lineElement_val,lineMatrix,Fin.sum_univ_three] <;> ring

end TernaryPoly.OrdinaryFaceRadical
