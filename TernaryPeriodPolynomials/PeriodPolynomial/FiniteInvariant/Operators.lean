module

public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryHomogeneousCoordinates
public import TernaryPeriodPolynomials.ModularForm.ModularSymbol.Coefficients
public import TernaryPeriodPolynomials.Polynomial.Parity
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.SimpleRing.Matrix
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.BinaryFiniteInvariant
open BinaryHomogeneous

abbrev H (d : ℕ) := BinaryHomogeneous.H ℚ d
abbrev Mat := Matrix (Fin 2) (Fin 2) ℚ

/-- Actual matrix substitution on the exact homogeneous coefficient space. -/
def operator (d : ℕ) (M : Mat) : Module.End ℚ (H d) where
  toFun q := ⟨BinaryModularSymbolCoefficients.substitute M q.val,
    BinaryModularSymbolCoefficients.substitute_homogeneous M q.property⟩
  map_add' q r := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a q := by apply Subtype.ext; exact map_smul _ _ _

@[simp] theorem operator_coe (d : ℕ) (M : Mat) (q : H d) :
    (operator d M q).val = BinaryModularSymbolCoefficients.substitute M q.val := rfl

theorem operator_mul (d : ℕ) (M N : Mat) : operator d (M*N) = operator d N * operator d M := by
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  exact (congrArg (fun f : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ => f q.val)
    (BinaryModularSymbolCoefficients.substitute_comp N M)).symm

@[simp] theorem operator_one (d : ℕ) : operator d 1 = 1 := by
  ext q : 1
  apply Subtype.ext
  change BinaryModularSymbolCoefficients.substitute 1 q.val = q.val
  rw [BinaryModularSymbolCoefficients.substitute_one]
  rfl

def swapMatrix : Mat := !![0,1;1,0]
def firstSignMatrix : Mat := !![-1,0;0,1]
def rotationMatrix : Mat := !![0,-1;1,-1]
def swap (d : ℕ) := operator d swapMatrix
def negateFirst (d : ℕ) := operator d firstSignMatrix
def rotation (d : ℕ) := operator d rotationMatrix

@[simp] theorem swap_coe (d : ℕ) (q : H d) : (swap d q).val = bind₁ ![X 1,X 0] q.val := by
  change bind₁ (BinaryModularSymbolCoefficients.linearForm swapMatrix) q.val = _
  congr 2
  funext i
  fin_cases i <;> simp [BinaryModularSymbolCoefficients.linearForm,swapMatrix,Fin.sum_univ_two]

@[simp] theorem negateFirst_coe (d : ℕ) (q : H d) :
    (negateFirst d q).val = bind₁ ![-X 0,X 1] q.val := by
  change bind₁ (BinaryModularSymbolCoefficients.linearForm firstSignMatrix) q.val = _
  congr 2
  funext i
  fin_cases i <;> simp [BinaryModularSymbolCoefficients.linearForm,firstSignMatrix,Fin.sum_univ_two]

@[simp] theorem rotation_coe (d : ℕ) (q : H d) :
    (rotation d q).val = bind₁ ![-X 1,X 0-X 1] q.val := by
  change bind₁ (BinaryModularSymbolCoefficients.linearForm rotationMatrix) q.val = _
  congr 2
  funext i
  fin_cases i <;> simp [BinaryModularSymbolCoefficients.linearForm,rotationMatrix,Fin.sum_univ_two,sub_eq_add_neg]

theorem swap_sq (d : ℕ) : swap d * swap d = 1 := by
  rw [swap,←operator_mul]
  convert operator_one d using 1
  congr 1
  decide +kernel

theorem negateFirst_sq (d : ℕ) : negateFirst d * negateFirst d = 1 := by
  rw [negateFirst,←operator_mul]
  convert operator_one d using 1
  congr 1
  decide +kernel

theorem rotation_cube (d : ℕ) : rotation d * rotation d * rotation d = 1 := by
  rw [rotation,←operator_mul,←operator_mul]
  convert operator_one d using 1
  congr 1
  decide +kernel

theorem swap_rotation_swap (d : ℕ) : swap d * rotation d * swap d = rotation d * rotation d := by
  rw [swap,rotation,←operator_mul,←operator_mul,←operator_mul]
  congr 1
  decide +kernel

/-- Total negation is the actual homogeneous degree character. -/
theorem operator_neg_one (d : ℕ) : operator d (-1) = (-1 : ℚ)^d • (1 : Module.End ℚ (H d)) := by
  ext q : 1
  apply Subtype.ext
  change BinaryModularSymbolCoefficients.substitute (-1) q.val = (-1 : ℚ)^d • q.val
  have he := homogeneous_bind_smul q.property (-1 : ℚ)
  convert he using 2
  change bind₁ (BinaryModularSymbolCoefficients.linearForm (-1)) = bind₁ (fun i => (-1 : ℚ) • X i)
  congr 1
  funext i
  fin_cases i <;> simp [BinaryModularSymbolCoefficients.linearForm,Matrix.one_apply]

/-- On even degree the two involutions commute, as actual operators on homogeneous polynomials. -/
theorem swap_negateFirst_comm (d : ℕ) (hd : Even d) : swap d * negateFirst d = negateFirst d * swap d := by
  have hn : operator d (-1) = 1 := by rw [operator_neg_one,hd.neg_one_pow,one_smul]
  calc
    swap d * negateFirst d = operator d (firstSignMatrix*swapMatrix) := (operator_mul _ _ _).symm
    _ = operator d ((swapMatrix*firstSignMatrix)*(-1)) := by congr 1; decide +kernel
    _ = operator d (-1) * (negateFirst d * swap d) := by rw [operator_mul,operator_mul]; rfl
    _ = negateFirst d * swap d := by rw [hn,one_mul]

end TernaryPoly.BinaryFiniteInvariant
