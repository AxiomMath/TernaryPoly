module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantDiagonal

@[expose] public section


open MvPolynomial Matrix

noncomputable section
namespace TernaryPoly.RadicalCoinvariantAlgebra
open RelativeStabilizerParameters RelativeStabilizerMatrices

/-- The exact scalar on each integral root parameter under diagonal conjugation. -/
def rootScale (ε : ℤˣ × ℤˣ) (k : Fin 3) : ℤ :=
  ![ε.1.val * (ε.2⁻¹).val, ε.1.val, ε.2.val] k

theorem diagonal_root_commute (ε : ℤˣ × ℤˣ) (k : Fin 3) (t : ℤ) :
    diagonalHom ε * rootElement k t =
      rootElement k (rootScale ε k * t) * diagonalHom ε := by
  rcases ε with ⟨a,b⟩
  rcases Int.units_eq_one_or a with rfl | rfl <;>
    rcases Int.units_eq_one_or b with rfl | rfl <;>
    apply Units.ext <;> rw [Units.val_mul, Units.val_mul] <;>
    fin_cases k <;> ext i j <;> rw [Matrix.mul_apply, Matrix.mul_apply] <;>
    fin_cases i <;> fin_cases j <;>
    simp [diagonalHom, rootElement, rootScale, bbMatrix, Fin.sum_univ_three]

/-- This is literal conjugation of the existing integral stabilizer matrices. -/
theorem diagonal_root_conjugate (ε : ℤˣ × ℤˣ) (k : Fin 3) (t : ℤ) :
    diagonalHom ε * rootElement k t * (diagonalHom ε)⁻¹ =
      rootElement k (rootScale ε k * t) := by
  rw [diagonal_root_commute, mul_assoc, mul_inv_cancel, mul_one]

/-- Conjugation on the ordered plane radical `(E13,E23)`. -/
def planeRadicalDiagonal (ε : ℤˣ × ℤˣ) : Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.diagonal ![(rootScale ε 1 : ℚ), (rootScale ε 2 : ℚ)]

/-- Conjugation on the ordered line radical `(E12,E13)`. -/
def lineRadicalDiagonal (ε : ℤˣ × ℤˣ) : Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.diagonal ![(rootScale ε 0 : ℚ), (rootScale ε 1 : ℚ)]

/-- The determinant character of the dual of the top exterior root space. -/
def planeRootDual (ε : ℤˣ × ℤˣ) : ℚ := (planeRadicalDiagonal ε).det⁻¹

def lineRootDual (ε : ℤˣ × ℤˣ) : ℚ := (lineRadicalDiagonal ε).det⁻¹

theorem planeRootDual_formula (ε : ℤˣ × ℤˣ) :
    planeRootDual ε = unitScalar ε.1⁻¹ * unitScalar ε.2⁻¹ := by
  rcases ε with ⟨a,b⟩
  rcases Int.units_eq_one_or a with rfl | rfl <;>
    rcases Int.units_eq_one_or b with rfl | rfl <;>
    simp [planeRootDual, planeRadicalDiagonal, rootScale, unitScalar]

theorem lineRootDual_formula (ε : ℤˣ × ℤˣ) :
    lineRootDual ε = unitScalar ε.1⁻¹ ^ 2 * unitScalar ε.2 := by
  rcases ε with ⟨a,b⟩
  rcases Int.units_eq_one_or a with rfl | rfl <;>
    rcases Int.units_eq_one_or b with rfl | rfl <;>
    simp [lineRootDual, lineRadicalDiagonal, rootScale, unitScalar]

/-- The full plane monomial scalar retains the top-exterior-dual determinant factor. -/
theorem plane_twisted_monomial (ε : ℤˣ × ℤˣ) (r s : ℕ) :
    planeRootDual ε •
      binaryDiagonal (unitScalar ε.1⁻¹) (unitScalar ε.2⁻¹) (X 0 ^ r * X 1 ^ s) =
    (unitScalar ε.1⁻¹ ^ (r+1) * unitScalar ε.2⁻¹ ^ (s+1)) •
      (X 0 ^ r * X 1 ^ s) := by
  rw [binaryDiagonal_monomial, smul_smul, planeRootDual_formula]
  congr 1
  simp only [pow_succ]
  ring

/-- The actual axis character including the top-exterior-dual determinant factor. -/
theorem line_twisted_character (n : ℕ) (ε : ℤˣ × ℤˣ) (p : H n) :
    lineRootDual ε *
      unaryScalarEquiv n (lineEval n (PolynomialGLAction.integralAction n 0 (diagonalHom ε) p)) =
    (unitScalar ε.1⁻¹ ^ (n+2) * unitScalar ε.2) *
      unaryScalarEquiv n (lineEval n p) := by
  rw [lineScalar_integralAction_diagonal, lineRootDual_formula, pow_add]
  ring

/-- An actual diagonal element kills invariants in the twisted line coinvariants. -/
theorem line_twisted_fixed_eq_zero (n : ℕ) (p : H n)
    (hp : ∀ ε : ℤˣ × ℤˣ,
      lineRootDual ε *
        unaryScalarEquiv n (lineEval n (PolynomialGLAction.integralAction n 0 (diagonalHom ε) p)) =
      unaryScalarEquiv n (lineEval n p)) :
    unaryScalarEquiv n (lineEval n p) = 0 := by
  have h := hp (1,-1)
  rw [line_twisted_character] at h
  simp only [unitScalar, inv_one, Units.val_one, Int.cast_one, one_pow,
    Units.val_neg, Int.cast_neg, one_mul, neg_mul] at h
  linarith

end TernaryPoly.RadicalCoinvariantAlgebra
