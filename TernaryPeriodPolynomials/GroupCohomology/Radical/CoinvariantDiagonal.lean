module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantMatrices
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantAxis

@[expose] public section


open MvPolynomial Matrix

noncomputable section
namespace TernaryPoly.RadicalCoinvariantAlgebra
open RelativeStabilizerParameters RelativeStabilizerMatrices

def unitScalar (a : ℤˣ) : ℚ := (a.val : ℚ)

def diagonalSubst (a b : ℚ) : Poly →ₐ[ℚ] Poly :=
  bind₁ ![C a * X 0, C b * X 1, X 2]

def binaryDiagonal (a b : ℚ) : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ :=
  bind₁ ![C a * X 0, C b * X 1]

def unaryDiagonal (a : ℚ) : MvPolynomial (Fin 1) ℚ →ₐ[ℚ] MvPolynomial (Fin 1) ℚ :=
  bind₁ ![C a * X 0]

theorem diagonal_substitute (ε : ℤˣ × ℤˣ) :
    PolynomialGLAction.substitute
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (diagonalHom ε)).val =
      diagonalSubst (unitScalar ε.1) (unitScalar ε.2) := by
  ext i
  rw [PolynomialGLAction.substitute_X]
  fin_cases i <;>
    simp [diagonalHom, bbMatrix, GeneralLinearGroup.map_apply,
      PolynomialGLAction.linearForm, Fin.sum_univ_three, diagonalSubst, unitScalar]

theorem integralAction_diagonal (n : ℕ) (ε : ℤˣ × ℤˣ) (p : H n) :
    (PolynomialGLAction.integralAction n 0 (diagonalHom ε) p : Poly) =
      diagonalSubst (unitScalar ε.1⁻¹) (unitScalar ε.2⁻¹) p := by
  rw [PolynomialGLAction.integralAction_coe, PolynomialGLAction.action_apply]
  simp only [PolynomialGLAction.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    zpow_zero, one_smul]
  rw [← map_inv, ← map_inv]
  exact DFunLike.congr_fun (diagonal_substitute ε⁻¹) (p : Poly)

theorem planeEval_diagonal (a b : ℚ) (p : Poly) :
    planeEvalAlg (diagonalSubst a b p) = binaryDiagonal a b (planeEvalAlg p) := by
  have h : planeEvalAlg.comp (diagonalSubst a b) =
      (binaryDiagonal a b).comp planeEvalAlg := by
    ext i; fin_cases i <;> simp [planeEvalAlg, diagonalSubst, binaryDiagonal]
  exact DFunLike.congr_fun h p

theorem lineEval_diagonal (a b : ℚ) (p : Poly) :
    lineEvalAlg (diagonalSubst a b p) = unaryDiagonal a (lineEvalAlg p) := by
  have h : lineEvalAlg.comp (diagonalSubst a b) =
      (unaryDiagonal a).comp lineEvalAlg := by
    ext i; fin_cases i <;> simp [lineEvalAlg, diagonalSubst, unaryDiagonal]
  exact DFunLike.congr_fun h p

/-- The actual diagonal action intertwines plane coinvariant evaluation. -/
theorem planeEval_integralAction_diagonal (n : ℕ) (ε : ℤˣ × ℤˣ) (p : H n) :
    (planeEval n (PolynomialGLAction.integralAction n 0 (diagonalHom ε) p) :
      MvPolynomial (Fin 2) ℚ) =
    binaryDiagonal (unitScalar ε.1⁻¹) (unitScalar ε.2⁻¹) (planeEval n p) := by
  rw [planeEval_coe, integralAction_diagonal, planeEval_diagonal]
  rfl

/-- The actual diagonal action intertwines line coinvariant evaluation. -/
theorem lineEval_integralAction_diagonal (n : ℕ) (ε : ℤˣ × ℤˣ) (p : H n) :
    (lineEval n (PolynomialGLAction.integralAction n 0 (diagonalHom ε) p) :
      MvPolynomial (Fin 1) ℚ) =
    unaryDiagonal (unitScalar ε.1⁻¹) (lineEval n p) := by
  rw [lineEval_coe, integralAction_diagonal, lineEval_diagonal]
  rfl

theorem unaryDiagonal_monomial (a : ℚ) (n : ℕ) (c : ℚ) :
    unaryDiagonal a (monomial (Finsupp.single (0 : Fin 1) n) c) =
      a ^ n • monomial (Finsupp.single (0 : Fin 1) n) c := by
  have hm : monomial (Finsupp.single (0 : Fin 1) n) c = X 0 ^ n * C c := by
    simpa using (monomial_single_add (n := (0 : Fin 1)) (e := n) (s := 0) (a := c))
  rw [hm]
  simp [unaryDiagonal, mul_pow, Algebra.smul_def, map_pow]
  ring

theorem unaryDiagonal_homogeneous (a : ℚ) (n : ℕ) (p : UnaryH n) :
    unaryDiagonal a p = a ^ n • (p : MvPolynomial (Fin 1) ℚ) := by
  rw [unary_homogeneous_eq n p, unaryDiagonal_monomial]

/-- The actual untwisted axis character is the inverse first diagonal entry to degree n. -/
theorem lineScalar_integralAction_diagonal (n : ℕ) (ε : ℤˣ × ℤˣ) (p : H n) :
    unaryScalarEquiv n (lineEval n (PolynomialGLAction.integralAction n 0 (diagonalHom ε) p)) =
      unitScalar ε.1⁻¹ ^ n * unaryScalarEquiv n (lineEval n p) := by
  change (_ : MvPolynomial (Fin 1) ℚ).coeff (Finsupp.single (0 : Fin 1) n) = _
  rw [lineEval_integralAction_diagonal, unaryDiagonal_homogeneous, coeff_smul]
  rfl

theorem binaryDiagonal_monomial (a b : ℚ) (r s : ℕ) :
    binaryDiagonal a b (X 0 ^ r * X 1 ^ s) =
      (a ^ r * b ^ s) • (X 0 ^ r * X 1 ^ s) := by
  simp [binaryDiagonal, mul_pow, Algebra.smul_def, map_mul, map_pow]
  ring

end TernaryPoly.RadicalCoinvariantAlgebra
