module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantDiagonal

@[expose] public section

open MvPolynomial Matrix

noncomputable section
namespace TernaryPoly.RadicalCoinvariantAlgebra
open RelativeStabilizerParameters RelativeStabilizerMatrices

/-- Literal inverse of the actual block-diagonal plane Levi matrix. -/
theorem planeLevi_inv (A : GL2) : (planeElement A 0)⁻¹ = planeElement A⁻¹ 0 := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, planeElement_val, planeElement_val]
  have hA : A.val * (A⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [planeMatrix, Fin.sum_univ_three]
  all_goals
    first
    | simpa [Matrix.mul_apply, Fin.sum_univ_two]
        using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hA
    | simpa [Matrix.mul_apply, Fin.sum_univ_two]
        using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hA
    | simpa [Matrix.mul_apply, Fin.sum_univ_two]
        using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hA
    | simpa [Matrix.mul_apply, Fin.sum_univ_two]
        using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) hA

/-- Literal inverse of the actual block-diagonal line Levi matrix. -/
theorem lineLevi_inv (ε : ℤˣ) (D : GL2) :
    (lineElement ε 0 D)⁻¹ = lineElement ε⁻¹ 0 D⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, lineElement_val, lineElement_val]
  have hD : D.val * (D⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  ext i j
  rw [Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [lineMatrix, Fin.sum_univ_three]
  all_goals
    first
    | simpa [Matrix.mul_apply, Fin.sum_univ_two]
        using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hD
    | simpa [Matrix.mul_apply, Fin.sum_univ_two]
        using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hD
    | simpa [Matrix.mul_apply, Fin.sum_univ_two]
        using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hD
    | simpa [Matrix.mul_apply, Fin.sum_univ_two]
        using congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) hD

def binaryMatrixSubst (M : Matrix (Fin 2) (Fin 2) ℚ) :
    MvPolynomial (Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 2) ℚ :=
  bind₁ fun i => ∑ j, C (M i j) * X j

theorem planeEval_plane_substitute (A : GL2) (p : Poly) :
    planeEvalAlg (PolynomialGLAction.substitute
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (planeElement A 0)).val p) =
    binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) A).val (planeEvalAlg p) := by
  have h : planeEvalAlg.comp (PolynomialGLAction.substitute
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (planeElement A 0)).val) =
      (binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) A).val).comp planeEvalAlg := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [planeEvalAlg, PolynomialGLAction.substitute, PolynomialGLAction.linearForm,
        GeneralLinearGroup.map_apply, Matrix.map, planeMatrix, binaryMatrixSubst,
        Fin.sum_univ_three, Fin.sum_univ_two]
  exact DFunLike.congr_fun h p

theorem lineEval_line_substitute (ε : ℤˣ) (D : GL2) (p : Poly) :
    lineEvalAlg (PolynomialGLAction.substitute
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineElement ε 0 D)).val p) =
    unaryDiagonal (unitScalar ε) (lineEvalAlg p) := by
  have h : lineEvalAlg.comp (PolynomialGLAction.substitute
      (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineElement ε 0 D)).val) =
      (unaryDiagonal (unitScalar ε)).comp lineEvalAlg := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [lineEvalAlg, PolynomialGLAction.substitute, PolynomialGLAction.linearForm,
        Matrix.map, lineMatrix, unaryDiagonal, unitScalar, Fin.sum_univ_three]
  exact DFunLike.congr_fun h p

/-- Evaluation gives the actual inverse-substitution plane Levi action, for arbitrary GL₂. -/
theorem planeEval_Levi (n : ℕ) (A : GL2) (p : H n) :
    (planeEval n (PolynomialGLAction.integralAction n 0 (planeElement A 0) p) :
      MvPolynomial (Fin 2) ℚ) =
    binaryMatrixSubst (GeneralLinearGroup.map (Int.castRingHom ℚ) A⁻¹).val (planeEval n p) := by
  rw [planeEval_coe, PolynomialGLAction.integralAction_coe, PolynomialGLAction.action_apply]
  simp only [PolynomialGLAction.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    zpow_zero, one_smul]
  rw [← map_inv, planeLevi_inv, planeEval_plane_substitute]
  rfl

/-- Evaluation gives the actual axis action of every line Levi block. -/
theorem lineEval_Levi (n : ℕ) (ε : ℤˣ) (D : GL2) (p : H n) :
    (lineEval n (PolynomialGLAction.integralAction n 0 (lineElement ε 0 D) p) :
      MvPolynomial (Fin 1) ℚ) =
    unaryDiagonal (unitScalar ε⁻¹) (lineEval n p) := by
  rw [lineEval_coe, PolynomialGLAction.integralAction_coe, PolynomialGLAction.action_apply]
  simp only [PolynomialGLAction.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    zpow_zero, one_smul]
  rw [← map_inv, lineLevi_inv, lineEval_line_substitute]
  rfl

/-- The lower line-Levi block does not act on the untwisted axis quotient. -/
theorem lineScalar_Levi (n : ℕ) (ε : ℤˣ) (D : GL2) (p : H n) :
    unaryScalarEquiv n (lineEval n (PolynomialGLAction.integralAction n 0 (lineElement ε 0 D) p)) =
      unitScalar ε⁻¹ ^ n * unaryScalarEquiv n (lineEval n p) := by
  change (_ : MvPolynomial (Fin 1) ℚ).coeff (Finsupp.single (0 : Fin 1) n) = _
  rw [lineEval_Levi, unaryDiagonal_homogeneous, coeff_smul]
  rfl

/-- Actual block multiplication identifies the plane radical conjugation representation. -/
theorem planeLevi_radical_commute (A : GL2) (u : Fin 2 → ℤ) :
    planeElement A 0 * planeElement 1 u =
      planeElement 1 (A.val.mulVec u) * planeElement A 0 := by
  apply Units.ext
  simp only [Units.val_mul, planeElement_val]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [planeMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]

/-- The genuine plane Levi acts on the two radical parameters by its GL₂ matrix. -/
theorem planeLevi_radical_conjugate (A : GL2) (u : Fin 2 → ℤ) :
    planeElement A 0 * planeElement 1 u * (planeElement A 0)⁻¹ =
      planeElement 1 (A.val.mulVec u) := by
  rw [planeLevi_radical_commute, mul_assoc, mul_inv_cancel, mul_one]

/-- The dual top-exterior character of that actual radical action. -/
def planeLeviRootDual (A : GL2) : ℚ := (A.val.det : ℚ)⁻¹

end TernaryPoly.RadicalCoinvariantAlgebra
