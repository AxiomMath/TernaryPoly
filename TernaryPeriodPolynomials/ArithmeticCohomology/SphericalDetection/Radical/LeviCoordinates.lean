module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.LeviPolynomialSubstitution

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The Levi action on a plane-radical one-cochain includes inverse conjugation of its input. -/
def planeRadicalLeviPair (matrix : Binary.GL2) (pair : Fin 2 → Poly) (coordinate : Fin 2) : Poly :=
  ∑ index : Fin 2, C (matrix⁻¹.val index coordinate) * action (-1) (planeLevi matrix 1) (pair index)

/-- The lower-radical inputs transform by the opposite binary matrix. -/
def lowerRadicalLeviPair (matrix : Binary.GL2) (pair : Fin 2 → Poly) (coordinate : Fin 2) : Poly :=
  ∑ index : Fin 2, C (matrix.val coordinate index) * action (-1) (planeLevi matrix 1) (pair index)

theorem pderiv_action_planeLevi_binary (exponent : ℤ) (matrix : Binary.GL2)
    (coordinate : Fin 2) (polynomial : Poly) :
    pderiv coordinate.castSucc (action exponent (planeLevi matrix 1) polynomial) =
      ∑ index : Fin 2, C (matrix⁻¹.val index coordinate) *
        action exponent (planeLevi matrix 1) (pderiv index.castSucc polynomial) := by
  simp only [action_apply, Derivation.map_smul, planeLevi_inverse, inv_one, planeLevi_value, Units.val_one]
  change determinantCharacter exponent (planeLevi matrix 1) •
    pderiv coordinate.castSucc (substitute (planeBlock matrix⁻¹.val 1) polynomial) = _
  rw [pderiv_substitute_planeBlock_binary, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp only [Algebra.smul_def]
  ring

theorem pderiv_action_planeLevi_third (exponent : ℤ) (matrix : Binary.GL2) (polynomial : Poly) :
    pderiv 2 (action exponent (planeLevi matrix 1) polynomial) =
      action exponent (planeLevi matrix 1) (pderiv 2 polynomial) := by
  simp only [action_apply, Derivation.map_smul, planeLevi_inverse, inv_one, planeLevi_value, Units.val_one]
  change determinantCharacter exponent (planeLevi matrix 1) •
    pderiv 2 (substitute (planeBlock matrix⁻¹.val 1) polynomial) = _
  rw [pderiv_substitute_planeBlock_third, C_1, one_mul]

theorem action_planeLevi_mul_third (exponent : ℤ) (matrix : Binary.GL2) (polynomial : Poly) :
    action exponent (planeLevi matrix 1) (X 2 * polynomial) =
      X 2 * action exponent (planeLevi matrix 1) polynomial := by
  simp only [action_apply, planeLevi_inverse, inv_one, planeLevi_value, Units.val_one, map_mul, substitute_X]
  change determinantCharacter exponent (planeLevi matrix 1) •
    (linearForm (planeBlock matrix⁻¹.val 1) 2 * substitute (planeBlock matrix⁻¹.val 1) polynomial) = _
  rw [planeBlock_linearForm_third, C_1, one_mul, mul_smul_comm]

theorem planeRadicalLeviPair_gradient (matrix : Binary.GL2) (polynomial : Binary.Poly)
    (coordinate : Fin 2) :
    planeRadicalLeviPair matrix
      (fun index => pderiv index.castSucc (binaryPolynomialLift polynomial)) coordinate =
      pderiv coordinate.castSucc (binaryPolynomialLift (Binary.action (-1) matrix polynomial)) := by
  rw [planeRadicalLeviPair, ← pderiv_action_planeLevi_binary, action_planeLevi_lift]
  simp only [Units.val_one, one_zpow, one_smul]

theorem planeRadicalLeviPair_boundary (matrix : Binary.GL2) (polynomial : Poly)
    (coordinate : Fin 2) :
    planeRadicalLeviPair matrix (fun index => X 2 * pderiv index.castSucc polynomial) coordinate =
      X 2 * pderiv coordinate.castSucc (action (-1) (planeLevi matrix 1) polynomial) := by
  dsimp only [planeRadicalLeviPair]
  rw [pderiv_action_planeLevi_binary, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [action_planeLevi_mul_third]
  ring

theorem planeRadicalLeviPair_add (matrix : Binary.GL2) (first second : Fin 2 → Poly)
    (coordinate : Fin 2) :
    planeRadicalLeviPair matrix (first + second) coordinate =
      planeRadicalLeviPair matrix first coordinate + planeRadicalLeviPair matrix second coordinate := by
  simp [planeRadicalLeviPair, mul_add, Finset.sum_add_distrib]

theorem planeRadicalLeviPair_normal (matrix : Binary.GL2) (polynomial : Binary.Poly)
    (potential : Poly) (coordinate : Fin 2) :
    planeRadicalLeviPair matrix (fun index =>
      pderiv index.castSucc (binaryPolynomialLift polynomial) + X 2 * pderiv index.castSucc potential) coordinate =
      pderiv coordinate.castSucc (binaryPolynomialLift (Binary.action (-1) matrix polynomial)) +
        X 2 * pderiv coordinate.castSucc (action (-1) (planeLevi matrix 1) potential) := by
  have addition := planeRadicalLeviPair_add matrix
    (fun index => pderiv index.castSucc (binaryPolynomialLift polynomial))
    (fun index => X 2 * pderiv index.castSucc potential) coordinate
  rw [planeRadicalLeviPair_gradient, planeRadicalLeviPair_boundary] at addition
  exact addition

theorem binary_det_smul_inverse (matrix : Binary.GL2) :
    matrix.val.det • matrix⁻¹.val = !![matrix.val 1 1, -matrix.val 0 1;
      -matrix.val 1 0, matrix.val 0 0] := by
  have equation := congrArg (fun other => matrix.inv * other) (Matrix.mul_adjugate matrix.val)
  rw [← Matrix.mul_assoc, matrix.inv_val, one_mul, Matrix.mul_smul, mul_one] at equation
  exact equation.symm.trans (Matrix.adjugate_fin_two matrix.val)

/-- The determinant twist in the coefficient action cancels in the lower contraction. -/
theorem lowerRadicalLeviPair_contraction (matrix : Binary.GL2) (pair : Fin 2 → Poly) :
    lowerRadicalContraction (lowerRadicalLeviPair matrix pair 0) (lowerRadicalLeviPair matrix pair 1) =
      substitute (planeBlock matrix⁻¹.val 1) (lowerRadicalContraction (pair 0) (pair 1)) := by
  have adjugate := binary_det_smul_inverse matrix
  have entry00 := congrArg (fun other : Matrix (Fin 2) (Fin 2) ℂ => other 0 0) adjugate
  have entry01 := congrArg (fun other : Matrix (Fin 2) (Fin 2) ℂ => other 0 1) adjugate
  have entry10 := congrArg (fun other : Matrix (Fin 2) (Fin 2) ℂ => other 1 0) adjugate
  have entry11 := congrArg (fun other : Matrix (Fin 2) (Fin 2) ℂ => other 1 1) adjugate
  change matrix.val.det * matrix⁻¹.val 0 0 = matrix.val 1 1 at entry00
  change matrix.val.det * matrix⁻¹.val 0 1 = -matrix.val 0 1 at entry01
  change matrix.val.det * matrix⁻¹.val 1 0 = -matrix.val 1 0 at entry10
  change matrix.val.det * matrix⁻¹.val 1 1 = matrix.val 0 0 at entry11
  have det_nonzero : matrix.val.det ≠ 0 := (GeneralLinearGroup.det matrix).ne_zero
  have scalar_eq : determinantCharacter (-1) (planeLevi matrix 1) = matrix.val.det⁻¹ := by
    rw [planeLevi_determinantCharacter]
    change matrix.val.det ^ (-1 : ℤ) * (1 : ℂ) ^ (-1 : ℤ) = _
    simp
  have inv00 : matrix⁻¹.val 0 0 = matrix.val.det⁻¹ * matrix.val 1 1 := by
    rw [← entry00, ← mul_assoc, inv_mul_cancel₀ det_nonzero, one_mul]
  have inv01 : matrix⁻¹.val 0 1 = -(matrix.val.det⁻¹ * matrix.val 0 1) := by
    calc
      _ = matrix.val.det⁻¹ * (matrix.val.det * matrix⁻¹.val 0 1) := by
        rw [← mul_assoc, inv_mul_cancel₀ det_nonzero, one_mul]
      _ = _ := by rw [entry01, mul_neg]
  have inv10 : matrix⁻¹.val 1 0 = -(matrix.val.det⁻¹ * matrix.val 1 0) := by
    calc
      _ = matrix.val.det⁻¹ * (matrix.val.det * matrix⁻¹.val 1 0) := by
        rw [← mul_assoc, inv_mul_cancel₀ det_nonzero, one_mul]
      _ = _ := by rw [entry10, mul_neg]
  have inv11 : matrix⁻¹.val 1 1 = matrix.val.det⁻¹ * matrix.val 0 0 := by
    rw [← entry11, ← mul_assoc, inv_mul_cancel₀ det_nonzero, one_mul]
  simp only [lowerRadicalContraction, lowerRadicalLeviPair, Fin.sum_univ_two,
    action_apply, scalar_eq, planeLevi_inverse, inv_one, planeLevi_value, Units.val_one,
    map_sub, map_mul, substitute_X, linearForm, planeBlock, Fin.sum_univ_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    Matrix.empty_val', C_0, zero_mul, add_zero,
    inv00, inv01, inv10, inv11, map_neg, map_mul, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  ring

theorem lowerRadicalLeviPair_binary (matrix : Binary.GL2) (pair : Fin 2 → Poly)
    (polynomial : Binary.Poly)
    (coordinate : lowerRadicalContraction (pair 0) (pair 1) = binaryPolynomialLift polynomial) :
    lowerRadicalContraction (lowerRadicalLeviPair matrix pair 0) (lowerRadicalLeviPair matrix pair 1) =
      binaryPolynomialLift (Binary.action 0 matrix polynomial) := by
  rw [lowerRadicalLeviPair_contraction, coordinate, substitute_planeBlock_lift]
  simp [Binary.action_apply, Binary.determinantCharacter]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
