module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.BinaryPeriodBoundary

@[expose] public section


open GeneralEisenstein Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryPointPower_mobius_substitution (degree : ℕ) (a b c d point : ℂ)
    (nonzero : c * point + d ≠ 0) :
    Binary.substitute !![d, -b; -c, a] (binaryPointPower degree point).val =
      ((c * point + d) ^ degree • binaryPointPower degree ((a * point + b) / (c * point + d))).val := by
  simp only [binaryPointPower, Submodule.coe_smul, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  rw [map_pow, map_pow, ← mul_pow]
  have coefficient : (C (c * point + d) : Binary.Poly) * C ((a * point + b) / (c * point + d)) =
      C (a * point + b) := by
    rw [← map_mul, mul_div_cancel₀ _ nonzero]
  have substitution : Binary.substitute !![d, -b; -c, a] (X 0 - C point * X 1) =
      C (c * point + d) * (X 0 - C ((a * point + b) / (c * point + d)) * X 1) := by
    rw [mul_sub, ← mul_assoc, coefficient]
    simp only [Binary.substitute, map_sub, map_mul, bind₁_C_right, bind₁_X_right,
      Binary.linearForm, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, map_neg, map_add]
    ring
  exact congrArg (fun polynomial : Binary.Poly => polynomial ^ degree) substitution

theorem arithmeticBinaryRep_pointPower (degree : ℕ) (twist : ℤ)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (point : UpperHalfPlane) :
    (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL matrix) (binaryPointPower degree point) =
      UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ matrix) point ^ degree •
        binaryPointPower degree ((SpecialLinearGroup.mapGL ℝ matrix • point : UpperHalfPlane) : ℂ) := by
  apply Subtype.ext
  rw [arithmeticBinaryRep_specialLinear_coe]
  have inverse : (matrix⁻¹).val.map (Int.castRingHom ℂ) =
      !![(matrix.val 1 1 : ℂ), -(matrix.val 0 1 : ℂ); -(matrix.val 1 0 : ℂ), (matrix.val 0 0 : ℂ)] := by
    rw [SpecialLinearGroup.SL2_inv_expl]
    ext row column
    fin_cases row <;> fin_cases column <;> norm_cast
  rw [inverse]
  have denominator : UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ matrix) point =
      (matrix.val 1 0 : ℂ) * (point : ℂ) + (matrix.val 1 1 : ℂ) := by
    simp [UpperHalfPlane.denom, SpecialLinearGroup.mapGL]
  have numerator : UpperHalfPlane.num (SpecialLinearGroup.mapGL ℝ matrix) point =
      (matrix.val 0 0 : ℂ) * (point : ℂ) + (matrix.val 0 1 : ℂ) := by
    simp [UpperHalfPlane.num, SpecialLinearGroup.mapGL]
  have positive : 0 < ((GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ matrix) : ℝˣ) : ℝ) := by
    simp
  rw [UpperHalfPlane.coe_smul_of_det_pos positive, numerator, denominator]
  apply binaryPointPower_mobius_substitution
  rw [← denominator]
  exact UpperHalfPlane.denom_ne_zero _ point

/-- The polynomial-valued holomorphic differential associated to a scalar cusp form. -/
def classicalBinaryForm {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (point : ℂ) : Binary.HomogeneousPoly degree :=
  form (UpperHalfPlane.ofComplex point) • binaryPointPower degree point

theorem classicalBinaryForm_coord_holomorphic {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (functional : Binary.HomogeneousPoly degree →ₗ[ℂ] ℂ) :
    DifferentiableOn ℂ (fun point => functional (classicalBinaryForm form degree point))
      UpperHalfPlane.upperHalfPlaneSet := by
  have holomorphic := UpperHalfPlane.mdifferentiable_iff.mp (CuspFormClass.holo form)
  simp only [classicalBinaryForm, map_smul, smul_eq_mul]
  intro point member
  exact (holomorphic point member).mul
    (binaryPointPower_functional_analytic degree functional point).differentiableAt.differentiableWithinAt

theorem classicalBinaryForm_modular {weight : ℤ}
    (form : CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range weight)
    (degree : ℕ) (weight_eq : weight = (degree : ℤ) + 2) (twist : ℤ)
    (matrix : SpecialLinearGroup (Fin 2) ℤ) (point : UpperHalfPlane) :
    (UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ matrix) point ^ 2)⁻¹ •
        classicalBinaryForm form degree ((SpecialLinearGroup.mapGL ℝ matrix • point : UpperHalfPlane) : ℂ) =
      (arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL matrix)
        (classicalBinaryForm form degree point) := by
  let denominator := UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ matrix) point
  let moved := (SpecialLinearGroup.mapGL ℝ matrix • point : UpperHalfPlane)
  have modular : form moved = denominator ^ weight * form point :=
    SlashInvariantForm.slash_action_eqn'' form
      (show SpecialLinearGroup.mapGL ℝ matrix ∈ (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range
        from ⟨matrix, rfl⟩) point
  have denominator_nonzero : denominator ≠ 0 := UpperHalfPlane.denom_ne_zero _ point
  have power : (denominator ^ 2)⁻¹ * denominator ^ weight = denominator ^ degree := by
    rw [weight_eq, zpow_add₀ denominator_nonzero, zpow_natCast, zpow_ofNat]
    field_simp
  have scalar : (denominator ^ 2)⁻¹ * (form moved) = form point * denominator ^ degree := by
    rw [modular, ← mul_assoc, power, mul_comm]
  have linear := map_smul ((arithmeticBinaryRep degree twist).ρ (SpecialLinearGroup.toGL matrix))
    (form point) (binaryPointPower degree point)
  change (denominator ^ 2)⁻¹ • classicalBinaryForm form degree moved = _
  simp only [classicalBinaryForm, UpperHalfPlane.ofComplex_apply]
  erw [linear]
  erw [arithmeticBinaryRep_pointPower]
  change (denominator ^ 2)⁻¹ • (form moved • binaryPointPower degree moved) =
    form point • (denominator ^ degree • binaryPointPower degree moved)
  rw [smul_smul, smul_smul, scalar]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
