module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SourceReconstruction

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryPointPower (degree : ℕ) (point : ℂ) : Binary.HomogeneousPoly degree :=
  ⟨(X 0 - C point * X 1) ^ degree, by
    change ((X 0 - C point * X 1) ^ degree : Binary.Poly).IsHomogeneous degree
    simpa only [one_mul] using
      ((isHomogeneous_X ℂ (0 : Fin 2)).sub ((isHomogeneous_X ℂ (1 : Fin 2)).C_mul point)).pow degree⟩

theorem binaryAffineInverse_substitute_negative (point : ℂ) (positive : 0 < point.im) :
    Binary.substitute
        (GeneralLinearGroup.map (algebraMap ℝ ℂ) (invertibleMatrix (binaryUpperSectionMatrix point)))⁻¹.val
        binaryNegativeCoordinate =
      C (1 / (Real.sqrt point.im : ℂ)) * (X 0 - C point * X 1) := by
  have root_ne : (Real.sqrt point.im : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr positive)
  have root_sq : (Real.sqrt point.im : ℂ) ^ 2 = (point.im : ℂ) := by
    exact_mod_cast Real.sq_sqrt positive.le
  have coefficient : (point.re : ℂ) / (Real.sqrt point.im : ℂ) +
      Complex.I * (Real.sqrt point.im : ℂ) = point / (Real.sqrt point.im : ℂ) := by
    field_simp
    linear_combination Complex.I * root_sq + Complex.re_add_im point
  rw [← map_inv, GeneralLinearGroup.val_map_apply, GeneralLinearGroup.coe_inv,
    invertibleMatrix_val _ (binaryUpperSectionMatrix_invertible point positive),
    binaryUpperSectionMatrix_inverse point positive]
  simp only [binaryNegativeCoordinate, Binary.substitute, map_sub, map_mul, bind₁_C_right,
    bind₁_X_right, Binary.linearForm, binaryUpperSectionInverse, Matrix.map_apply, Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, map_div₀,
    map_one, map_neg, map_zero, zero_mul, zero_add]
  change C (1 / (Real.sqrt point.im : ℂ)) * X 0 +
    -C ((point.re : ℂ) / (Real.sqrt point.im : ℂ)) * X 1 -
    C Complex.I * (C (Real.sqrt point.im : ℂ) * X 1) = _
  calc
    C (1 / (Real.sqrt point.im : ℂ)) * X (0 : Fin 2) +
        -C ((point.re : ℂ) / (Real.sqrt point.im : ℂ)) * X 1 -
        C Complex.I * (C (Real.sqrt point.im : ℂ) * X 1) =
        C (1 / (Real.sqrt point.im : ℂ)) * X 0 -
        C ((point.re : ℂ) / (Real.sqrt point.im : ℂ) + Complex.I * (Real.sqrt point.im : ℂ)) * X 1 := by
      simp only [map_add, map_mul]
      ring
    _ = C (1 / (Real.sqrt point.im : ℂ)) * (X 0 - C point * X 1) := by
      rw [coefficient]
      simp only [div_eq_mul_inv, map_mul, map_one]
      ring

theorem binaryCoefficient_affine_first (degree : ℕ) (point : ℂ) (positive : 0 < point.im) :
    binaryCoefficient degree (invertibleMatrix (binaryUpperSectionMatrix point))
        (binaryWeightBasis (degree + 1) 0) =
      ((1 / (Real.sqrt point.im : ℂ)) ^ (degree + 1)) • binaryPointPower (degree + 1) point := by
  have determinant : (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (invertibleMatrix (binaryUpperSectionMatrix point)))).val = 1 := by
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_map_apply,
      invertibleMatrix_val _ (binaryUpperSectionMatrix_invertible point positive)]
    change (Complex.ofRealHom.mapMatrix (binaryUpperSectionMatrix point)).det = 1
    rw [← Complex.ofRealHom.map_det, binaryUpperSectionMatrix_det point positive, map_one]
  apply Subtype.ext
  simp only [binaryCoefficient, Binary.homogeneousAction_coe, Binary.action_apply,
    Binary.determinantCharacter, MonoidHom.coe_mk, OneHom.coe_mk, determinant, _root_.one_zpow,
    binaryWeightBasis_coe, Fin.val_zero, pow_zero, Nat.sub_zero, one_mul,
    map_pow, binaryAffineInverse_substitute_negative point positive, mul_pow,
    Submodule.coe_smul, binaryPointPower, Algebra.smul_def]
  simp only [map_one, one_mul, algebraMap_eq]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
