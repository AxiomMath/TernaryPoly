module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cusp.CasimirOperator

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cuspLowering_raising_of_eigenvectors (cusp : CuspidalRepresentation)
    (weight eigenvalue : ℂ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * weight) • vector)
    (casimir : cuspCasimirOperator cusp vector = eigenvalue • vector) :
    cuspLoweringOperator cusp (cuspRaisingOperator cusp vector) =
      (eigenvalue - weight ^ 2 - 2 * weight) • vector := by
  have product := congrArg (fun operator : Module.End ℂ cusp.smooth => operator vector)
    (cuspLowering_raising_product cusp)
  change cuspLoweringOperator cusp (cuspRaisingOperator cusp vector) =
    cuspCasimirOperator cusp vector + cuspRotationOperator cusp (cuspRotationOperator cusp vector) +
      (2 * Complex.I) • cuspRotationOperator cusp vector at product
  rw [casimir, rotation, map_smul, rotation, smul_smul, smul_smul] at product
  have squared : (Complex.I * weight) * (Complex.I * weight) = -(weight ^ 2) := by
    calc
      _ = (Complex.I * Complex.I) * weight ^ 2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  have linear : (2 * Complex.I) * (Complex.I * weight) = -(2 * weight) := by
    calc
      _ = 2 * (Complex.I * Complex.I) * weight := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [squared, linear] at product
  rw [product]
  module

theorem cuspRaising_lowering_of_eigenvectors (cusp : CuspidalRepresentation)
    (weight eigenvalue : ℂ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * weight) • vector)
    (casimir : cuspCasimirOperator cusp vector = eigenvalue • vector) :
    cuspRaisingOperator cusp (cuspLoweringOperator cusp vector) =
      (eigenvalue - weight ^ 2 + 2 * weight) • vector := by
  have product := congrArg (fun operator : Module.End ℂ cusp.smooth => operator vector)
    (cuspRaising_lowering_product cusp)
  change cuspRaisingOperator cusp (cuspLoweringOperator cusp vector) =
    cuspCasimirOperator cusp vector + cuspRotationOperator cusp (cuspRotationOperator cusp vector) -
      (2 * Complex.I) • cuspRotationOperator cusp vector at product
  rw [casimir, rotation, map_smul, rotation, smul_smul, smul_smul] at product
  have squared : (Complex.I * weight) * (Complex.I * weight) = -(weight ^ 2) := by
    calc
      _ = (Complex.I * Complex.I) * weight ^ 2 := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  have linear : (2 * Complex.I) * (Complex.I * weight) = -(2 * weight) := by
    calc
      _ = 2 * (Complex.I * Complex.I) * weight := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [squared, linear] at product
  rw [product]
  module

theorem cuspCasimir_eigenvalue_real (cusp : CuspidalRepresentation)
    (eigenvalue : ℂ) (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (eigenvector : cuspCasimirOperator cusp vector = eigenvalue • vector) : eigenvalue.im = 0 := by
  have symmetric := cuspCasimirOperator_symmetric cusp vector vector
  rw [eigenvector, Submodule.coe_smul, inner_smul_left, inner_smul_right,
    inner_self_eq_norm_sq_to_K] at symmetric
  have vector_nonzero : vector.val ≠ 0 := by intro zero; exact nonzero (Subtype.ext zero)
  have norm_nonzero : (‖vector.val‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr vector_nonzero)
  have conjugate := mul_right_cancel₀ (pow_ne_zero 2 norm_nonzero) symmetric
  have imaginary := congrArg Complex.im conjugate
  simp only [Complex.conj_im] at imaginary
  linarith

theorem cuspRaising_norm_sq_of_eigenvectors (cusp : CuspidalRepresentation)
    (weight eigenvalue : ℝ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (casimir : cuspCasimirOperator cusp vector = (eigenvalue : ℂ) • vector) :
    ‖(cuspRaisingOperator cusp vector).val‖ ^ 2 =
      (weight ^ 2 + 2 * weight - eigenvalue) * ‖vector.val‖ ^ 2 := by
  have adjoint := cuspRaising_lowering_adjoint cusp vector (cuspRaisingOperator cusp vector)
  rw [cuspLowering_raising_of_eigenvectors cusp weight eigenvalue vector rotation casimir,
    Submodule.coe_smul, inner_smul_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at adjoint
  apply Complex.ofReal_injective
  push_cast
  linear_combination adjoint

theorem cuspLowering_norm_sq_of_eigenvectors (cusp : CuspidalRepresentation)
    (weight eigenvalue : ℝ) (vector : cusp.smooth)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (casimir : cuspCasimirOperator cusp vector = (eigenvalue : ℂ) • vector) :
    ‖(cuspLoweringOperator cusp vector).val‖ ^ 2 =
      (weight ^ 2 - 2 * weight - eigenvalue) * ‖vector.val‖ ^ 2 := by
  have adjoint := cuspLowering_raising_adjoint cusp vector (cuspLoweringOperator cusp vector)
  rw [cuspRaising_lowering_of_eigenvectors cusp weight eigenvalue vector rotation casimir,
    Submodule.coe_smul, inner_smul_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at adjoint
  apply Complex.ofReal_injective
  push_cast
  linear_combination adjoint

theorem cuspCasimir_bound_of_weight (cusp : CuspidalRepresentation)
    (weight eigenvalue : ℝ) (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (casimir : cuspCasimirOperator cusp vector = (eigenvalue : ℂ) • vector) :
    eigenvalue ≤ weight ^ 2 - 2 * |weight| := by
  have vector_nonzero : vector.val ≠ 0 := by intro zero; exact nonzero (Subtype.ext zero)
  have norm_sq_positive : 0 < ‖vector.val‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr vector_nonzero)
  have raising := cuspRaising_norm_sq_of_eigenvectors cusp weight eigenvalue vector rotation casimir
  have lowering := cuspLowering_norm_sq_of_eigenvectors cusp weight eigenvalue vector rotation casimir
  have raising_nonnegative : 0 ≤ weight ^ 2 + 2 * weight - eigenvalue := by
    apply nonneg_of_mul_nonneg_left (by rw [← raising]; positivity) norm_sq_positive
  have lowering_nonnegative : 0 ≤ weight ^ 2 - 2 * weight - eigenvalue := by
    apply nonneg_of_mul_nonneg_left (by rw [← lowering]; positivity) norm_sq_positive
  rcases le_total 0 weight with positive | negative
  · rw [abs_of_nonneg positive]
    linarith
  · rw [abs_of_nonpos negative]
    linarith

theorem cuspCasimir_eq_of_lowering_zero (cusp : CuspidalRepresentation)
    (weight eigenvalue : ℝ) (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (casimir : cuspCasimirOperator cusp vector = (eigenvalue : ℂ) • vector)
    (lowest : cuspLoweringOperator cusp vector = 0) : eigenvalue = weight * (weight - 2) := by
  have norm_formula := cuspLowering_norm_sq_of_eigenvectors cusp weight eigenvalue vector rotation casimir
  rw [lowest, Submodule.coe_zero, norm_zero, zero_pow (by decide)] at norm_formula
  have vector_nonzero : vector.val ≠ 0 := by intro zero; exact nonzero (Subtype.ext zero)
  have norm_sq_nonzero : ‖vector.val‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr vector_nonzero)
  have coefficient_zero := (mul_eq_zero.mp norm_formula.symm).resolve_right norm_sq_nonzero
  nlinarith

theorem cuspCasimir_eq_of_raising_zero (cusp : CuspidalRepresentation)
    (weight eigenvalue : ℝ) (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector)
    (casimir : cuspCasimirOperator cusp vector = (eigenvalue : ℂ) • vector)
    (highest : cuspRaisingOperator cusp vector = 0) : eigenvalue = weight * (weight + 2) := by
  have norm_formula := cuspRaising_norm_sq_of_eigenvectors cusp weight eigenvalue vector rotation casimir
  rw [highest, Submodule.coe_zero, norm_zero, zero_pow (by decide)] at norm_formula
  have vector_nonzero : vector.val ≠ 0 := by intro zero; exact nonzero (Subtype.ext zero)
  have norm_sq_nonzero : ‖vector.val‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr vector_nonzero)
  have coefficient_zero := (mul_eq_zero.mp norm_formula.symm).resolve_right norm_sq_nonzero
  nlinarith

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
