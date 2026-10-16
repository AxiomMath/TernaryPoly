module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.AffineCoefficientDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binarySymmetricSection_det (point : UpperHalfPlane) :
    (GeneralLinearGroup.det (binarySymmetricSection point)).val = 1 := point.toSL2R.property

theorem binaryRotations_det (angle : Circle) :
    (GeneralLinearGroup.det (binaryRotations angle)).val = 1 := binaryRotationMatrix_det angle

theorem binary_stabilizer_det_one_rotation (matrix : BinaryRealGL)
    (determinant : (GeneralLinearGroup.det matrix).val = 1)
    (stabilizes : matrix • UpperHalfPlane.I = UpperHalfPlane.I) :
    ∃ angle : Circle, matrix = binaryRotations angle := by
  obtain ⟨unit, angle, positive, decomposition⟩ :=
    binary_stabilizer_positive_decomposition matrix (by rw [determinant]; norm_num) stabilizes
  have square : unit.val ^ 2 = 1 := by
    rw [decomposition, map_mul, Units.val_mul, GeneralLinearGroup.det_scalar,
      Units.val_pow_eq_pow_val, Fintype.card_fin, binaryRotations_det, mul_one] at determinant
    exact determinant
  have unit_one : unit = 1 := Units.ext (by change unit.val = 1; nlinarith)
  exact ⟨angle, by simpa only [unit_one, map_one, one_mul] using decomposition⟩

theorem binary_det_one_section_rotation (matrix : BinaryRealGL)
    (determinant : (GeneralLinearGroup.det matrix).val = 1) (point : UpperHalfPlane) :
    ∃ angle : Circle, matrix * binarySymmetricSection point =
      binarySymmetricSection (matrix • point) * binaryRotations angle := by
  let residual := (binarySymmetricSection (matrix • point))⁻¹ * matrix * binarySymmetricSection point
  have residual_det : (GeneralLinearGroup.det residual).val = 1 := by
    simp only [residual, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      binarySymmetricSection_det, determinant, inv_one, one_mul]
  have residual_fixes : residual • UpperHalfPlane.I = UpperHalfPlane.I := by
    simp only [residual, mul_smul, binarySymmetricSection_smul]
    exact (congrArg (fun value => (binarySymmetricSection (matrix • point))⁻¹ • value)
      (binarySymmetricSection_smul (matrix • point)).symm).trans
      (inv_smul_smul (binarySymmetricSection (matrix • point)) UpperHalfPlane.I)
  obtain ⟨angle, equality⟩ := binary_stabilizer_det_one_rotation residual residual_det residual_fixes
  refine ⟨angle, ?_⟩
  rw [← equality]
  simp only [residual, ← mul_assoc, mul_inv_cancel, one_mul]

theorem binarySymmetricSection_denom (point : UpperHalfPlane) (argument : ℂ) :
    UpperHalfPlane.denom (binarySymmetricSection point) argument = 1 / (Real.sqrt point.im : ℂ) := by
  simp only [UpperHalfPlane.denom]
  rw [← binaryUpperSectionMatrix_coe]
  simp [binaryUpperSectionMatrix]

theorem binaryRotations_denom_I (angle : Circle) :
    UpperHalfPlane.denom (binaryRotations angle) Complex.I = (angle : ℂ) := by
  apply Complex.ext <;> simp [UpperHalfPlane.denom, binaryRotations, binaryRotation]

def binaryIwasawaPhase (matrix : BinaryRealGL) (point : UpperHalfPlane) : Circle :=
  complexDirection (UpperHalfPlane.denom matrix point) (UpperHalfPlane.denom_ne_zero matrix point)

theorem binary_det_one_sqrt_im (matrix : BinaryRealGL)
    (determinant : (GeneralLinearGroup.det matrix).val = 1) (point : UpperHalfPlane) :
    Real.sqrt (matrix • point).im = Real.sqrt point.im / ‖UpperHalfPlane.denom matrix point‖ := by
  rw [UpperHalfPlane.im_smul_eq_div_normSq, determinant, abs_one, one_mul,
    Complex.normSq_eq_norm_sq, Real.sqrt_div point.im_pos.le, Real.sqrt_sq (norm_nonneg _)]

theorem binary_det_one_section_phase (matrix : BinaryRealGL)
    (determinant : (GeneralLinearGroup.det matrix).val = 1) (point : UpperHalfPlane) :
    matrix * binarySymmetricSection point =
      binarySymmetricSection (matrix • point) * binaryRotations (binaryIwasawaPhase matrix point) := by
  obtain ⟨angle, equality⟩ := binary_det_one_section_rotation matrix determinant point
  have denominator := congrArg (fun element => UpperHalfPlane.denom element Complex.I) equality
  have cocycle_first := UpperHalfPlane.denom_cocycle_σ matrix (binarySymmetricSection point) UpperHalfPlane.I
  have cocycle_second := UpperHalfPlane.denom_cocycle_σ (binarySymmetricSection (matrix • point))
    (binaryRotations angle) UpperHalfPlane.I
  simp only [binarySymmetricSection_smul, binaryRotations_smul_I] at cocycle_first cocycle_second
  simp only [UpperHalfPlane.σ, binarySymmetricSection_det, binaryRotations_det] at cocycle_first cocycle_second
  norm_num at cocycle_first cocycle_second
  rw [cocycle_first, cocycle_second, binarySymmetricSection_denom, binarySymmetricSection_denom,
    binaryRotations_denom_I] at denominator
  have root : (Real.sqrt (matrix • point).im : ℂ) =
      (Real.sqrt point.im : ℂ) / (‖UpperHalfPlane.denom matrix point‖ : ℂ) := by
    exact_mod_cast binary_det_one_sqrt_im matrix determinant point
  have root_nonzero : (Real.sqrt point.im : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr point.im_pos)
  have norm_nonzero : (‖UpperHalfPlane.denom matrix point‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (UpperHalfPlane.denom_ne_zero matrix point)
  have angle_eq : angle = binaryIwasawaPhase matrix point := by
    apply Subtype.ext
    change (angle : ℂ) = UpperHalfPlane.denom matrix point / (‖UpperHalfPlane.denom matrix point‖ : ℂ)
    rw [root] at denominator
    field_simp at denominator ⊢
    simpa only [mul_comm] using denominator.symm
  rwa [angle_eq] at equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
