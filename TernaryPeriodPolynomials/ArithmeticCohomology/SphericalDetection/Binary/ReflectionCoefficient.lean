module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeReflection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryReflection_inverse : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
  apply inv_eq_of_mul_eq_one_left
  simpa only [pow_two] using UpperHalfPlane.J_sq

theorem binaryReflection_normalizingFactor (exponent : ℂ) :
    normPower (GeneralLinearGroup.det (atInfinity UpperHalfPlane.J)) exponent = 1 := by
  rw [binary_normalizingFactor_eq]
  norm_num [UpperHalfPlane.val_J, Matrix.det_fin_two]

theorem binaryReflection_substitute_negative :
    Binary.substitute (GeneralLinearGroup.map (algebraMap ℝ ℂ) UpperHalfPlane.J).val binaryNegativeCoordinate =
      -binaryPositiveCoordinate := by
  simp [binaryNegativeCoordinate, binaryPositiveCoordinate, Binary.substitute, Binary.linearForm,
    UpperHalfPlane.val_J, Fin.sum_univ_two]
  ring

theorem binaryCoefficient_reflection_first {degree : ℕ} (odd : Odd degree) :
    binaryCoefficient degree UpperHalfPlane.J (binaryWeightBasis (degree + 1) 0) =
      -binaryWeightBasis (degree + 1) (Fin.last (degree + 1)) := by
  have determinant : (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) UpperHalfPlane.J)).val = -1 := by
    norm_num [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.map_apply, UpperHalfPlane.val_J, Matrix.det_fin_two]
  have even : Even (degree + 1) := by
    obtain ⟨index, rfl⟩ := odd
    exact ⟨index + 1, by omega⟩
  apply Subtype.ext
  simp only [binaryCoefficient, Binary.homogeneousAction_coe, Binary.action_apply, Binary.determinantCharacter,
    MonoidHom.coe_mk, OneHom.coe_mk, determinant, ← map_inv, binaryReflection_inverse,
    binaryWeightBasis_coe, Fin.val_zero, pow_zero, Nat.sub_zero, one_mul, Fin.val_last, Nat.sub_self, mul_one,
    map_pow, binaryReflection_substitute_negative, Submodule.coe_neg]
  rw [even.neg_pow]
  norm_num

theorem binaryHilbertOperator_reflection_supported_first (cusp : CuspidalRepresentation)
    {degree : ℕ} (odd : Odd degree) (vector : Fin (degree + 2) → cusp.H)
    (support : ∀ position : Fin (degree + 1), vector position.succ = 0) :
    binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) UpperHalfPlane.J vector (Fin.last (degree + 1)) =
      -cusp.π (atInfinity UpperHalfPlane.J) (vector 0) := by
  rw [binaryHilbertOperator_apply, binaryReflection_normalizingFactor, one_smul]
  rw [Fin.sum_univ_succ]
  have tail : ∑ position : Fin (degree + 1),
      (binaryWeightBasis (degree + 1)).coord (Fin.last (degree + 1))
        (binaryCoefficient degree UpperHalfPlane.J (binaryWeightBasis (degree + 1) position.succ)) •
      cusp.π (atInfinity UpperHalfPlane.J) (vector position.succ) = 0 := by
    simp only [support, map_zero, smul_zero, Finset.sum_const_zero]
  rw [tail, add_zero, binaryCoefficient_reflection_first odd, map_neg, Module.Basis.coord_apply]
  simp

end TernaryPeriodPolynomials.SphericalDetection.Helpers
