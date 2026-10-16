module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.UnitaryCentral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryDetNormalizedMatrix (matrix : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt matrix.det)⁻¹ • matrix

theorem binaryDetNormalizedMatrix_det (matrix : Matrix (Fin 2) (Fin 2) ℝ)
    (positive : 0 < matrix.det) : (binaryDetNormalizedMatrix matrix).det = 1 := by
  rw [binaryDetNormalizedMatrix, Matrix.det_smul, Fintype.card_fin, inv_pow,
    Real.sq_sqrt positive.le, inv_mul_cancel₀ (ne_of_gt positive)]

theorem binaryDetNormalizedMatrix_one : binaryDetNormalizedMatrix 1 = 1 := by
  simp [binaryDetNormalizedMatrix]

theorem binaryDetNormalizedMatrix_recover (matrix : BinaryRealGL)
    (positive : 0 < matrix.val.det) :
    GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (Real.sqrt matrix.val.det)
      (ne_of_gt (Real.sqrt_pos.mpr positive))) *
        invertibleMatrix (binaryDetNormalizedMatrix matrix.val) = matrix := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_scalar,
    invertibleMatrix_val _ (by rw [binaryDetNormalizedMatrix_det _ positive]; norm_num)]
  ext row column
  simp only [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Units.val_mk0, binaryDetNormalizedMatrix, Matrix.smul_apply, smul_eq_mul]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr positive)), one_mul]

theorem cuspRotationWeight_positive_formula (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (vector : cusp.H) (weight : ℤ)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector)
    (matrix : BinaryRealGL) (positive : 0 < matrix.val.det) :
    cusp.π (atInfinity matrix) vector =
      binaryPhaseValue (invertibleMatrix (binaryDetNormalizedMatrix matrix.val)) Complex.I ^ weight •
        cuspAffineOrbitVector cusp vector
          ((invertibleMatrix (binaryDetNormalizedMatrix matrix.val) • UpperHalfPlane.I : UpperHalfPlane) : ℂ) := by
  have normalized_det :
      (GeneralLinearGroup.det (invertibleMatrix (binaryDetNormalizedMatrix matrix.val))).val = 1 := by
    change (invertibleMatrix (binaryDetNormalizedMatrix matrix.val)).val.det = 1
    rw [invertibleMatrix_val _ (by rw [binaryDetNormalizedMatrix_det _ positive]; norm_num),
      binaryDetNormalizedMatrix_det _ positive]
  have equality := cuspRotationWeight_affine_transform cusp vector weight rotation
    (invertibleMatrix (binaryDetNormalizedMatrix matrix.val)) normalized_det UpperHalfPlane.I
  simp only [UpperHalfPlane.coe_I, cuspAffineOrbitVector_I] at equality
  conv_lhs => rw [← binaryDetNormalizedMatrix_recover matrix positive]
  rw [atInfinity_mul, map_mul, Module.End.mul_apply,
    cuspUnitary_positive_scalar cusp spherical central_positive _ (Real.sqrt_pos.mpr positive)]
  exact equality

end TernaryPeriodPolynomials.SphericalDetection.Helpers
