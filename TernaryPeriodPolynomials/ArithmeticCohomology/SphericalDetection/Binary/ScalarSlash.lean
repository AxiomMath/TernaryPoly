module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarModularity

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspScalarWeightedRealization_det_one (cusp : CuspidalRepresentation)
    (halfWeight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (matrix : BinaryRealGL) (determinant : (GeneralLinearGroup.det matrix).val = 1)
    (point : UpperHalfPlane) :
    cuspScalarWeightedRealization cusp halfWeight vector (atInfinity matrix) point =
      UpperHalfPlane.denom matrix point ^ (2 * halfWeight) *
        cuspScalarWeightedRealization cusp halfWeight vector 1 ((matrix • point : UpperHalfPlane) : ℂ) := by
  have phase := cuspScalarAffineRealization_rotation cusp vector (2 * halfWeight) rotation 1
    matrix determinant point
  rw [one_mul] at phase
  have scalar_identity :
      cuspScalarAffineRealization cusp vector (atInfinity matrix) point =
        binaryPhaseValue matrix point ^ (2 * halfWeight) *
          cuspScalarAffineRealization cusp vector 1 ((matrix • point : UpperHalfPlane) : ℂ) := by
    rw [cuspScalarAffineRealization, binaryUpperSectionMatrix_coe, invertibleMatrix_coe,
      ← atInfinity_mul]
    exact phase
  simp only [cuspScalarWeightedRealization, Complex.real_smul]
  rw [scalar_identity]
  change _ = UpperHalfPlane.denom matrix point ^ (2 * halfWeight) *
    ((((matrix • point : UpperHalfPlane).im ^ halfWeight : ℝ) : ℂ) * _)
  rw [binary_weighted_phase_identity matrix determinant point halfWeight]
  have cancel : UpperHalfPlane.denom matrix point ^ (2 * halfWeight) *
      UpperHalfPlane.denom matrix point ^ (-2 * halfWeight) = 1 := by
    rw [← zpow_add₀ (UpperHalfPlane.denom_ne_zero matrix point)]
    convert zpow_zero (UpperHalfPlane.denom matrix point) using 1
    congr 1
    ring
  calc
    _ = (UpperHalfPlane.denom matrix point ^ (2 * halfWeight) *
        UpperHalfPlane.denom matrix point ^ (-2 * halfWeight)) *
        (((point.im ^ halfWeight : ℝ) : ℂ) *
          (binaryPhaseValue matrix point ^ (2 * halfWeight) *
            cuspScalarAffineRealization cusp vector 1 ((matrix • point : UpperHalfPlane) : ℂ))) := by
      rw [cancel, one_mul]
      rfl
    _ = _ := by ring

theorem binaryDetNormalized_smul (matrix : BinaryRealGL) (positive : 0 < matrix.val.det)
    (point : UpperHalfPlane) :
    invertibleMatrix (binaryDetNormalizedMatrix matrix.val) • point = matrix • point := by
  conv_rhs => rw [← binaryDetNormalizedMatrix_recover matrix positive]
  rw [mul_smul, UpperHalfPlane.glScalar_smul]

theorem binaryDetNormalized_denom (matrix : BinaryRealGL) (positive : 0 < matrix.val.det)
    (point : ℂ) :
    UpperHalfPlane.denom (invertibleMatrix (binaryDetNormalizedMatrix matrix.val)) point =
      (Real.sqrt matrix.val.det : ℂ)⁻¹ * UpperHalfPlane.denom matrix point := by
  have value : (invertibleMatrix (binaryDetNormalizedMatrix matrix.val)).val =
      binaryDetNormalizedMatrix matrix.val :=
    invertibleMatrix_val _ (by rw [binaryDetNormalizedMatrix_det _ positive]; norm_num)
  unfold UpperHalfPlane.denom
  rw [value]
  simp only [binaryDetNormalizedMatrix, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem cuspScalarWeightedRealization_det_normalize (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.smooth) (matrix : BinaryRealGL)
    (positive : 0 < matrix.val.det) (point : ℂ) :
    cuspScalarWeightedRealization cusp halfWeight vector (atInfinity matrix) point =
      cuspScalarWeightedRealization cusp halfWeight vector
        (atInfinity (invertibleMatrix (binaryDetNormalizedMatrix matrix.val))) point := by
  unfold cuspScalarWeightedRealization cuspScalarAffineRealization
  congr 1
  conv_lhs => rw [← binaryDetNormalizedMatrix_recover matrix positive]
  rw [atInfinity_mul, mul_assoc, atInfinity_scalar, cusp.central,
    central_positive _ (Real.sqrt_pos.mpr positive), one_mul]

theorem cuspScalarWeightedRealization_positive (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (matrix : BinaryRealGL) (positive : 0 < matrix.val.det) (point : UpperHalfPlane) :
    cuspScalarWeightedRealization cusp halfWeight vector (atInfinity matrix) point =
      (matrix.val.det : ℂ) ^ (-halfWeight) * UpperHalfPlane.denom matrix point ^ (2 * halfWeight) *
        cuspScalarWeightedRealization cusp halfWeight vector 1 ((matrix • point : UpperHalfPlane) : ℂ) := by
  have normalized_det :
      (GeneralLinearGroup.det (invertibleMatrix (binaryDetNormalizedMatrix matrix.val))).val = 1 := by
    change (invertibleMatrix (binaryDetNormalizedMatrix matrix.val)).val.det = 1
    rw [invertibleMatrix_val _ (by rw [binaryDetNormalizedMatrix_det _ positive]; norm_num),
      binaryDetNormalizedMatrix_det _ positive]
  rw [cuspScalarWeightedRealization_det_normalize cusp central_positive halfWeight vector matrix positive,
    cuspScalarWeightedRealization_det_one cusp halfWeight vector rotation _ normalized_det,
    binaryDetNormalized_smul matrix positive, binaryDetNormalized_denom matrix positive, mul_zpow]
  have power : ((Real.sqrt matrix.val.det : ℂ)⁻¹) ^ (2 * halfWeight) =
      (matrix.val.det : ℂ) ^ (-halfWeight) := by
    rw [inv_zpow, zpow_mul, zpow_ofNat, ← Complex.ofReal_pow, Real.sq_sqrt positive.le, zpow_neg]
  rw [power]

def cuspScalarWeightedLinear (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (base : BinaryAdelicGL) : cusp.smooth →ₗ[ℂ] (UpperHalfPlane → ℂ) where
  toFun vector point := cuspScalarWeightedRealization cusp halfWeight vector base point
  map_add' first second := by
    funext point
    simp only [cuspScalarWeightedRealization, cuspScalarAffineRealization, map_add,
      Pi.add_apply, smul_add]
  map_smul' scalar vector := by
    funext point
    simp only [cuspScalarWeightedRealization, cuspScalarAffineRealization, map_smul,
      Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

/-- The inverse finite translation has the same order convention as the slash action. -/
def cuspFiniteRationalSlash (cusp : CuspidalRepresentation) (matrix : BinaryRationalGL) :
    Module.End ℂ cusp.smooth :=
  cuspSmoothAction cusp (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) matrix⁻¹))

theorem cuspFiniteRationalSlash_realize (cusp : CuspidalRepresentation) (rational : BinaryRationalGL)
    (vector : cusp.smooth) (matrix : BinaryRealGL) :
    cusp.realize (cuspFiniteRationalSlash cusp rational vector) (atInfinity matrix) =
      cusp.realize vector (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational * matrix)) := by
  rw [cuspFiniteRationalSlash, cuspSmoothAction_realize]
  have invariant := cusp.leftRational rational vector
    (atInfinity matrix * atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational⁻¹))
  rw [binaryRationalMatrix_split] at invariant
  have finite_inverse (element : BinaryFiniteGL) : atFinite element⁻¹ = (atFinite element)⁻¹ := by
    apply Units.ext
    rfl
  rw [map_inv, finite_inverse] at invariant ⊢
  rw [mul_assoc, ← mul_assoc (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational)),
    ← (atInfinity_commute_atFinite matrix (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational)).eq,
    mul_assoc, mul_inv_cancel, mul_one, ← atInfinity_mul] at invariant
  exact invariant.symm

theorem cuspFiniteRationalSlash_weighted (cusp : CuspidalRepresentation) (rational : BinaryRationalGL)
    (halfWeight : ℤ) (vector : cusp.smooth) (point : UpperHalfPlane) :
    cuspScalarWeightedLinear cusp halfWeight 1 (cuspFiniteRationalSlash cusp rational vector) point =
      cuspScalarWeightedRealization cusp halfWeight vector
        (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)) point := by
  change point.im ^ halfWeight •
    cusp.realize (cuspFiniteRationalSlash cusp rational vector)
      (1 * atInfinity (invertibleMatrix (binaryUpperSectionMatrix point))) = _
  rw [one_mul, cuspFiniteRationalSlash_realize, atInfinity_mul]
  rfl

theorem cuspFiniteRationalSlash_eq_slash (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (rational : BinaryRationalGL)
    (positive : 0 < (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational).val.det) :
    cuspScalarWeightedLinear cusp halfWeight 1 (cuspFiniteRationalSlash cusp rational vector) =
      (((GeneralLinearGroup.map (algebraMap ℚ ℝ) rational).val.det : ℂ) ^ (halfWeight + 1)) •
        SlashAction.map (-2 * halfWeight) (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)
          (cuspScalarWeightedLinear cusp halfWeight 1 vector) := by
  funext point
  rw [cuspFiniteRationalSlash_weighted,
    cuspScalarWeightedRealization_positive cusp central_positive halfWeight vector rotation _ positive,
    Pi.smul_apply, smul_eq_mul, ModularForm.slash_apply]
  have det_positive : 0 < (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)).val := positive
  have sigma : UpperHalfPlane.σ (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational) =
      ContinuousAlgEquiv.refl ℝ ℂ := by
    unfold UpperHalfPlane.σ
    rw [ite_eq_left det_positive]
  rw [sigma, ContinuousAlgEquiv.refl_apply, abs_of_pos det_positive]
  simp only [GeneralLinearGroup.val_det_apply]
  have power : ((GeneralLinearGroup.map (algebraMap ℚ ℝ) rational).val.det : ℂ) ^ (halfWeight + 1) *
      ((GeneralLinearGroup.map (algebraMap ℚ ℝ) rational).val.det : ℂ) ^ (-2 * halfWeight - 1) =
      ((GeneralLinearGroup.map (algebraMap ℚ ℝ) rational).val.det : ℂ) ^ (-halfWeight) := by
    rw [← zpow_add₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt positive))]
    congr 1
    ring
  have negative : -(-2 * halfWeight) = 2 * halfWeight := by ring
  rw [negative]
  change _ = _ * (cuspScalarWeightedRealization cusp halfWeight vector 1 _ * _ * _)
  rw [← power]
  ring

end TernaryPeriodPolynomials.SphericalDetection.Helpers
