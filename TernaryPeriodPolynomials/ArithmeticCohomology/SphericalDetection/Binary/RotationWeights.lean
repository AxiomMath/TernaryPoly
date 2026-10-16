module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationBasis
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.TangentCohomology

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryRotations_normalizingFactor (angle : Circle) (exponent : ℂ) :
    normPower (Matrix.GeneralLinearGroup.det (atInfinity (binaryRotations angle))) exponent = 1 := by
  rw [binary_normalizingFactor_eq]
  change Complex.exp (exponent * (Real.log (binaryRotationMatrix angle).det : ℂ)) = 1
  rw [binaryRotationMatrix_det, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

theorem binaryHilbertOperator_rotation_apply (degree : ℕ) (cusp : CuspidalRepresentation)
    (angle : Circle) (vectors : BinaryHomogeneousExponent (degree + 1) → cusp.H)
    (exponent : BinaryHomogeneousExponent (degree + 1)) :
    binaryHilbertOperator cusp (binaryRotationBasis (degree + 1)) (binaryRotations angle) vectors exponent =
      (((angle : ℂ)⁻¹) ^ exponent.val 0 * (angle : ℂ) ^ exponent.val 1) •
        cusp.π (atInfinity (binaryRotations angle)) (vectors exponent) := by
  classical
  rw [binaryHilbertOperator_apply, binaryRotations_normalizingFactor, one_smul]
  simp only [binaryRotationBasis_coefficient, map_smul, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
  simp

def binaryCuspRotationWeight {degree : ℕ} (exponent : BinaryHomogeneousExponent (degree + 1)) : ℤ :=
  (exponent.val 0 : ℤ) - (exponent.val 1 : ℤ) - 2

theorem binaryCuspRotationWeight_bounds {degree : ℕ} (exponent : BinaryHomogeneousExponent (degree + 1)) :
    -(degree : ℤ) - 3 ≤ binaryCuspRotationWeight exponent ∧
      binaryCuspRotationWeight exponent ≤ (degree : ℤ) - 1 := by
  have total := binaryHomogeneousExponent_sum exponent
  unfold binaryCuspRotationWeight
  omega

theorem binaryCuspRotationWeight_scalar {degree : ℕ} (exponent : BinaryHomogeneousExponent (degree + 1))
    (angle : Circle) :
    ((((angle : ℂ)⁻¹) ^ exponent.val 0 * (angle : ℂ) ^ exponent.val 1)⁻¹ * ((angle : ℂ) ^ 2)⁻¹) =
      (angle : ℂ) ^ binaryCuspRotationWeight exponent := by
  have nonzero : (angle : ℂ) ≠ 0 := by
    intro zero
    have norm := Circle.norm_coe angle
    rw [zero, norm_zero] at norm
    exact zero_ne_one norm
  simp [binaryCuspRotationWeight, zpow_sub₀ nonzero, zpow_natCast, div_eq_mul_inv,
    inv_pow, mul_comm]

theorem binaryCuspRotationWeight_even {degree : ℕ} (odd : Odd degree)
    (exponent : BinaryHomogeneousExponent (degree + 1)) : Even (binaryCuspRotationWeight exponent) := by
  obtain ⟨half, degree_eq⟩ := odd
  have total := binaryHomogeneousExponent_sum exponent
  refine ⟨(exponent.val 0 : ℤ) - (half : ℤ) - 2, ?_⟩
  unfold binaryCuspRotationWeight
  omega

theorem binaryRotation_eigenvector_coordinate {degree : ℕ} (cusp : CuspidalRepresentation)
    (vector : BinaryHomogeneousExponent (degree + 1) → cusp.H)
    (eigenvector : ∀ angle : Circle,
      binaryHilbertOperator cusp (binaryRotationBasis (degree + 1)) (binaryRotations angle) vector =
        ((angle : ℂ) ^ 2)⁻¹ • vector)
    (exponent : BinaryHomogeneousExponent (degree + 1)) (angle : Circle) :
    cusp.π (atInfinity (binaryRotations angle)) (vector exponent) =
      (angle : ℂ) ^ binaryCuspRotationWeight exponent • vector exponent := by
  have nonzero : (angle : ℂ) ≠ 0 := by
    intro zero
    have norm := Circle.norm_coe angle
    rw [zero, norm_zero] at norm
    exact zero_ne_one norm
  have coefficient_nonzero : (((angle : ℂ)⁻¹) ^ exponent.val 0 * (angle : ℂ) ^ exponent.val 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (inv_ne_zero nonzero)) (pow_ne_zero _ nonzero)
  have coordinate := congrFun (eigenvector angle) exponent
  rw [binaryHilbertOperator_rotation_apply, Pi.smul_apply] at coordinate
  calc
    cusp.π (atInfinity (binaryRotations angle)) (vector exponent) =
        (((angle : ℂ)⁻¹) ^ exponent.val 0 * (angle : ℂ) ^ exponent.val 1)⁻¹ •
          ((((angle : ℂ)⁻¹) ^ exponent.val 0 * (angle : ℂ) ^ exponent.val 1) •
            cusp.π (atInfinity (binaryRotations angle)) (vector exponent)) :=
      (inv_smul_smul₀ coefficient_nonzero _).symm
    _ = (angle : ℂ) ^ binaryCuspRotationWeight exponent • vector exponent := by
      rw [coordinate, smul_smul, binaryCuspRotationWeight_scalar]

theorem cohomological_exists_unitary_rotation_weight (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree) :
    ∃ (level : Subgroup BinaryFiniteGL) (vector : cusp.H) (weight : ℤ),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧ vector ≠ 0 ∧
      (∀ element : level, cusp.π (atFinite element.val) vector = vector) ∧
      (-(degree : ℤ) - 3 ≤ weight ∧ weight ≤ (degree : ℤ) - 1) ∧
      ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector := by
  obtain ⟨level, vectors, level_open, level_compact, nonzero, fixed, rotation⟩ :=
    cohomological_exists_rotation_eigenvector cusp spherical cohomological (binaryRotationBasis (degree + 1))
  obtain ⟨exponent, coordinate_nonzero⟩ := Function.ne_iff.mp nonzero
  exact ⟨level, vectors exponent, binaryCuspRotationWeight exponent, level_open, level_compact,
    coordinate_nonzero, fun element => fixed element exponent, binaryCuspRotationWeight_bounds exponent,
    binaryRotation_eigenvector_coordinate cusp vectors rotation exponent⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
