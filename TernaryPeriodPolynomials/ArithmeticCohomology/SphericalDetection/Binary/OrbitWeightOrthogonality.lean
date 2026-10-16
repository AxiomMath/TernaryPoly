module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.DiskWeightOrthogonality
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Scalar.Holomorphic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ReflectionLadders

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryDiskCoordinate_norm_lt_one (point : ℂ) (positive : 0 < point.im) :
    ‖binaryDiskCoordinate point‖ < 1 := by
  have denominator : point + Complex.I ≠ 0 := by
    intro zero
    have imaginary := congrArg Complex.im zero
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at imaginary
    linarith
  rw [binaryDiskCoordinate, norm_div, div_lt_one (norm_pos_iff.mpr denominator)]
  have squares : ‖point - Complex.I‖ ^ 2 < ‖point + Complex.I‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.I_re, sub_zero,
      Complex.sub_im, Complex.I_im, Complex.add_re, add_zero, Complex.add_im]
    nlinarith
  nlinarith [norm_nonneg (point + Complex.I), norm_nonneg (point - Complex.I)]

theorem cuspAffineOrbitVector_inner_above_weight (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ (2 * halfWeight) • vector)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet)
    (test : cusp.H) (testWeight : ℤ) (above : 2 * halfWeight < testWeight)
    (test_rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) test =
      (angle : ℂ) ^ testWeight • test) (point : UpperHalfPlane) :
    inner ℂ test (cuspAffineOrbitVector cusp vector point) = 0 := by
  have denominator : (point : ℂ) + Complex.I ≠ 0 := by
    intro zero
    have imaginary := congrArg Complex.im zero
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im, UpperHalfPlane.coe_im] at imaginary
    linarith [point.im_pos]
  have zero := cuspDiskOrbit_inner_above_weight cusp halfWeight vector rotation holomorphic test testWeight above
    test_rotation (binaryDiskCoordinate point) (binaryDiskCoordinate_norm_lt_one point point.im_pos)
  rw [cuspDiskOrbit, binaryDiskPoint_coordinate point denominator, inner_smul_right] at zero
  have weighted_zero := (mul_eq_zero.mp zero).resolve_left
    (zpow_ne_zero _ (binaryDiskCoordinate_sub_ne_zero point denominator))
  rw [cuspWeightedAffineOrbit, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right] at weighted_zero
  exact (mul_eq_zero.mp weighted_zero).resolve_left (by
    change ((point.im ^ halfWeight : ℝ) : ℂ) ≠ 0
    exact Complex.ofReal_ne_zero.mpr (zpow_ne_zero halfWeight (ne_of_gt point.im_pos)))

theorem cuspPositiveOrbit_inner_above_weight (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ (2 * halfWeight) • vector)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet)
    (test : cusp.H) (testWeight : ℤ) (above : 2 * halfWeight < testWeight)
    (test_rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) test =
      (angle : ℂ) ^ testWeight • test) (matrix : BinaryRealGL) (positive : 0 < matrix.val.det) :
    inner ℂ test (cusp.π (atInfinity matrix) vector) = 0 := by
  rw [cuspRotationWeight_positive_formula cusp spherical central_positive vector (2 * halfWeight) rotation matrix positive,
    inner_smul_right, cuspAffineOrbitVector_inner_above_weight cusp halfWeight vector rotation holomorphic
      test testWeight above test_rotation, mul_zero]

theorem cuspRealOrbit_inner_weight_gap (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.H)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ (2 * halfWeight) • vector)
    (holomorphic : DifferentiableOn ℂ (cuspWeightedAffineOrbit cusp halfWeight vector)
      UpperHalfPlane.upperHalfPlaneSet)
    (test : cusp.H) (testWeight : ℤ) (above : 2 * halfWeight < testWeight) (below : testWeight < -(2 * halfWeight))
    (test_rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) test =
      (angle : ℂ) ^ testWeight • test) (matrix : BinaryRealGL) :
    inner ℂ test (cusp.π (atInfinity matrix) vector) = 0 := by
  by_cases positive : 0 < matrix.val.det
  · exact cuspPositiveOrbit_inner_above_weight cusp spherical central_positive halfWeight vector rotation
      holomorphic test testWeight above test_rotation matrix positive
  · have negative : matrix.val.det < 0 := lt_of_le_of_ne (le_of_not_gt positive) matrix.det_ne_zero
    have reflected_positive : 0 < (UpperHalfPlane.J * matrix).val.det := by
      have reflection_det : UpperHalfPlane.J.val.det = -1 := by norm_num [UpperHalfPlane.val_J, Matrix.det_fin_two]
      rw [GeneralLinearGroup.coe_mul, Matrix.det_mul, reflection_det, neg_one_mul]
      exact neg_pos.mpr negative
    have zero := cuspPositiveOrbit_inner_above_weight cusp spherical central_positive halfWeight vector rotation
      holomorphic (cusp.π (atInfinity UpperHalfPlane.J) test) (-testWeight) (by omega)
      (cuspReflection_rotation cusp testWeight test test_rotation) (UpperHalfPlane.J * matrix) reflected_positive
    rw [atInfinity_mul, map_mul, Module.End.mul_apply, cuspUnitary_inner] at zero
    exact zero

end TernaryPeriodPolynomials.SphericalDetection.Helpers
