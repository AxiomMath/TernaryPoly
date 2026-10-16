module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.GLStrongApproximation

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryAdelic_rational_real_integral (matrix : BinaryAdelicGL) :
    ∃ (rational : BinaryRationalGL) (real : BinaryRealGL)
      (compact : GeneralLinearGroup (Fin 2) IntegralAdeles),
      matrix = GeneralLinearGroup.map rationalAdele rational * atInfinity real *
        atFinite (GeneralLinearGroup.map integralEmbedding compact) := by
  obtain ⟨real, finite, split⟩ := binaryAdelic_exists_real_finite matrix
  obtain ⟨rational, compact, finite_split⟩ := finiteGL_rational_integral_factorization finite
  refine ⟨rational, (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)⁻¹ * real, compact, ?_⟩
  rw [split, finite_split, atFinite_mul, binaryRationalMatrix_split]
  rw [mul_assoc (atInfinity _) (atFinite _) (atInfinity _),
    ← (atInfinity_commute_atFinite
      ((GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)⁻¹ * real)
      (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational)).eq,
    ← mul_assoc (atInfinity _) (atInfinity _) (atFinite _), ← atInfinity_mul]
  simp only [mul_inv_cancel_left, mul_assoc]

theorem cuspRealization_exists_real_nonzero (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (nonzero : vector ≠ 0) :
    ∃ real : BinaryRealGL, cusp.realize vector (atInfinity real) ≠ 0 := by
  obtain ⟨base, base_nonzero⟩ := cuspScalarWeightedRealization_nonzero cusp 0 vector nonzero
  rw [cuspScalarWeightedRealization_I] at base_nonzero
  obtain ⟨rational, real, compact, split⟩ := binaryAdelic_rational_real_integral base
  refine ⟨real, ?_⟩
  rw [split, mul_assoc, cusp.leftRational,
    cuspRealization_right_eigenvector cusp vector _ 1 (by simpa only [one_smul] using spherical compact),
    one_mul] at base_nonzero
  exact base_nonzero

def binaryIntegerReflection : GeneralLinearGroup (Fin 2) ℤ :=
  ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem binaryIntegerReflection_real :
    GeneralLinearGroup.map (Int.castRingHom ℝ) binaryIntegerReflection = UpperHalfPlane.J := by
  apply Units.ext
  funext row column
  fin_cases row <;> fin_cases column <;>
    simp [binaryIntegerReflection, UpperHalfPlane.val_J, GeneralLinearGroup.map_apply]

theorem cuspSpherical_integral_fixed (cusp : CuspidalRepresentation) (vector : cusp.H)
    (spherical : vector ∈ cuspSphericalValues cusp) (integer : GeneralLinearGroup (Fin 2) ℤ) :
    cusp.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
      (GeneralLinearGroup.map (Int.castRingHom ℚ) integer))) vector = vector := by
  have equality : GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles)
      (GeneralLinearGroup.map (Int.castRingHom ℚ) integer) =
      GeneralLinearGroup.map integralEmbedding (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) integer) := by
    apply Units.ext
    funext row column
    simp only [GeneralLinearGroup.map_apply]
    change algebraMap ℚ FiniteAdeles (integer.val row column : ℚ) =
      integralEmbedding (integer.val row column : IntegralAdeles)
    simp only [map_intCast]
  rw [equality]
  exact spherical _

theorem cuspRealization_reflection (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (matrix : BinaryRealGL) :
    cusp.realize vector (atInfinity (UpperHalfPlane.J * matrix)) =
      cusp.realize vector (atInfinity matrix) := by
  have real_equality : GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (GeneralLinearGroup.map (Int.castRingHom ℚ) binaryIntegerReflection) = UpperHalfPlane.J := by
    rw [← binaryIntegerReflection_real]
    apply Units.ext
    funext row column
    simp only [GeneralLinearGroup.map_apply]
    change algebraMap ℚ ℝ (binaryIntegerReflection.val row column : ℚ) =
      (binaryIntegerReflection.val row column : ℝ)
    simp only [map_intCast]
  simpa only [real_equality] using cuspRealization_rational_real cusp vector
    (GeneralLinearGroup.map (Int.castRingHom ℚ) binaryIntegerReflection)
    (cuspSpherical_integral_fixed cusp vector.val spherical binaryIntegerReflection) matrix

theorem cuspRealization_exists_positive_nonzero (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (nonzero : vector ≠ 0) :
    ∃ real : BinaryRealGL, 0 < real.val.det ∧ cusp.realize vector (atInfinity real) ≠ 0 := by
  obtain ⟨real, real_nonzero⟩ := cuspRealization_exists_real_nonzero cusp vector spherical nonzero
  by_cases positive : 0 < real.val.det
  · exact ⟨real, positive, real_nonzero⟩
  · refine ⟨UpperHalfPlane.J * real, ?_, ?_⟩
    · have negative : real.val.det < 0 :=
        lt_of_le_of_ne (le_of_not_gt positive) (GeneralLinearGroup.det_ne_zero real)
      have reflection_det : UpperHalfPlane.J.val.det = -1 := by
        norm_num [UpperHalfPlane.val_J, Matrix.det_fin_two]
      rw [GeneralLinearGroup.coe_mul, Matrix.det_mul, reflection_det, neg_one_mul]
      exact neg_pos.mpr negative
    · rwa [cuspRealization_reflection cusp vector spherical]

/-- A nonzero spherical weight vector has nonzero scalar realization at adelic base one. -/
theorem cuspScalarWeightedRealization_identity_nonzero (cusp : CuspidalRepresentation)
    (central_positive : ∀ unit : ℝˣ, 0 < unit.val → cusp.centralCharacter (realAdeleUnit unit) = 1)
    (halfWeight : ℤ) (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val) (nonzero : vector ≠ 0) :
    ∃ point : UpperHalfPlane, cuspScalarWeightedRealization cusp halfWeight vector 1 point ≠ 0 := by
  obtain ⟨real, positive, real_nonzero⟩ := cuspRealization_exists_positive_nonzero cusp vector spherical nonzero
  refine ⟨real • UpperHalfPlane.I, ?_⟩
  intro zero
  have identity := cuspScalarWeightedRealization_positive cusp central_positive halfWeight vector rotation real positive
    UpperHalfPlane.I
  rw [zero, mul_zero] at identity
  exact real_nonzero (by simpa only [UpperHalfPlane.coe_I, cuspScalarWeightedRealization_I] using identity)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
