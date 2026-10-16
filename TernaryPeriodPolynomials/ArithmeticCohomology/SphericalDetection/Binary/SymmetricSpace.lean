module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ReflectionCohomology
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def complexDirection (value : ℂ) (nonzero : value ≠ 0) : Circle :=
  ⟨value / (‖value‖ : ℂ), by
    change dist (value / (‖value‖ : ℂ)) 0 = 1
    rw [dist_zero_right]
    simp [Complex.norm_real, norm_ne_zero_iff.mpr nonzero]⟩

theorem complexDirection_re (value : ℂ) (nonzero : value ≠ 0) :
    ((complexDirection value nonzero : Circle) : ℂ).re = value.re / ‖value‖ := by
  exact Complex.div_ofReal_re value ‖value‖

theorem complexDirection_im (value : ℂ) (nonzero : value ≠ 0) :
    ((complexDirection value nonzero : Circle) : ℂ).im = value.im / ‖value‖ := by
  exact Complex.div_ofReal_im value ‖value‖

theorem binary_stabilizer_positive_decomposition (matrix : BinaryRealGL)
    (positive : 0 < (GeneralLinearGroup.det matrix).val)
    (stabilizes : matrix • UpperHalfPlane.I = UpperHalfPlane.I) :
    ∃ (unit : ℝˣ) (angle : Circle), 0 < unit.val ∧
      matrix = GeneralLinearGroup.scalar (Fin 2) unit * binaryRotations angle := by
  obtain ⟨diagonal, off_diagonal⟩ := (UpperHalfPlane.gl_smul_I_eq_I_iff_of_pos positive).mp stabilizes
  let value : ℂ := ⟨matrix.val 0 0, matrix.val 1 0⟩
  have nonzero : value ≠ 0 := by
    intro zero
    have first := congrArg Complex.re zero
    have second := congrArg Complex.im zero
    change matrix.val 0 0 = 0 at first
    change matrix.val 1 0 = 0 at second
    have determinant := matrix.det_ne_zero
    apply determinant
    simp [Matrix.det_fin_two, first, second]
  let unit : ℝˣ := Units.mk0 ‖value‖ (norm_ne_zero_iff.mpr nonzero)
  refine ⟨unit, complexDirection value nonzero, norm_pos_iff.mpr nonzero, ?_⟩
  have norm_ne : ‖value‖ ≠ 0 := norm_ne_zero_iff.mpr nonzero
  have real_scaled : ‖value‖ * (complexDirection value nonzero : ℂ).re = matrix.val 0 0 := by
    rw [complexDirection_re]
    change ‖value‖ * (matrix.val 0 0 / ‖value‖) = matrix.val 0 0
    field_simp
  have imaginary_scaled : ‖value‖ * (complexDirection value nonzero : ℂ).im = matrix.val 1 0 := by
    rw [complexDirection_im]
    change ‖value‖ * (matrix.val 1 0 / ‖value‖) = matrix.val 1 0
    field_simp
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.coe_scalar, binaryRotations, binaryRotation, Matrix.mul_apply,
      Fin.sum_univ_two, unit, real_scaled, imaginary_scaled, diagonal, off_diagonal]

theorem binary_cocycle_stabilizer_zero (representation : Rep ℂ BinaryRealGL)
    (cycle : groupCohomology.cocycles₁ representation)
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (reflection_zero : cycle UpperHalfPlane.J = 0)
    (central_zero : ∀ unit : ℝˣ, 0 < unit.val → cycle (GeneralLinearGroup.scalar (Fin 2) unit) = 0)
    (matrix : BinaryRealGL) (stabilizes : matrix • UpperHalfPlane.I = UpperHalfPlane.I) : cycle matrix = 0 := by
  have positive_case (matrix : BinaryRealGL) (positive : 0 < (GeneralLinearGroup.det matrix).val)
      (stabilizes : matrix • UpperHalfPlane.I = UpperHalfPlane.I) : cycle matrix = 0 := by
    obtain ⟨unit, angle, unit_positive, rfl⟩ := binary_stabilizer_positive_decomposition matrix positive stabilizes
    exact cocycle_mul_eq_zero representation cycle _ _ (central_zero unit unit_positive) (rotations_zero angle)
  rcases lt_or_gt_of_ne (GeneralLinearGroup.det matrix).ne_zero with negative | positive
  · have product_positive : 0 < (GeneralLinearGroup.det (matrix * UpperHalfPlane.J)).val := by
      simpa only [map_mul, Units.val_mul, UpperHalfPlane.det_J, Units.val_neg, Units.val_one,
        mul_neg_one, neg_pos] using negative
    have reflection_fixes : UpperHalfPlane.J • UpperHalfPlane.I = UpperHalfPlane.I := by
      apply UpperHalfPlane.ext
      simp [UpperHalfPlane.coe_J_smul]
    have product_fixes : (matrix * UpperHalfPlane.J) • UpperHalfPlane.I = UpperHalfPlane.I := by
      rw [mul_smul, reflection_fixes, stabilizes]
    exact (cocycle_right_eq_of_zero representation cycle matrix UpperHalfPlane.J reflection_zero).symm.trans
      (positive_case _ product_positive product_fixes)
  · exact positive_case matrix positive stabilizes

def binarySymmetricSection (point : UpperHalfPlane) : BinaryRealGL :=
  Matrix.SpecialLinearGroup.toGL point.toSL2R

theorem binarySymmetricSection_smul (point : UpperHalfPlane) :
    binarySymmetricSection point • UpperHalfPlane.I = point :=
  UpperHalfPlane.toSL2R_smul_I point

theorem binarySymmetricSection_continuous : Continuous binarySymmetricSection :=
  Matrix.SpecialLinearGroup.continuous_toGL.comp UpperHalfPlane.continuous_toSL2R

def binarySymmetricPotential (representation : Rep ℂ BinaryRealGL)
    (cycle : groupCohomology.cocycles₁ representation) (point : UpperHalfPlane) : representation :=
  cycle (binarySymmetricSection point)

theorem binarySymmetricPotential_descent (representation : Rep ℂ BinaryRealGL)
    (cycle : groupCohomology.cocycles₁ representation)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (matrix : BinaryRealGL) :
    binarySymmetricPotential representation cycle (matrix • UpperHalfPlane.I) = cycle matrix := by
  let lift := binarySymmetricSection (matrix • UpperHalfPlane.I)
  have fixes : (lift⁻¹ * matrix) • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [mul_smul, ← binarySymmetricSection_smul (matrix • UpperHalfPlane.I)]
    exact inv_smul_smul lift UpperHalfPlane.I
  have same := cocycle_right_eq_of_zero representation cycle lift (lift⁻¹ * matrix)
    (stabilizer_zero _ fixes)
  change cycle lift = cycle matrix
  simpa only [mul_inv_cancel_left] using same.symm

theorem binarySymmetricPotential_affine (representation : Rep ℂ BinaryRealGL)
    (cycle : groupCohomology.cocycles₁ representation)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (matrix : BinaryRealGL) (point : UpperHalfPlane) :
    binarySymmetricPotential representation cycle (matrix • point) =
      cycle matrix + representation.ρ matrix (binarySymmetricPotential representation cycle point) := by
  have descent := binarySymmetricPotential_descent representation cycle stabilizer_zero
    (matrix * binarySymmetricSection point)
  rw [mul_smul, binarySymmetricSection_smul] at descent
  have identity := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property matrix
    (binarySymmetricSection point)
  change cycle (matrix * binarySymmetricSection point) =
    representation.ρ matrix (cycle (binarySymmetricSection point)) + cycle matrix at identity
  exact descent.trans (identity.trans (add_comm _ _))

theorem binarySymmetricPotential_basepoint (representation : Rep ℂ BinaryRealGL)
    (cycle : groupCohomology.cocycles₁ representation)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) :
    binarySymmetricPotential representation cycle UpperHalfPlane.I = 0 := by
  have descent := binarySymmetricPotential_descent representation cycle stabilizer_zero 1
  simpa using descent

theorem binarySymmetricPotential_eq_zero_iff (representation : Rep ℂ BinaryRealGL)
    (cycle : groupCohomology.cocycles₁ representation)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) :
    binarySymmetricPotential representation cycle = 0 ↔ cycle = 0 := by
  constructor
  · intro zero
    apply groupCohomology.cocycles₁_ext
    intro matrix
    exact (binarySymmetricPotential_descent representation cycle stabilizer_zero matrix).symm.trans
      (congrFun zero (matrix • UpperHalfPlane.I))
  · rintro rfl
    rfl

theorem binarySymmetricPotential_coboundary_iff (representation : Rep ℂ BinaryRealGL)
    (cycle : groupCohomology.cocycles₁ representation)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) :
    groupCohomology.H1π representation cycle = 0 ↔
      ∃ primitive : representation, ∀ matrix : BinaryRealGL,
        binarySymmetricPotential representation cycle (matrix • UpperHalfPlane.I) =
          representation.ρ matrix primitive - primitive := by
  rw [groupCohomology.H1π_eq_zero_iff]
  constructor
  · rintro ⟨primitive, boundary⟩
    refine ⟨primitive, fun matrix => ?_⟩
    exact (binarySymmetricPotential_descent representation cycle stabilizer_zero matrix).trans
      (congrFun boundary matrix).symm
  · rintro ⟨primitive, boundary⟩
    refine ⟨primitive, funext fun matrix => ?_⟩
    exact (boundary matrix).symm.trans
      (binarySymmetricPotential_descent representation cycle stabilizer_zero matrix)

variable {degree : ℕ} {index : Type} [Fintype index]

theorem binarySymmetricPotential_continuous (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (continuous : Continuous (fun matrix => (cycle matrix : binaryHilbertFiniteValues cusp level).val)) :
    Continuous (fun point =>
      (binarySymmetricPotential (binaryHilbertFiniteRep cusp spherical basis level) cycle point :
        binaryHilbertFiniteValues cusp level).val) :=
  continuous.comp binarySymmetricSection_continuous

theorem cohomological_exists_symmetricPotential (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (cohomological : Cohomological cusp degree)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1))) :
    ∃ (level : Subgroup BinaryFiniteGL)
      (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level)),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      groupCohomology.H1π (binaryHilbertFiniteRep cusp spherical basis level) cycle ≠ 0 ∧
      Continuous (fun point =>
        (binarySymmetricPotential (binaryHilbertFiniteRep cusp spherical basis level) cycle point :
          binaryHilbertFiniteValues cusp level).val) ∧
      (∀ matrix : BinaryRealGL, matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0) ∧
      ∀ matrix : BinaryRealGL,
        binarySymmetricPotential (binaryHilbertFiniteRep cusp spherical basis level) cycle
          (matrix • UpperHalfPlane.I) = cycle matrix := by
  obtain ⟨level, cycle, level_open, level_compact, nonzero, continuous,
    rotations_zero, reflection_zero, central_zero⟩ :=
    cohomological_exists_symmetricSpace_H1 cusp spherical cohomological basis
  have stabilizer_zero := binary_cocycle_stabilizer_zero _ cycle rotations_zero reflection_zero central_zero
  exact ⟨level, cycle, level_open, level_compact, nonzero,
    binarySymmetricPotential_continuous cusp spherical basis level cycle continuous,
    stabilizer_zero, binarySymmetricPotential_descent _ cycle stabilizer_zero⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
