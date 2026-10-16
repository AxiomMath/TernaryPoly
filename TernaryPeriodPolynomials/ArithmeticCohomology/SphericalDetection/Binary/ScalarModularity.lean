module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarRealization
public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Perm.ConjAct
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.SetTheory.Cardinal.Embedding
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryRationalMatrix_split (matrix : BinaryRationalGL) :
    GeneralLinearGroup.map rationalAdele matrix =
      atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) matrix) *
        atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) matrix) := by
  apply Units.ext
  funext row column
  apply Prod.ext
  · simp only [atInfinity, atFinite, combineGL, pairMatrix, GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Prod.fst_sum, Prod.fst_mul, GeneralLinearGroup.coe_one]
    simp only [← Matrix.mul_apply, mul_one]
    rfl
  · simp only [atInfinity, atFinite, combineGL, pairMatrix, GeneralLinearGroup.coe_mul,
      Matrix.mul_apply, Prod.snd_sum, Prod.snd_mul, GeneralLinearGroup.coe_one]
    simp only [← Matrix.mul_apply, one_mul]
    rfl

theorem cuspRealization_rational_real (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (rational : BinaryRationalGL)
    (fixed : cusp.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational)) vector.val = vector.val)
    (matrix : BinaryRealGL) :
    cusp.realize vector (atInfinity (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational * matrix)) =
      cusp.realize vector (atInfinity matrix) := by
  have identity := cusp.leftRational rational vector (atInfinity matrix)
  rw [binaryRationalMatrix_split, mul_assoc,
    ← (atInfinity_commute_atFinite matrix (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational)).eq,
    ← mul_assoc, ← atInfinity_mul,
    cuspRealization_right_eigenvector cusp vector _ 1 (by simpa only [one_smul] using fixed), one_mul] at identity
  exact identity

theorem cuspScalarAffineRealization_modular_phase (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (weight : ℤ) (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ weight • vector.val) (rational : BinaryRationalGL)
    (determinant : (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)).val = 1)
    (fixed : cusp.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational)) vector.val = vector.val)
    (point : UpperHalfPlane) :
    binaryPhaseValue (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational) point ^ weight *
        cuspScalarAffineRealization cusp vector 1
          ((GeneralLinearGroup.map (algebraMap ℚ ℝ) rational • point : UpperHalfPlane) : ℂ) =
      cuspScalarAffineRealization cusp vector 1 point := by
  have identity := cuspScalarAffineRealization_rotation cusp vector weight rotation 1
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational) determinant point
  rw [one_mul, cuspRealization_rational_real cusp vector rational fixed] at identity
  rw [← identity, cuspScalarAffineRealization, one_mul, binaryUpperSectionMatrix_coe, invertibleMatrix_coe]

theorem binary_weighted_phase_identity (matrix : BinaryRealGL)
    (determinant : (GeneralLinearGroup.det matrix).val = 1) (point : UpperHalfPlane) (halfWeight : ℤ) :
    (((matrix • point : UpperHalfPlane).im ^ halfWeight : ℝ) : ℂ) =
      UpperHalfPlane.denom matrix point ^ (-2 * halfWeight) *
        ((point.im ^ halfWeight : ℝ) : ℂ) * binaryPhaseValue matrix point ^ (2 * halfWeight) := by
  have denominator_nonzero := UpperHalfPlane.denom_ne_zero matrix point
  have norm_nonzero : (‖UpperHalfPlane.denom matrix point‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr denominator_nonzero)
  rw [UpperHalfPlane.im_smul_eq_div_normSq, determinant, abs_one, one_mul, Complex.normSq_eq_norm_sq,
    div_zpow, ← zpow_ofNat, ← zpow_mul, binaryPhaseValue, div_zpow]
  push_cast
  have opposite : -2 * halfWeight = -(2 * halfWeight) := by ring
  rw [opposite, zpow_neg]
  field_simp

theorem cuspScalarWeightedRealization_modular (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val) (rational : BinaryRationalGL)
    (determinant : (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational)).val = 1)
    (fixed : cusp.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) rational)) vector.val = vector.val)
    (point : UpperHalfPlane) :
    cuspScalarWeightedRealization cusp halfWeight vector 1
        ((GeneralLinearGroup.map (algebraMap ℚ ℝ) rational • point : UpperHalfPlane) : ℂ) =
      UpperHalfPlane.denom (GeneralLinearGroup.map (algebraMap ℚ ℝ) rational) point ^ (-2 * halfWeight) *
        cuspScalarWeightedRealization cusp halfWeight vector 1 point := by
  have identity := cuspScalarAffineRealization_modular_phase cusp vector (2 * halfWeight) rotation rational determinant fixed point
  simp only [cuspScalarWeightedRealization, Complex.real_smul]
  change (((GeneralLinearGroup.map (algebraMap ℚ ℝ) rational • point : UpperHalfPlane).im ^ halfWeight : ℝ) : ℂ) * _ = _
  rw [binary_weighted_phase_identity _ determinant point halfWeight, mul_assoc, mul_assoc, identity]
  rfl

theorem binaryIntegral_specialLinear_real (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (SpecialLinearGroup.mapGL ℚ matrix) = SpecialLinearGroup.mapGL ℝ matrix := by
  apply Units.ext
  ext row column
  change (((matrix.val row column : ℤ) : ℚ) : ℝ) = (matrix.val row column : ℝ)
  norm_cast

theorem cuspSpherical_specialLinear_fixed (cusp : CuspidalRepresentation) (vector : cusp.H)
    (spherical : vector ∈ cuspSphericalValues cusp) (matrix : SpecialLinearGroup (Fin 2) ℤ) :
    cusp.π (atFinite (GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (SpecialLinearGroup.mapGL ℚ matrix))) vector = vector := by
  have equality : GeneralLinearGroup.map (algebraMap ℚ FiniteAdeles) (SpecialLinearGroup.mapGL ℚ matrix) =
      GeneralLinearGroup.map integralEmbedding (SpecialLinearGroup.mapGL IntegralAdeles matrix) := by
    apply Units.ext
    funext row column
    simp only [GeneralLinearGroup.map_apply, SpecialLinearGroup.mapGL_coe_matrix, SpecialLinearGroup.map_apply_coe]
    change algebraMap ℚ FiniteAdeles (algebraMap ℤ ℚ (matrix.val row column)) =
      integralEmbedding (algebraMap ℤ IntegralAdeles (matrix.val row column))
    simp
  rw [equality]
  exact spherical _

theorem cuspScalarWeightedRealization_modular_levelOne (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val) (matrix : SpecialLinearGroup (Fin 2) ℤ) (point : UpperHalfPlane) :
    cuspScalarWeightedRealization cusp halfWeight vector 1 ((SpecialLinearGroup.mapGL ℝ matrix • point : UpperHalfPlane) : ℂ) =
      UpperHalfPlane.denom (SpecialLinearGroup.mapGL ℝ matrix) point ^ (-2 * halfWeight) *
        cuspScalarWeightedRealization cusp halfWeight vector 1 point := by
  have determinant : (GeneralLinearGroup.det
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (SpecialLinearGroup.mapGL ℚ matrix))).val = 1 := by
    rw [binaryIntegral_specialLinear_real]
    exact (SpecialLinearGroup.map (algebraMap ℤ ℝ) matrix).property
  simpa only [binaryIntegral_specialLinear_real] using
    cuspScalarWeightedRealization_modular cusp halfWeight vector rotation (SpecialLinearGroup.mapGL ℚ matrix) determinant
      (cuspSpherical_specialLinear_fixed cusp vector.val spherical matrix) point

def cuspLevelOneSlashInvariant (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth)
    (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val) :
    SlashInvariantForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight) := by
  refine ⟨fun point => cuspScalarWeightedRealization cusp halfWeight vector 1 point, ?_⟩
  rintro matrix ⟨integral, rfl⟩
  funext point
  rw [ModularForm.slash_apply]
  have determinant : (GeneralLinearGroup.det (SpecialLinearGroup.mapGL ℝ integral)).val = 1 :=
    (SpecialLinearGroup.map (algebraMap ℤ ℝ) integral).property
  simp only [UpperHalfPlane.σ, determinant, zero_lt_one, ite_true, ContinuousAlgEquiv.refl_apply, abs_one,
    Complex.ofReal_one, one_zpow, mul_one]
  rw [cuspScalarWeightedRealization_modular_levelOne cusp halfWeight vector spherical rotation integral point,
    mul_right_comm, ← zpow_add₀ (UpperHalfPlane.denom_ne_zero _ point), add_neg_cancel, zpow_zero, one_mul]

theorem cuspScalarWeightedRealization_zero_at_infty (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (negative : halfWeight < 0) (vector : cusp.smooth) (base : BinaryAdelicGL) :
    UpperHalfPlane.IsZeroAtImInfty (fun point : UpperHalfPlane => cuspScalarWeightedRealization cusp halfWeight vector base point) := by
  obtain ⟨bound, _, bounded⟩ := cuspScalarWeightedRealization_bound cusp halfWeight vector
  rw [UpperHalfPlane.isZeroAtImInfty_iff]
  intro epsilon epsilon_positive
  have limit : Filter.Tendsto (fun value : ℝ => value ^ halfWeight * bound) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using (tendsto_zpow_atTop_zero (𝕜 := ℝ) negative).mul_const bound
  obtain ⟨cutoff, small⟩ := Filter.eventually_atTop.mp (limit.eventually (gt_mem_nhds epsilon_positive))
  exact ⟨cutoff, fun point point_large => (bounded base point).trans (small point.im point_large).le⟩

theorem cuspLevelOneSlashInvariant_zero_at_cusps (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (negative : halfWeight < 0) (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val) {point : OnePoint ℝ}
    (is_cusp : IsCusp point (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range) :
    point.IsZeroAt (cuspLevelOneSlashInvariant cusp halfWeight vector spherical rotation) (-2 * halfWeight) := by
  obtain ⟨matrix, point_eq⟩ := isCusp_SL2Z_iff'.mp is_cusp
  apply (OnePoint.isZeroAt_iff point_eq.symm).mpr
  rw [SlashInvariantFormClass.slash_action_eq (Γ := (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range)
    (k := -2 * halfWeight) (cuspLevelOneSlashInvariant cusp halfWeight vector spherical rotation)
    (SpecialLinearGroup.mapGL ℝ matrix) ⟨matrix, rfl⟩]
  exact cuspScalarWeightedRealization_zero_at_infty cusp halfWeight negative vector 1

def cuspLevelOneCuspForm_of_holomorphic (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (negative : halfWeight < 0) (vector : cusp.smooth) (spherical : vector.val ∈ cuspSphericalValues cusp)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ (2 * halfWeight) • vector.val)
    (holomorphic : DifferentiableOn ℂ (cuspScalarWeightedRealization cusp halfWeight vector 1)
      UpperHalfPlane.upperHalfPlaneSet) :
    CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range (-2 * halfWeight) := by
  refine ⟨cuspLevelOneSlashInvariant cusp halfWeight vector spherical rotation, ?_,
    cuspLevelOneSlashInvariant_zero_at_cusps cusp halfWeight negative vector spherical rotation⟩
  rw [UpperHalfPlane.mdifferentiable_iff]
  apply holomorphic.congr
  intro point positive
  rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos positive]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
