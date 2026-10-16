module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CohomologicalHolomorphic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def cuspScalarAffineRealization (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (base : BinaryAdelicGL) (point : ℂ) : ℂ :=
  cusp.realize vector (base * atInfinity (invertibleMatrix (binaryUpperSectionMatrix point)))

def cuspScalarWeightedRealization (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) (point : ℂ) : ℂ :=
  point.im ^ halfWeight • cuspScalarAffineRealization cusp vector base point

theorem cuspScalarAffineRealization_I (cusp : CuspidalRepresentation) (vector : cusp.smooth) (base : BinaryAdelicGL) :
    cuspScalarAffineRealization cusp vector base Complex.I = cusp.realize vector base := by
  rw [cuspScalarAffineRealization, binaryAffineSection_I, atInfinity_one, mul_one]

theorem cuspScalarWeightedRealization_I (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) :
    cuspScalarWeightedRealization cusp halfWeight vector base Complex.I = cusp.realize vector base := by
  rw [cuspScalarWeightedRealization, Complex.I_im, one_zpow, one_smul, cuspScalarAffineRealization_I]

theorem cuspScalarAffineRealization_analytic (cusp : CuspidalRepresentation) (vector : cusp.smooth) (base : BinaryAdelicGL) :
    AnalyticOnNhd ℝ (cuspScalarAffineRealization cusp vector base) UpperHalfPlane.upperHalfPlaneSet := by
  have group_regular := smooth_one_contDiffOn (function := fun matrix => cusp.realize vector (base * atInfinity matrix))
    (cusp.scalarSmooth vector base)
  have affine_regular : ContDiffOn ℝ ⊤ (cuspScalarAffineRealization cusp vector base) UpperHalfPlane.upperHalfPlaneSet :=
    group_regular.comp binaryUpperSectionMatrix_contDiffOn binaryUpperSectionMatrix_invertible
  intro point member
  exact (affine_regular.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds member)).analyticAt

theorem cuspScalarWeightedRealization_analytic (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (base : BinaryAdelicGL) :
    AnalyticOnNhd ℝ (cuspScalarWeightedRealization cusp halfWeight vector base) UpperHalfPlane.upperHalfPlaneSet := by
  intro point positive
  exact ((Complex.imCLM.analyticAt point).zpow (n := halfWeight) (ne_of_gt positive)).smul
    (cuspScalarAffineRealization_analytic cusp vector base point positive)

theorem cuspScalarWeightedRealization_nonzero (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (vector : cusp.smooth) (nonzero : vector ≠ 0) :
    ∃ base : BinaryAdelicGL, cuspScalarWeightedRealization cusp halfWeight vector base Complex.I ≠ 0 := by
  classical
  by_contra no_base
  push Not at no_base
  apply nonzero
  apply cusp.injective
  ext base
  simpa only [cuspScalarWeightedRealization_I, map_zero, Pi.zero_apply] using no_base base

theorem cuspRealization_right_eigenvector (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (element : BinaryAdelicGL) (scalar : ℂ) (eigenvector : cusp.π element vector.val = scalar • vector.val)
    (base : BinaryAdelicGL) :
    cusp.realize vector (base * element) = scalar * cusp.realize vector base := by
  have equality : (⟨cusp.π element vector.val, cusp.smooth_stable element vector.val vector.property⟩ : cusp.smooth) =
      scalar • vector := Subtype.ext eigenvector
  have identity := cusp.equivariant element vector base
  rw [equality, map_smul] at identity
  exact identity.symm

theorem cuspScalarAffineRealization_rotation (cusp : CuspidalRepresentation) (vector : cusp.smooth)
    (weight : ℤ) (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector.val =
      (angle : ℂ) ^ weight • vector.val) (base : BinaryAdelicGL) (matrix : BinaryRealGL)
    (determinant : (Matrix.GeneralLinearGroup.det matrix).val = 1) (point : UpperHalfPlane) :
    cusp.realize vector (base * atInfinity (matrix * binarySymmetricSection point)) =
      binaryPhaseValue matrix point ^ weight * cuspScalarAffineRealization cusp vector base
        ((matrix • point : UpperHalfPlane) : ℂ) := by
  rw [binary_det_one_section_phase matrix determinant point, atInfinity_mul, ← mul_assoc,
    cuspRealization_right_eigenvector cusp vector _ _ (rotation (binaryIwasawaPhase matrix point))]
  rw [cuspScalarAffineRealization, binaryUpperSectionMatrix_coe, invertibleMatrix_coe, binaryPhaseValue_coe]

theorem cuspScalarWeightedRealization_bound (cusp : CuspidalRepresentation) (halfWeight : ℤ) (vector : cusp.smooth) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ (base : BinaryAdelicGL) (point : UpperHalfPlane),
      ‖cuspScalarWeightedRealization cusp halfWeight vector base point‖ ≤ point.im ^ halfWeight * bound := by
  obtain ⟨bound, bounded⟩ := cusp.bounded vector
  refine ⟨bound, (norm_nonneg _).trans (bounded 1), ?_⟩
  intro base point
  rw [cuspScalarWeightedRealization, norm_smul, Real.norm_eq_abs]
  change |point.im ^ halfWeight| * ‖cuspScalarAffineRealization cusp vector base point‖ ≤ point.im ^ halfWeight * bound
  rw [abs_of_pos (zpow_pos point.im_pos halfWeight)]
  exact mul_le_mul_of_nonneg_left (bounded _) (le_of_lt (zpow_pos point.im_pos halfWeight))

end TernaryPeriodPolynomials.SphericalDetection.Helpers
