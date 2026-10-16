module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.IwasawaPhase
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.TensorDifferential

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def binaryPhaseValue (matrix : BinaryRealGL) (point : ℂ) : ℂ :=
  UpperHalfPlane.denom matrix point / (‖UpperHalfPlane.denom matrix point‖ : ℂ)

theorem binaryPhaseValue_coe (matrix : BinaryRealGL) (point : UpperHalfPlane) :
    binaryPhaseValue matrix point = (binaryIwasawaPhase matrix point : ℂ) := rfl

theorem cuspRotationWeight_affine_transform (cusp : CuspidalRepresentation)
    (vector : cusp.H) (weight : ℤ)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
      (angle : ℂ) ^ weight • vector)
    (matrix : BinaryRealGL) (determinant : (Matrix.GeneralLinearGroup.det matrix).val = 1)
    (point : UpperHalfPlane) :
    cusp.π (atInfinity matrix) (cuspAffineOrbitVector cusp vector point) =
      binaryPhaseValue matrix point ^ weight • cuspAffineOrbitVector cusp vector ((matrix • point : UpperHalfPlane) : ℂ) := by
  rw [cuspAffineOrbitVector, binaryUpperSectionMatrix_coe, invertibleMatrix_coe]
  change (cusp.π (atInfinity matrix) * cusp.π (atInfinity (binarySymmetricSection point))) vector = _
  rw [← map_mul, ← atInfinity_mul, binary_det_one_section_phase matrix determinant point,
    atInfinity_mul, map_mul, Module.End.mul_apply, rotation, map_smul]
  rw [cuspAffineOrbitVector, binaryUpperSectionMatrix_coe, invertibleMatrix_coe, binaryPhaseValue_coe]

theorem binaryPhaseValue_contDiffOn (matrix : BinaryRealGL) {order : WithTop ℕ∞} :
    ContDiffOn ℝ order (binaryPhaseValue matrix) UpperHalfPlane.upperHalfPlaneSet := by
  have denominator : ContDiffOn ℝ order (UpperHalfPlane.denom matrix) UpperHalfPlane.upperHalfPlaneSet := by
    unfold UpperHalfPlane.denom
    fun_prop
  have nonzero : ∀ point ∈ UpperHalfPlane.upperHalfPlaneSet, UpperHalfPlane.denom matrix point ≠ 0 :=
    fun point member => UpperHalfPlane.denom_ne_zero matrix ⟨point, member⟩
  have norm_regular := denominator.norm ℂ nonzero
  have norm_complex_regular : ContDiffOn ℝ order
      (fun point => (‖UpperHalfPlane.denom matrix point‖ : ℂ)) UpperHalfPlane.upperHalfPlaneSet :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn norm_regular
  convert denominator.mul (norm_complex_regular.inv (fun point member =>
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (nonzero point member)))) using 1; rfl

theorem binaryPhaseValue_rotation_I (angle : Circle) :
    binaryPhaseValue (binaryRotations angle) Complex.I = (angle : ℂ) := by
  rw [binaryPhaseValue, binaryRotations_denom_I, Circle.norm_coe, Complex.ofReal_one, div_one]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
