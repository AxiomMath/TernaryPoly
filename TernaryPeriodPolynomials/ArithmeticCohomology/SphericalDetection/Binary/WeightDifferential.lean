module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.PhaseDerivative

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspRotationWeight_differential (cusp : CuspidalRepresentation)
    (vector : cusp.H) (weight : ℤ)
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (cuspAffineOrbitVector cusp vector) UpperHalfPlane.upperHalfPlaneSet)
    (rotation : ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector)
    (angle : Circle) (direction : ℂ) :
    cusp.π (atInfinity (binaryRotations angle))
        (fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I direction) =
      (angle : ℂ) ^ weight •
        fderiv ℝ (cuspAffineOrbitVector cusp vector) Complex.I (((angle : ℂ) ^ 2)⁻¹ * direction) +
      ((weight : ℂ) * (angle : ℂ) ^ (weight - 1) * binaryRotationPhaseDerivative angle direction) • vector := by
  let orbit := cuspAffineOrbitVector cusp vector
  let moebius : ℂ → ℂ := fun point => ((binaryRotations angle • UpperHalfPlane.ofComplex point : UpperHalfPlane) : ℂ)
  have moebius_value : moebius Complex.I = Complex.I := by
    simp only [moebius, ← UpperHalfPlane.coe_I, UpperHalfPlane.ofComplex_apply, binaryRotations_smul_I]
  have moebius_derivative : HasFDerivAt moebius
      (UpperHalfPlane.smulFDeriv (binaryRotations angle) Complex.I) Complex.I :=
    (UpperHalfPlane.hasStrictFDerivAt_smul (binaryRotations angle) UpperHalfPlane.I).hasFDerivAt
  have orbit_derivative := ((regular.contDiffAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds
    (show Complex.I.im > 0 by simp))).differentiableAt (by simp)).hasFDerivAt
  have line_derivative := complexAffineLine_hasDerivAt direction
  have orbit_line := orbit_derivative.comp_hasDerivAt_of_eq 0 line_derivative (by simp)
  have left_derivative := ((cuspUnitaryOperator cusp (atInfinity (binaryRotations angle))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 orbit_line
  have moebius_line := moebius_derivative.comp_hasDerivAt_of_eq 0 line_derivative (by simp)
  have orbit_moebius := orbit_derivative.comp_hasDerivAt_of_eq 0 moebius_line (by
    simp only [Function.comp_apply, zero_smul, add_zero, moebius_value])
  have right_derivative := (binaryRotationPhase_zpow_hasDerivAt angle direction weight).smul orbit_moebius
  have equality :
      (fun parameter : ℝ => cusp.π (atInfinity (binaryRotations angle)) (orbit (Complex.I + parameter • direction))) =ᶠ[nhds 0]
      (fun parameter : ℝ => binaryPhaseValue (binaryRotations angle) (Complex.I + parameter • direction) ^ weight •
        orbit (moebius (Complex.I + parameter • direction))) := by
    filter_upwards [binaryAffineLine_eventually_positive direction] with parameter positive
    have transform := cuspRotationWeight_affine_transform cusp vector weight rotation
      (binaryRotations angle) (binaryRotations_det angle) (⟨Complex.I + parameter • direction, positive⟩ : UpperHalfPlane)
    simpa only [orbit, moebius, UpperHalfPlane.ofComplex_apply_of_im_pos positive] using transform
  have same_derivative := left_derivative.unique (right_derivative.congr_of_eventuallyEq equality)
  simp only [Function.comp_apply, zero_smul, add_zero, binaryPhaseValue_rotation_I,
    moebius_value, cuspAffineOrbitVector_I, binaryRotations_smulFDeriv] at same_derivative
  exact same_derivative

end TernaryPeriodPolynomials.SphericalDetection.Helpers
