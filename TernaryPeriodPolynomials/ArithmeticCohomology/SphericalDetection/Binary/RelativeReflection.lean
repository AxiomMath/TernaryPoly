module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ClassicalEndpoints

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryHilbertRotationInvariant_zero (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    {degree : ℕ} (odd : Odd degree) (cohomological : Cohomological cusp degree)
    (vector : Fin (degree + 2) → cusp.H)
    (rotation : ∀ angle : Circle,
      binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) (binaryRotations angle) vector = vector) :
    vector = 0 := by
  have character : ∀ angle : Circle,
      binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) (binaryRotations angle) vector =
        (angle : ℂ) ^ (0 : ℤ) • vector := by simpa only [zpow_zero, one_smul] using rotation
  funext position
  apply cohomological_cusp_weight_gap cusp spherical odd cohomological _ _ _ _
    (binaryWeightBasis_eigenvector_coordinate cusp degree 0 vector character position)
  · simp only [binaryUnitaryWeight]; omega
  · simp only [binaryUnitaryWeight]; omega

theorem binaryRelativeCycle_reflection_zero (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    {degree : ℕ} (odd : Odd degree) (cohomological : Cohomological cusp degree)
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical (binaryWeightBasis (degree + 1)) level))
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0) :
    cycle UpperHalfPlane.J = 0 := by
  apply Subtype.ext
  apply binaryHilbertRotationInvariant_zero cusp spherical odd cohomological
  intro angle
  exact congrArg Subtype.val (cocycle_normalizer_fixed _ cycle (binaryRotations angle) UpperHalfPlane.J
    (binaryRotations angle⁻¹) (binaryRotation_mul_reflection angle) (rotations_zero angle) (rotations_zero angle⁻¹))

theorem binaryUpperPotential_reflection {degree : ℕ} {index : Type} [Fintype index]
    (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (reflection_zero : cycle UpperHalfPlane.J = 0) (point : ℂ) (positive : 0 < point.im) :
    binaryUpperPotential cusp spherical basis level cycle point =
      binaryHilbertOperator cusp basis UpperHalfPlane.J
        (binaryUpperPotential cusp spherical basis level cycle (binaryComplexReflection point)) := by
  let upper : UpperHalfPlane := ⟨point, positive⟩
  let reflected : UpperHalfPlane :=
    ⟨binaryComplexReflection point, by rw [binaryComplexReflection_im]; exact positive⟩
  have first := cocycle_right_eq_of_zero _ cycle (binarySymmetricSection upper) UpperHalfPlane.J reflection_zero
  have second := (groupCohomology.mem_cocycles₁_iff _).mp cycle.property UpperHalfPlane.J (binarySymmetricSection reflected)
  change cycle (UpperHalfPlane.J * binarySymmetricSection reflected) =
    (binaryHilbertFiniteRep cusp spherical basis level).ρ UpperHalfPlane.J (cycle (binarySymmetricSection reflected)) +
      cycle UpperHalfPlane.J at second
  rw [reflection_zero, add_zero] at second
  rw [binarySymmetricSection_mul_reflection] at first
  have equality := first.symm.trans second
  change (cycle (invertibleMatrix (binaryUpperSectionMatrix point)) : binaryHilbertFiniteValues cusp level).val = _
  rw [binaryUpperSectionMatrix_coe upper, invertibleMatrix_coe]
  change _ = binaryHilbertOperator cusp basis UpperHalfPlane.J
    (cycle (invertibleMatrix (binaryUpperSectionMatrix (binaryComplexReflection point))) : binaryHilbertFiniteValues cusp level).val
  rw [binaryUpperSectionMatrix_coe reflected, invertibleMatrix_coe]
  exact congrArg Subtype.val equality

theorem binaryUpperPotential_reflection_fderiv {degree : ℕ} {index : Type} [Fintype index]
    (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (reflection_zero : cycle UpperHalfPlane.J = 0)
    (regular : DifferentiableAt ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I)
    (direction : ℂ) :
    fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction =
      binaryHilbertOperator cusp basis UpperHalfPlane.J
        (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I
          (binaryComplexReflection direction)) := by
  have derivative := ((binaryHilbertOperator cusp basis UpperHalfPlane.J).restrictScalars ℝ).hasFDerivAt.comp Complex.I
    ((show HasFDerivAt (binaryUpperPotential cusp spherical basis level cycle)
      (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I) (binaryComplexReflection Complex.I) by
        rw [binaryComplexReflection_basepoint]; exact regular.hasFDerivAt).comp Complex.I binaryComplexReflection.hasFDerivAt)
  have equality : (fun point => binaryHilbertOperator cusp basis UpperHalfPlane.J
      (binaryUpperPotential cusp spherical basis level cycle (binaryComplexReflection point))) =ᶠ[nhds Complex.I]
      binaryUpperPotential cusp spherical basis level cycle := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show 0 < Complex.I.im by simp)] with point positive
    exact (binaryUpperPotential_reflection cusp spherical basis level cycle reflection_zero point positive).symm
  exact congrArg (fun differential : ℂ →L[ℝ] (index → cusp.H) => differential direction)
    (derivative.congr_of_eventuallyEq equality.symm).fderiv

theorem binaryRelativeTangents_reflection {degree : ℕ} {index : Type} [Fintype index]
    (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (reflection_zero : cycle UpperHalfPlane.J = 0)
    (regular : DifferentiableAt ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I) :
    fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 +
        Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I =
      -binaryHilbertOperator cusp basis UpperHalfPlane.J
        (binaryHolomorphicTangent cusp spherical basis level cycle) := by
  have horizontal := binaryUpperPotential_reflection_fderiv cusp spherical basis level cycle reflection_zero regular 1
  have vertical := binaryUpperPotential_reflection_fderiv cusp spherical basis level cycle reflection_zero regular Complex.I
  have reflected_one : binaryComplexReflection 1 = -1 := by simp [binaryComplexReflection]
  rw [reflected_one, map_neg, map_neg] at horizontal
  rw [binaryComplexReflection_basepoint] at vertical
  simp only [binaryHolomorphicTangent, map_sub, map_smul]
  rw [← neg_eq_iff_eq_neg.mpr horizontal, ← vertical]
  module

end TernaryPeriodPolynomials.SphericalDetection.Helpers
