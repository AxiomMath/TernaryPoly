module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.SphericalProjection
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationWeights

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem cuspSphericalProjection_finite_real (cusp : CuspidalRepresentation)
    (finite : BinaryFiniteGL) (real : BinaryRealGL) (vector : cusp.H) :
    cuspSphericalProjection cusp
        (cusp.π (atFinite finite) (cusp.π (atInfinity real) vector)) =
      cusp.π (atInfinity real)
        (cuspSphericalProjection cusp (cusp.π (atFinite finite) vector)) := by
  change cuspSphericalProjection cusp
      ((cusp.π (atFinite finite) * cusp.π (atInfinity real)) vector) = _
  rw [← map_mul, (atInfinity_commute_atFinite real finite).symm.eq, map_mul,
    Module.End.mul_apply, cuspSphericalProjection_real]

theorem cusp_exists_spherical_rotation_weight (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) (weight : ℤ) (vector : cusp.H) (nonzero : vector ≠ 0)
    (rotation : ∀ angle : Circle,
      cusp.π (atInfinity (binaryRotations angle)) vector = (angle : ℂ) ^ weight • vector) :
    ∃ spherical_vector : cusp.H, spherical_vector ≠ 0 ∧
      spherical_vector ∈ cuspSphericalValues cusp ∧
      ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) spherical_vector =
        (angle : ℂ) ^ weight • spherical_vector := by
  obtain ⟨finite, projected_nonzero⟩ :=
    cuspSphericalProjection_finite_nonzero cusp spherical vector nonzero
  refine ⟨cuspSphericalProjection cusp (cusp.π (atFinite finite) vector), projected_nonzero,
    cuspSphericalProjection_mem cusp _, ?_⟩
  intro angle
  rw [← cuspSphericalProjection_finite_real, rotation angle, map_smul, map_smul]

theorem cohomological_exists_spherical_rotation_weight (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree) :
    ∃ (vector : cusp.H) (weight : ℤ), vector ≠ 0 ∧ vector ∈ cuspSphericalValues cusp ∧
      (-(degree : ℤ) - 3 ≤ weight ∧ weight ≤ (degree : ℤ) - 1) ∧
      (Odd degree → Even weight) ∧
      ∀ angle : Circle, cusp.π (atInfinity (binaryRotations angle)) vector =
        (angle : ℂ) ^ weight • vector := by
  obtain ⟨level, vectors, _, _, nonzero, _, rotation⟩ :=
    cohomological_exists_rotation_eigenvector cusp spherical cohomological (binaryRotationBasis (degree + 1))
  obtain ⟨exponent, coordinate_nonzero⟩ := Function.ne_iff.mp nonzero
  obtain ⟨vector, vector_nonzero, fixed, weight⟩ := cusp_exists_spherical_rotation_weight cusp spherical
    (binaryCuspRotationWeight exponent) (vectors exponent) coordinate_nonzero
    (binaryRotation_eigenvector_coordinate cusp vectors rotation exponent)
  exact ⟨vector, binaryCuspRotationWeight exponent, vector_nonzero, fixed,
    binaryCuspRotationWeight_bounds exponent, fun odd => binaryCuspRotationWeight_even odd exponent, weight⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
