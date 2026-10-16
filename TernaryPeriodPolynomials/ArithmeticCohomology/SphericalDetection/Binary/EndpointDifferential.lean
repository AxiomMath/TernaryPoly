module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointReflection

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realLinear_holomorphic_decomposition {E : Type} [AddCommGroup E] [Module ℂ E]
    [Module ℝ E] [IsScalarTower ℝ ℂ E] (linear : ℂ →ₗ[ℝ] E) (direction : ℂ) :
    linear direction = (2 : ℂ)⁻¹ •
      (direction • (linear 1 - Complex.I • linear Complex.I) +
        (starRingEnd ℂ direction) • (linear 1 + Complex.I • linear Complex.I)) := by
  rw [realLinear_complex_coordinates]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have real_part : (2 : ℂ)⁻¹ * (direction + starRingEnd ℂ direction) = (direction.re : ℂ) := by
    apply Complex.ext <;> simp
    ring
  have imaginary_part : (2 : ℂ)⁻¹ *
      (-direction * Complex.I + starRingEnd ℂ direction * Complex.I) = (direction.im : ℂ) := by
    apply Complex.ext <;> simp
    ring
  calc
    _ = ((2 : ℂ)⁻¹ * (direction + starRingEnd ℂ direction)) • linear 1 +
        ((2 : ℂ)⁻¹ * (-direction * Complex.I + starRingEnd ℂ direction * Complex.I)) •
          linear Complex.I := by rw [real_part, imaginary_part]; rfl
    _ = _ := by module

variable {degree : ℕ} {index : Type} [Fintype index]

/-- The full real differential is determined by the lower tangent, including the reflection sign. -/
theorem binaryUpperPotential_fderiv_from_lower (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp)
    (basis : Module.Basis index ℂ (Binary.HomogeneousPoly (degree + 1)))
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical basis level))
    (regular : DifferentiableOn ℝ (binaryUpperPotential cusp spherical basis level cycle)
      UpperHalfPlane.upperHalfPlaneSet)
    (stabilizer_zero : ∀ matrix : BinaryRealGL,
      matrix • UpperHalfPlane.I = UpperHalfPlane.I → cycle matrix = 0)
    (point : UpperHalfPlane) (direction : ℂ) :
    fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) (point : ℂ) direction =
      point.im⁻¹ • binaryAffineOrbitVector cusp basis
        ((2 : ℂ)⁻¹ •
          (direction • binaryHolomorphicTangent cusp spherical basis level cycle -
            (starRingEnd ℂ direction) • binaryHilbertOperator cusp basis UpperHalfPlane.J
              (binaryHolomorphicTangent cusp spherical basis level cycle))) point := by
  have base_regular := regular.differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show 0 < Complex.I.im by simp))
  have reflected := binaryRelativeTangents_reflection cusp spherical basis level cycle
    (stabilizer_zero UpperHalfPlane.J binaryReflection_smul_I) base_regular
  have decomposition := realLinear_holomorphic_decomposition
    (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I).toLinearMap direction
  change fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I direction =
    (2 : ℂ)⁻¹ • (direction • binaryHolomorphicTangent cusp spherical basis level cycle +
      (starRingEnd ℂ direction) •
        (fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I 1 +
          Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical basis level cycle) Complex.I Complex.I))
    at decomposition
  rw [reflected, smul_neg, ← sub_eq_add_neg] at decomposition
  have transported := binaryAffineOrbitVector_tangent cusp spherical basis level cycle regular
    stabilizer_zero point direction
  rw [decomposition] at transported
  rw [transported, inv_smul_smul₀ (ne_of_gt point.im_pos)]

end TernaryPeriodPolynomials.SphericalDetection.Helpers
