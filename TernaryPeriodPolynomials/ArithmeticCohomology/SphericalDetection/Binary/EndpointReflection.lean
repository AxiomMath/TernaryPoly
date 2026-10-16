module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ReflectionCoefficient

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryRelativeEndpoints_reflection (cusp : CuspidalRepresentation) (spherical : SphericalCusp cusp)
    {degree : ℕ} (odd : Odd degree) (cohomological : Cohomological cusp degree)
    (level : Subgroup BinaryFiniteGL)
    (cycle : groupCohomology.cocycles₁ (binaryHilbertFiniteRep cusp spherical (binaryWeightBasis (degree + 1)) level))
    (regular : ContDiffOn ℝ (↑(⊤ : ℕ∞))
      (binaryUpperPotential cusp spherical (binaryWeightBasis (degree + 1)) level cycle) UpperHalfPlane.upperHalfPlaneSet)
    (rotations_zero : ∀ angle : Circle, cycle (binaryRotations angle) = 0)
    (lower upper : binarySmoothValues cusp (Fin (degree + 2)))
    (lower_value : binarySmoothValues_val cusp lower =
      binaryHolomorphicTangent cusp spherical (binaryWeightBasis (degree + 1)) level cycle)
    (upper_value : binarySmoothValues_val cusp upper =
      fderiv ℝ (binaryUpperPotential cusp spherical (binaryWeightBasis (degree + 1)) level cycle) Complex.I 1 +
        Complex.I • fderiv ℝ (binaryUpperPotential cusp spherical (binaryWeightBasis (degree + 1)) level cycle) Complex.I Complex.I)
    (support : ∀ position : Fin (degree + 1), lower position.succ = 0) :
    (upper (Fin.last (degree + 1))).val = cusp.π (atInfinity UpperHalfPlane.J) (lower 0).val := by
  have reflection_zero := binaryRelativeCycle_reflection_zero cusp spherical odd cohomological level cycle rotations_zero
  have differentiable := (regular.differentiableOn (by simp)).differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (show 0 < Complex.I.im by simp))
  have tangents := binaryRelativeTangents_reflection cusp spherical (binaryWeightBasis (degree + 1)) level cycle
    reflection_zero differentiable
  rw [← upper_value, ← lower_value] at tangents
  have endpoint := congrFun tangents (Fin.last (degree + 1))
  change (upper (Fin.last (degree + 1))).val =
    -(binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) UpperHalfPlane.J
      (binarySmoothValues_val cusp lower) (Fin.last (degree + 1))) at endpoint
  rw [binaryHilbertOperator_reflection_supported_first cusp odd _ (fun position =>
    congrArg Subtype.val (support position)), neg_neg] at endpoint
  exact endpoint

theorem binaryClassicalEndpoints_eq_of_reflection (cusp : CuspidalRepresentation) (halfWeight : ℤ)
    (lower upper : cuspAffineSmoothValues cusp) (first second : cuspClassicalVectors cusp halfWeight)
    (first_eq : first.val.val = lower.val)
    (second_eq : second.val.val = cusp.π (atInfinity UpperHalfPlane.J) upper.val)
    (reflection : upper.val = cusp.π (atInfinity UpperHalfPlane.J) lower.val) : second = first := by
  apply Subtype.ext
  apply Subtype.ext
  rw [second_eq, reflection, first_eq]
  change (cusp.π (atInfinity UpperHalfPlane.J) * cusp.π (atInfinity UpperHalfPlane.J)) lower.val = lower.val
  rw [← map_mul, ← atInfinity_mul, show UpperHalfPlane.J * UpperHalfPlane.J = 1 from by
    simpa only [pow_two] using UpperHalfPlane.J_sq, atInfinity_one, map_one]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
