module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RotationWeights

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryWeightBasis_apply (degree : ℕ) (position : Fin (degree + 1)) :
    binaryWeightBasis degree position = binaryRotationBasis degree (binaryWeightExponent degree position) :=
  Module.Basis.reindex_apply _ _ _

theorem binaryWeightBasis_coefficient (degree : ℕ) (angle : Circle) (position : Fin (degree + 2)) :
    binaryCoefficient degree (binaryRotations angle) (binaryWeightBasis (degree + 1) position) =
      (angle : ℂ) ^ (((degree + 1 : ℕ) : ℤ) - 2 * (position.val : ℤ)) • binaryWeightBasis (degree + 1) position := by
  rw [binaryWeightBasis_apply, binaryRotationBasis_coefficient,
    binaryWeightExponent_first, binaryWeightExponent_second]
  have nonzero : (angle : ℂ) ≠ 0 := by
    intro zero
    have norm := Circle.norm_coe angle
    rw [zero, norm_zero] at norm
    exact zero_ne_one norm
  have scalar : ((angle : ℂ)⁻¹) ^ position.val * (angle : ℂ) ^ (degree + 1 - position.val) =
      (angle : ℂ) ^ (((degree + 1 : ℕ) : ℤ) - 2 * (position.val : ℤ)) := by
    calc
      _ = (angle : ℂ) ^ (-(position.val : ℤ)) * (angle : ℂ) ^ ((degree + 1 - position.val : ℕ) : ℤ) := by
        simp only [zpow_neg, zpow_natCast, inv_pow]
      _ = (angle : ℂ) ^ (-(position.val : ℤ) + ((degree + 1 - position.val : ℕ) : ℤ)) :=
        (zpow_add₀ nonzero _ _).symm
      _ = _ := by congr 1; omega
  rw [scalar]

theorem binaryHilbertOperator_weightBasis_rotation (cusp : CuspidalRepresentation) (degree : ℕ)
    (angle : Circle) (vector : Fin (degree + 2) → cusp.H) (position : Fin (degree + 2)) :
    binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) (binaryRotations angle) vector position =
      (angle : ℂ) ^ (((degree + 1 : ℕ) : ℤ) - 2 * (position.val : ℤ)) •
        cusp.π (atInfinity (binaryRotations angle)) (vector position) := by
  rw [binaryHilbertOperator_apply, binaryRotations_normalizingFactor, one_smul]
  simp [binaryWeightBasis_coefficient, Module.Basis.coord_apply, Finsupp.single_apply]

theorem binaryWeightBasis_eigenvector_coordinate (cusp : CuspidalRepresentation) (degree : ℕ) (weight : ℤ)
    (vector : Fin (degree + 2) → cusp.H)
    (rotation : ∀ angle : Circle,
      binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) (binaryRotations angle) vector =
        (angle : ℂ) ^ weight • vector)
    (position : Fin (degree + 2)) (angle : Circle) :
    cusp.π (atInfinity (binaryRotations angle)) (vector position) =
      (angle : ℂ) ^ binaryUnitaryWeight degree weight position • vector position := by
  have nonzero : (angle : ℂ) ≠ 0 := by
    intro zero
    have norm := Circle.norm_coe angle
    rw [zero, norm_zero] at norm
    exact zero_ne_one norm
  have coordinate := congrFun (rotation angle) position
  rw [binaryHilbertOperator_weightBasis_rotation, Pi.smul_apply] at coordinate
  have scalar : ((angle : ℂ) ^ (((degree + 1 : ℕ) : ℤ) - 2 * (position.val : ℤ)))⁻¹ * (angle : ℂ) ^ weight =
      (angle : ℂ) ^ binaryUnitaryWeight degree weight position := by
    rw [← zpow_neg, ← zpow_add₀ nonzero]
    congr 1
    unfold binaryUnitaryWeight
    omega
  calc
    _ = ((angle : ℂ) ^ (((degree + 1 : ℕ) : ℤ) - 2 * (position.val : ℤ)))⁻¹ •
        ((angle : ℂ) ^ (((degree + 1 : ℕ) : ℤ) - 2 * (position.val : ℤ)) •
          cusp.π (atInfinity (binaryRotations angle)) (vector position)) :=
      (inv_smul_smul₀ (zpow_ne_zero _ nonzero) _).symm
    _ = _ := by rw [coordinate, smul_smul, scalar]

theorem binaryWeightBasis_eigenvector_of_coordinates (cusp : CuspidalRepresentation) (degree : ℕ) (weight : ℤ)
    (vector : Fin (degree + 2) → cusp.H)
    (rotation : ∀ position angle, cusp.π (atInfinity (binaryRotations angle)) (vector position) =
      (angle : ℂ) ^ binaryUnitaryWeight degree weight position • vector position) (angle : Circle) :
    binaryHilbertOperator cusp (binaryWeightBasis (degree + 1)) (binaryRotations angle) vector =
      (angle : ℂ) ^ weight • vector := by
  have nonzero : (angle : ℂ) ≠ 0 := by
    intro zero
    have norm := Circle.norm_coe angle
    rw [zero, norm_zero] at norm
    exact zero_ne_one norm
  funext position
  rw [binaryHilbertOperator_weightBasis_rotation, rotation, smul_smul, ← zpow_add₀ nonzero]
  have exponent : (((degree + 1 : ℕ) : ℤ) - 2 * (position.val : ℤ)) +
      binaryUnitaryWeight degree weight position = weight := by unfold binaryUnitaryWeight; omega
  rw [exponent]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
