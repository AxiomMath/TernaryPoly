module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointPolynomial

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryAffineRootWeight (degree : ℕ) (halfWeight : ℤ)
    (weight : 2 * halfWeight = -((degree : ℤ) + 3)) (height : ℝ) (positive : 0 < height) :
    (1 / (Real.sqrt height : ℂ)) ^ (degree + 1) = (height ^ (halfWeight + 1) : ℝ) := by
  have real_equality : (1 / Real.sqrt height) ^ (degree + 1) = height ^ (halfWeight + 1) := by
    calc
      _ = Real.sqrt height ^ (-((degree + 1 : ℕ) : ℤ)) := by
        simp only [one_div, inv_pow, zpow_neg, zpow_natCast]
      _ = (Real.sqrt height ^ (2 : ℤ)) ^ (halfWeight + 1) := by
        rw [← zpow_mul]
        congr 1
        omega
      _ = _ := by rw [zpow_ofNat, Real.sq_sqrt positive.le]
  exact_mod_cast real_equality

theorem binaryAffineOrbitVector_single_zero (cusp : CuspidalRepresentation) (degree : ℕ)
    (vector : cusp.H) (point : ℂ) (positive : 0 < point.im) (position : Fin (degree + 2)) :
    binaryAffineOrbitVector cusp (binaryWeightBasis (degree + 1)) (Pi.single 0 vector) point position =
      ((1 / (Real.sqrt point.im : ℂ)) ^ (degree + 1) *
        (binaryWeightBasis (degree + 1)).coord position (binaryPointPower (degree + 1) point)) •
        cuspAffineOrbitVector cusp vector point := by
  rw [binaryAffineOrbitVector, binaryHilbertOperator_apply,
    binaryAffineSection_normalizingFactor point positive, one_smul, Fin.sum_univ_succ]
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne (Fin.succ_ne_zero _), map_zero, smul_zero,
    Finset.sum_const_zero, add_zero, binaryCoefficient_affine_first degree point positive, map_smul, smul_eq_mul]
  rfl

/-- The height factors cancel exactly at the cohomological weight. -/
theorem binaryAffineOrbitVector_single_weighted (cusp : CuspidalRepresentation) (degree : ℕ)
    (halfWeight : ℤ) (weight : 2 * halfWeight = -((degree : ℤ) + 3))
    (vector : cusp.H) (point : ℂ) (positive : 0 < point.im) (position : Fin (degree + 2)) :
    point.im⁻¹ •
        binaryAffineOrbitVector cusp (binaryWeightBasis (degree + 1)) (Pi.single 0 vector) point position =
      (binaryWeightBasis (degree + 1)).coord position (binaryPointPower (degree + 1) point) •
        cuspWeightedAffineOrbit cusp halfWeight vector point := by
  rw [binaryAffineOrbitVector_single_zero cusp degree vector point positive,
    binaryAffineRootWeight degree halfWeight weight point.im positive, mul_smul,
    Complex.coe_smul,
    smul_comm (point.im ^ (halfWeight + 1)), smul_comm point.im⁻¹, smul_smul,
    zpow_add₀ (ne_of_gt positive), zpow_one]
  have cancel : point.im⁻¹ * (point.im ^ halfWeight * point.im) = point.im ^ halfWeight := by
    field_simp
  rw [cancel]
  rfl

end TernaryPeriodPolynomials.SphericalDetection.Helpers
