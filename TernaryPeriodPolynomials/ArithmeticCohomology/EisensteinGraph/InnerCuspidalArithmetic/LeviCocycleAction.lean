module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ExplicitRadical

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def binaryIntegralComplex : GeneralLinearGroup (Fin 2) ℤ →* Binary.GL2 :=
  GeneralLinearGroup.map (Int.castRingHom ℂ)

theorem rationalCoefficientComponent_integral_val (degree : ℕ) (element : IntegralGL3)
    (polynomial : HomogeneousPoly degree) :
    (rationalCoefficientComponent degree trivialCharacter (integralRational element) polynomial).val =
      action (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) element) polynomial.val := by
  change ((1 : ℂ) • homogeneousAction degree (-1)
    (GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (GeneralLinearGroup.map (algebraMap ℚ ℝ)
        (GeneralLinearGroup.map (Int.castRingHom ℚ) element))) polynomial).val = _
  rw [one_smul]
  have matrices : GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (GeneralLinearGroup.map (algebraMap ℚ ℝ)
        (GeneralLinearGroup.map (Int.castRingHom ℚ) element)) =
      GeneralLinearGroup.map (Int.castRingHom ℂ) element := by
    apply Units.ext
    ext row column
    simp [GeneralLinearGroup.map_apply]
  rw [matrices]
  rfl

theorem standardBadLineRepresentation_binary (degree : ℕ)
    (element : ℤˣ × binaryArithmeticLevel) (polynomial : Binary.HomogeneousPoly degree) :
    standardBadLineRepresentation degree (SemidirectProduct.inr element)
      (binaryHomogeneousEmbedding degree polynomial) =
      (((element.1.val : ℂ) * (GeneralLinearGroup.det (binaryIntegralComplex element.2.val)).val)⁻¹ : ℂ) •
        binaryHomogeneousEmbedding degree
          (Binary.homogeneousAction degree 0 (binaryIntegralComplex element.2.val) polynomial) := by
  apply Subtype.ext
  change (rationalCoefficientComponent degree trivialCharacter
    (standardBadLineSemidirectEquiv (SemidirectProduct.inr element)).val
      (binaryHomogeneousEmbedding degree polynomial)).val = _
  rw [standardBadLineSemidirectEquiv_inr]
  change (rationalCoefficientComponent degree trivialCharacter
    (integralRational (lineLevi element.1 element.2.val))
      (binaryHomogeneousEmbedding degree polynomial)).val = _
  rw [rationalCoefficientComponent_integral_val, map_lineLevi]
  change action (-1) _ (binaryPolynomialEmbedding polynomial.val) = _
  rw [action_lineLevi_binary]
  change _ = _ • binaryPolynomialEmbedding
    (Binary.homogeneousAction degree 0 (binaryIntegralComplex element.2.val) polynomial).val
  rw [binaryUntwistedHomogeneous_val]
  rfl

theorem integralBadLine_inverse_conjAct_coordinates
    (element : ℤˣ × binaryArithmeticLevel) (radical : Multiplicative (ℤ × ℤ)) :
    (integralBadLineSplitting.conjAct element⁻¹ radical).toAdd =
      (element.1.inv * (radical.toAdd.1 * element.2.val.val 0 0 +
          radical.toAdd.2 * element.2.val.val 1 0),
        element.1.inv * (radical.toAdd.1 * element.2.val.val 0 1 +
          radical.toAdd.2 * element.2.val.val 1 1)) := by
  simpa using integralBadLine_conjAct_coordinates element⁻¹ radical

theorem leviCrossedAction_binaryPair (degree : ℕ) (element : ℤˣ × binaryArithmeticLevel)
    (pair : Binary.HomogeneousPoly degree × Binary.HomogeneousPoly degree) :
    leviCrossedAction integralBadLineSplitting.conjAct (standardBadLineRepresentation degree) element
      (explicitBinaryPairCocycle degree pair) =
      explicitBinaryPairCocycle degree
        (binaryMatrixPairAction degree (binaryIntegralComplex element.2.val) pair) := by
  apply Subtype.ext
  funext radical
  change standardBadLineRepresentation degree (SemidirectProduct.inr element)
    ((explicitBinaryPairCocycle degree pair).val
      (integralBadLineSplitting.conjAct element⁻¹ radical)) = _
  rw [explicitBinaryPairCocycle_apply, integralBadLine_inverse_conjAct_coordinates,
    map_add, map_smul, map_smul, standardBadLineRepresentation_binary,
    standardBadLineRepresentation_binary, explicitBinaryPairCocycle_apply]
  have inverse : element.1.inv = element.1.val := congrArg Units.val (Int.units_inv_eq_self element.1)
  have nonzero : (element.1.val : ℂ) ≠ 0 := by exact_mod_cast Units.ne_zero element.1
  have scalarCancel : (element.1.inv : ℂ) *
      (((element.1.val : ℂ) * (GeneralLinearGroup.det (binaryIntegralComplex element.2.val)).val)⁻¹) =
        (GeneralLinearGroup.det (binaryIntegralComplex element.2.val)).val⁻¹ := by
    rw [inverse, _root_.mul_inv_rev, mul_left_comm, mul_inv_cancel₀ nonzero, mul_one]
  change ((element.1.inv * (radical.toAdd.1 * element.2.val.val 0 0 +
      radical.toAdd.2 * element.2.val.val 1 0) : ℤ) : ℂ) •
      ((((element.1.val : ℂ) * (GeneralLinearGroup.det (binaryIntegralComplex element.2.val)).val)⁻¹) •
        binaryHomogeneousEmbedding degree
          (Binary.homogeneousAction degree 0 (binaryIntegralComplex element.2.val) pair.1)) +
    ((element.1.inv * (radical.toAdd.1 * element.2.val.val 0 1 +
      radical.toAdd.2 * element.2.val.val 1 1) : ℤ) : ℂ) •
      ((((element.1.val : ℂ) * (GeneralLinearGroup.det (binaryIntegralComplex element.2.val)).val)⁻¹) •
        binaryHomogeneousEmbedding degree
          (Binary.homogeneousAction degree 0 (binaryIntegralComplex element.2.val) pair.2)) = _
  simp only [Int.cast_mul, Int.cast_add, smul_smul]
  have cancel (value : ℂ) : ((element.1.inv : ℂ) * value) *
      (((element.1.val : ℂ) * (GeneralLinearGroup.det (binaryIntegralComplex element.2.val)).val)⁻¹) =
        value * (GeneralLinearGroup.det (binaryIntegralComplex element.2.val)).val⁻¹ := by
    rw [mul_right_comm, scalarCancel, mul_comm]
  rw [cancel, cancel]
  change _ = (radical.toAdd.1 : ℂ) • binaryHomogeneousEmbedding degree
      ((GeneralLinearGroup.det (binaryIntegralComplex element.2.val)).val⁻¹ •
        ((element.2.val.val 0 0 : ℂ) • Binary.homogeneousAction degree 0 (binaryIntegralComplex element.2.val) pair.1 +
          (element.2.val.val 0 1 : ℂ) • Binary.homogeneousAction degree 0 (binaryIntegralComplex element.2.val) pair.2)) +
    (radical.toAdd.2 : ℂ) • binaryHomogeneousEmbedding degree
      ((GeneralLinearGroup.det (binaryIntegralComplex element.2.val)).val⁻¹ •
        ((element.2.val.val 1 0 : ℂ) • Binary.homogeneousAction degree 0 (binaryIntegralComplex element.2.val) pair.1 +
          (element.2.val.val 1 1 : ℂ) • Binary.homogeneousAction degree 0 (binaryIntegralComplex element.2.val) pair.2))
  simp only [map_smul, map_add, smul_add, smul_smul, add_mul, add_smul]
  simp only [← mul_assoc,
    mul_right_comm _ (GeneralLinearGroup.det (binaryIntegralComplex element.2.val)).val⁻¹]
  exact add_add_add_comm _ _ _ _

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
