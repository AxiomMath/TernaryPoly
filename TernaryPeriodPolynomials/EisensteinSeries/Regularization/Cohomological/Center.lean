module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.Action

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem binaryValues_smul
    {cusp : CuspidalRepresentation} {degree : ℕ}
    {values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)}
    (values_cuspidal : BinaryValues cusp degree values) (scalar : ℂ) :
    BinaryValues cusp degree (fun groupElement => scalar • values groupElement) := by
  intro monomial
  simpa only [Submodule.coe_smul_of_tower, MvPolynomial.coeff_smul, Pi.smul_def]
    using (cuspFunctions cusp).smul_mem scalar (values_cuspidal monomial)

theorem binaryValues_central
    {cusp : CuspidalRepresentation} {degree : ℕ}
    {values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)}
    (values_cuspidal : BinaryValues cusp degree values)
    (idele : Adelesˣ) (groupElement : BinaryAdelicGL) :
    values (groupElement * GeneralLinearGroup.scalar (Fin 2) idele) =
      cusp.centralCharacter idele • values groupElement := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro monomial
  obtain ⟨vector, realized⟩ := values_cuspidal monomial
  have central_value := cusp.central idele vector groupElement
  rw [GeneralLinearGroup.scalar_commute] at central_value
  simpa only [congrFun realized, Submodule.coe_smul_of_tower,
    MvPolynomial.coeff_smul, smul_eq_mul] using central_value

theorem atInfinity_scalar (scalar : ℝˣ) :
    atInfinity (GeneralLinearGroup.scalar (Fin 2) scalar) =
      GeneralLinearGroup.scalar (Fin 2) (realAdeleUnit scalar) := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [atInfinity, combineGL, pairMatrix, realAdeleUnit,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

theorem binaryCohomologicalAction_scalar
    {cusp : CuspidalRepresentation} {degree : ℕ}
    {values : BinaryAdelicGL → Binary.HomogeneousPoly (degree + 1)}
    (values_cuspidal : BinaryValues cusp degree values)
    (scalar : ℝˣ) (groupElement : BinaryAdelicGL) :
    binaryCohomologicalAction degree (GeneralLinearGroup.scalar (Fin 2) scalar)
        values groupElement =
      (normPower (realAdeleUnit scalar) ((degree : ℂ) + 3) *
        ((scalar.val : ℂ) ^ (-2 : ℤ) * ((scalar.val : ℂ)⁻¹) ^ (degree + 1)) *
        cusp.centralCharacter (realAdeleUnit scalar)) • values groupElement := by
  unfold binaryCohomologicalAction binaryCoefficient
  rw [atInfinity_scalar, GeneralLinearGroup.det_scalar, Fintype.card_fin,
    normPower_pow, GeneralLinearGroup.map_scalar,
    binary_homogeneous_action_scalar, binaryValues_central values_cuspidal]
  simp only [smul_smul, Nat.cast_ofNat]
  have exponent : (2 : ℂ) * (((degree : ℂ) + 3) / 2) = (degree : ℂ) + 3 := by ring
  rw [exponent]
  simp only [Units.coe_map, Int.reduceMul, mul_assoc]
  rfl

theorem cohomological_central_scalar
    {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (scalar : ℝˣ) :
    normPower (realAdeleUnit scalar) ((degree : ℂ) + 3) *
      ((scalar.val : ℂ) ^ (-2 : ℤ) * ((scalar.val : ℂ)⁻¹) ^ (degree + 1)) *
      cusp.centralCharacter (realAdeleUnit scalar) = 1 := by
  let multiplier : ℂ :=
    normPower (realAdeleUnit scalar) ((degree : ℂ) + 3) *
      ((scalar.val : ℂ) ^ (-2 : ℤ) * ((scalar.val : ℂ)⁻¹) ^ (degree + 1)) *
      cusp.centralCharacter (realAdeleUnit scalar)
  change multiplier = 1
  by_contra multiplier_ne
  have multiplier_sub_ne : multiplier - 1 ≠ 0 := sub_ne_zero.mpr multiplier_ne
  obtain ⟨cocycle, cusp_values, _, _, cocycle_identity, not_coboundary⟩ := cohomological
  let center := GeneralLinearGroup.scalar (Fin 2) scalar
  apply not_coboundary
  refine ⟨fun groupElement => (multiplier - 1)⁻¹ • cocycle center groupElement,
    binaryValues_smul (cusp_values center) _, ?_⟩
  intro realElement groupElement
  have commute_identity := cocycle_identity center realElement groupElement
  rw [GeneralLinearGroup.scalar_commute,
    cocycle_identity realElement center groupElement] at commute_identity
  rw [binaryCohomologicalAction_scalar (cusp_values realElement)] at commute_identity
  change cocycle realElement groupElement +
      binaryCohomologicalAction degree realElement (cocycle center) groupElement =
    cocycle center groupElement + multiplier • cocycle realElement groupElement
      at commute_identity
  have difference_identity :
      binaryCohomologicalAction degree realElement (cocycle center) groupElement -
        cocycle center groupElement =
      (multiplier - 1) • cocycle realElement groupElement := by
    rw [_root_.sub_smul multiplier (1 : ℂ) (cocycle realElement groupElement), one_smul]
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using commute_identity)
  change cocycle realElement groupElement =
    binaryCohomologicalAction degree realElement
      (fun groupElement => (multiplier - 1)⁻¹ • cocycle center groupElement) groupElement - _
  have action_smul : binaryCohomologicalAction degree realElement
      (fun groupElement => (multiplier - 1)⁻¹ • cocycle center groupElement) groupElement =
      (multiplier - 1)⁻¹ •
        binaryCohomologicalAction degree realElement (cocycle center) groupElement := by
    simp only [binaryCohomologicalAction, map_smul]
    exact smul_comm _ _ _
  rw [action_smul]
  dsimp only
  rw [← _root_.smul_sub (multiplier - 1)⁻¹
    (binaryCohomologicalAction degree realElement (cocycle center) groupElement)
    (cocycle center groupElement), difference_identity, smul_smul,
    inv_mul_cancel₀ multiplier_sub_ne, one_smul]

theorem normPower_ofReal (idele : Adelesˣ) (exponent : ℝ) :
    normPower idele (exponent : ℂ) =
      (Real.exp (exponent * Real.log (adeleNorm idele : ℝ)) : ℂ) := by
  simp only [normPower, ← Complex.ofReal_mul, Complex.ofReal_exp]

theorem cohomological_centralCharacter_positive
    {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree)
    (scalar : ℝˣ) (scalar_positive : 0 < scalar.val) :
    cusp.centralCharacter (realAdeleUnit scalar) = 1 := by
  let factor : ℝ :=
    Real.exp (((degree : ℝ) + 3) * Real.log (adeleNorm (realAdeleUnit scalar) : ℝ)) *
      (scalar.val ^ (-2 : ℤ) * (scalar.val⁻¹) ^ (degree + 1))
  have factor_positive : 0 < factor := by
    dsimp [factor]
    positivity
  have central_identity : (factor : ℂ) * cusp.centralCharacter (realAdeleUnit scalar) = 1 := by
    have identity := cohomological_central_scalar cohomological scalar
    have exponent : (degree : ℂ) + 3 = (((degree : ℝ) + 3 : ℝ) : ℂ) := by simp
    rw [exponent, normPower_ofReal] at identity
    simpa only [factor, Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_pow,
      Complex.ofReal_inv] using identity
  have factor_one : factor = 1 := by
    have norm_identity := congrArg norm central_identity
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos factor_positive, cusp.centralUnitary, mul_one, norm_one] using norm_identity
  simpa only [factor_one, Complex.ofReal_one, one_mul] using central_identity

theorem adeleNorm_real_neg_one :
    adeleNorm (realAdeleUnit (-1 : ℝˣ)) = 1 := by
  have square_one :
      realAdeleUnit (-1 : ℝˣ) * realAdeleUnit (-1 : ℝˣ) = 1 := by
    apply Units.ext
    simp [realAdeleUnit]
  have norm_square := congrArg (fun idele => (adeleNorm idele : ℝ)) square_one
  simp only [map_mul, NNReal.coe_mul, map_one, NNReal.coe_one] at norm_square
  apply NNReal.coe_injective
  have norm_nonnegative := (adeleNorm (realAdeleUnit (-1 : ℝˣ))).coe_nonneg
  change (adeleNorm (realAdeleUnit (-1 : ℝˣ)) : ℝ) = 1
  nlinarith

theorem cohomological_centralCharacter_neg_one
    {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) :
    cusp.centralCharacter (realAdeleUnit (-1 : ℝˣ)) = (-1 : ℂ) ^ (degree + 1) := by
  have central_identity := cohomological_central_scalar cohomological (-1 : ℝˣ)
  have norm_power_one (exponent : ℂ) :
      normPower (realAdeleUnit (-1 : ℝˣ)) exponent = 1 := by
    simp [normPower, adeleNorm_real_neg_one]
  norm_num only [norm_power_one, Units.val_neg, Units.val_one, Complex.ofReal_neg,
    Complex.ofReal_one, zpow_neg, neg_one_sq, inv_one, inv_neg, one_mul]
    at central_identity
  have sign_square :
      (-1 : ℂ) ^ (degree + 1) * (-1 : ℂ) ^ (degree + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  apply mul_left_cancel₀ (pow_ne_zero (degree + 1) (by norm_num : (-1 : ℂ) ≠ 0))
  exact central_identity.trans sign_square.symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
