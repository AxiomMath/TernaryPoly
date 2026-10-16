module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.EisensteinNormSum
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.SubgroupCosetUnfolding
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.GroupAverages

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem integerSpecialLinearReal_injective :
    Function.Injective (SpecialLinearGroup.map (Int.castRingHom ℝ) (n := Fin 3)) := by
  intro first second equal
  apply Subtype.ext
  ext row column
  have entry := congrArg (fun matrix : SpecialLinearGroup (Fin 3) ℝ => matrix.val row column) equal
  change (first.val row column : ℝ) = (second.val row column : ℝ) at entry
  exact_mod_cast entry

noncomputable def principalIntegerRealEquiv : principalIntegerSpecialLinear ≃* principalRealSpecialLinear :=
  principalIntegerSpecialLinear.equivMapOfInjective (SpecialLinearGroup.map (Int.castRingHom ℝ))
    integerSpecialLinearReal_injective

theorem principalIntegerRealEquiv_val (matrix : principalIntegerSpecialLinear) :
    (principalIntegerRealEquiv matrix).val = SpecialLinearGroup.map (Int.castRingHom ℝ) matrix.val := rfl

def integerSpecialLinearRationalHom : SpecialLinearGroup (Fin 3) ℤ →* RationalGL3 :=
  (GeneralLinearGroup.map (Int.castRingHom ℚ)).comp SpecialLinearGroup.toGL

noncomputable def principalRealRationalHom : principalRealSpecialLinear →* RationalGL3 :=
  integerSpecialLinearRationalHom.comp
    (principalIntegerSpecialLinear.subtype.comp principalIntegerRealEquiv.symm.toMonoidHom)

theorem principalRealRationalHom_integer (matrix : principalIntegerSpecialLinear) :
    principalRealRationalHom (principalIntegerRealEquiv matrix) = integerSpecialLinearRationalHom matrix.val := by
  change integerSpecialLinearRationalHom (principalIntegerRealEquiv.symm (principalIntegerRealEquiv matrix)).val = _
  rw [principalIntegerRealEquiv.symm_apply_apply]

theorem principalRealRationalHom_real (matrix : principalRealSpecialLinear) :
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (principalRealRationalHom matrix) =
      SpecialLinearGroup.toGL matrix.val := by
  obtain ⟨integer, rfl⟩ := principalIntegerRealEquiv.surjective matrix
  rw [principalRealRationalHom_integer, principalIntegerRealEquiv_val]
  change GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (SpecialLinearGroup.toGL integer.val)) = _
  rw [integerGL3_map_map, specialLinear_toGL_map]

noncomputable instance principalRealFlagsMulAction : MulAction principalRealSpecialLinear (Flags .plane) :=
  MulAction.compHom (Flags .plane) principalRealRationalHom

theorem principalRealFlags_smul (matrix : principalRealSpecialLinear) (flag : Flags .plane) :
    matrix • flag = principalRealRationalHom matrix • flag := rfl

theorem normalized_eisensteinSummand_finite_level
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (level : finiteLevel)
    (matrix : AdelicGL) (flag : Flags .plane) :
    eisensteinSummand (unitaryNormalize degree family) parameter (matrix * atFinite level.val) flag =
      eisensteinSummand (unitaryNormalize degree family) parameter matrix flag := by
  change unitaryNormalize degree family parameter (rationalGroup flag.out⁻¹ * (matrix * atFinite level.val)) = _
  rw [← mul_assoc, unitaryNormalize_finite_level flat.1 parameter level]
  rfl

theorem normalized_eisensteinSummand_principal_slice_translate
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (integral : GL3 IntegralAdeles)
    (principal : principalRealSpecialLinear) (matrix : SpecialLinearGroup (Fin 3) ℝ) (flag : Flags .plane) :
    eisensteinSummand (unitaryNormalize degree family) parameter
      (realSpecialIntegralSlice integral (principal.val * matrix)) flag =
      eisensteinSummand (unitaryNormalize degree family) parameter
        (realSpecialIntegralSlice integral matrix) (principal⁻¹ • flag) := by
  obtain ⟨integer, rfl⟩ := principalIntegerRealEquiv.surjective principal
  let realPart := GeneralLinearGroup.map (Int.castRingHom ℝ) (SpecialLinearGroup.toGL integer.val)
  let finitePart := GeneralLinearGroup.map (Int.castRingHom FiniteAdeles) (SpecialLinearGroup.toGL integer.val)
  let point := realSpecialIntegralSlice integral matrix
  have finite_eq : finiteGroup point = GeneralLinearGroup.map integralEmbedding integral := by
    simp only [point, realSpecialIntegralSlice, map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul]
  have level : (finiteGroup point)⁻¹ * finitePart * finiteGroup point ∈ finiteLevel := by
    rw [finite_eq]
    exact principalIntegerSpecialLinear_finite_conjugate integer integral
  have identity : (atInfinity realPart * point) * atFinite ((finiteGroup point)⁻¹ * finitePart * finiteGroup point) =
      rationalGroup (integerSpecialLinearRationalHom integer.val) * point := by
    rw [integerSpecialLinearRationalHom, MonoidHom.comp_apply, integerGL3_adelic_factor]
    change (atInfinity realPart * point) * atFinite ((finiteGroup point)⁻¹ * finitePart * finiteGroup point) =
      (atInfinity realPart * atFinite finitePart) * point
    simp only [mul_assoc]
    rw [atFinite_left_conjugate]
    simp only [mul_assoc]
  have finite_identity := normalized_eisensteinSummand_finite_level flat parameter ⟨_, level⟩
    (atInfinity realPart * point) flag
  rw [identity, normalized_eisensteinSummand_rational_translate flat] at finite_identity
  rw [realSpecialIntegralSlice_left_mul, principalIntegerRealEquiv_val, ← specialLinear_toGL_map,
    principalRealFlags_smul, map_inv, principalRealRationalHom_integer]
  exact finite_identity.symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
