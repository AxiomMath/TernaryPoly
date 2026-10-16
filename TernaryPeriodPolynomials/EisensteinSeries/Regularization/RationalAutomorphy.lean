module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Normalized.Continuation
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.ParabolicFactorization

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem induced_binary_rational
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (rationalMatrix : BinaryRationalGL) (groupElement : AdelicGL) :
    sectionValue (planeLevi (GeneralLinearGroup.map rationalAdele rationalMatrix) 1 *
      groupElement) = sectionValue groupElement := by
  obtain ⟨vector, realized⟩ := induced.2.2.2.2.2 groupElement
  have rational_value := congrFun realized (GeneralLinearGroup.map rationalAdele rationalMatrix)
  have identity_value := congrFun realized (1 : BinaryAdelicGL)
  have rational_invariance := inducingData.cusp.leftRational rationalMatrix vector 1
  rw [mul_one] at rational_invariance
  rw [rational_invariance, GeneralLinearGroup.map_det, normPower_rational,
    one_mul] at rational_value
  have levi_one : planeLevi (1 : BinaryAdelicGL) 1 = 1 := (planeLeviHom Adeles).map_one
  rw [map_one, normPower_one, one_mul, levi_one, one_mul] at identity_value
  exact rational_value.symm.trans identity_value

theorem induced_rankOne_rational
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (rationalScalar : ℚˣ) (groupElement : AdelicGL) :
    sectionValue (planeLevi 1 (Units.map rationalAdele rationalScalar) * groupElement) =
      sectionValue groupElement := by
  rw [induced.2.2.2.2.1, inducingData.chi.rational, normPower_rational, one_mul, one_mul]

theorem induced_levi_rational
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (rationalMatrix : BinaryRationalGL) (rationalScalar : ℚˣ)
    (groupElement : AdelicGL) :
    sectionValue (rationalGroup (planeLevi rationalMatrix rationalScalar) * groupElement) =
      sectionValue groupElement := by
  have levi_split : planeLevi rationalMatrix rationalScalar =
      planeLevi rationalMatrix 1 * planeLevi 1 rationalScalar := by
    change (planeLeviHom ℚ) (rationalMatrix, rationalScalar) =
      (planeLeviHom ℚ) (rationalMatrix, 1) * (planeLeviHom ℚ) (1, rationalScalar)
    rw [← map_mul]
    simp only [Prod.mk_mul_mk, mul_one, one_mul]
  rw [levi_split, map_mul, mul_assoc]
  change sectionValue (GeneralLinearGroup.map rationalAdele (planeLevi rationalMatrix 1) *
    (GeneralLinearGroup.map rationalAdele (planeLevi 1 rationalScalar) * groupElement)) = _
  rw [map_planeLevi, map_planeLevi, map_one, map_one,
    induced_binary_rational induced, induced_rankOne_rational induced]

theorem induced_parabolic_rational
    {degree : ℕ} {inducingData : InducingData degree}
    {parameter : ℂ} {sectionValue : AdelicGL → ℂ}
    (induced : IsInduced inducingData .plane parameter sectionValue)
    (rationalMatrix : RationalGL3) (parabolic : rationalMatrix ∈ GeneralEisenstein.parabolic .plane)
    (groupElement : AdelicGL) :
    sectionValue (rationalGroup rationalMatrix * groupElement) = sectionValue groupElement := by
  obtain ⟨first, second, binary, scalar, factorization⟩ :=
    planeParabolic_factorization rationalMatrix parabolic
  rw [factorization, map_mul, mul_assoc]
  change sectionValue (GeneralLinearGroup.map rationalAdele (planeUnipotent first second) *
    (rationalGroup (planeLevi binary scalar) * groupElement)) = _
  rw [map_planeUnipotent, induced.2.2.2.1, induced_levi_rational induced]

theorem eisensteinSummand_of_representative
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (rationalMatrix : RationalGL3) (groupElement : AdelicGL) :
    eisensteinSummand family parameter groupElement (QuotientGroup.mk rationalMatrix) =
      family parameter (rationalGroup rationalMatrix⁻¹ * groupElement) := by
  obtain ⟨parabolicElement, representative⟩ :=
    QuotientGroup.mk_out_eq_mul (GeneralEisenstein.parabolic .plane) rationalMatrix
  unfold eisensteinSummand
  rw [representative, _root_.mul_inv_rev, map_mul, mul_assoc]
  exact induced_parabolic_rational induced parabolicElement.val⁻¹
    ((GeneralEisenstein.parabolic .plane).inv_mem parabolicElement.property)
    (rationalGroup rationalMatrix⁻¹ * groupElement)

theorem eisensteinSummand_rational_translate
    {degree : ℕ} {inducingData : InducingData degree}
    {family : ℂ → AdelicGL → ℂ} {parameter : ℂ}
    (induced : IsInduced inducingData .plane parameter (family parameter))
    (rationalMatrix : RationalGL3) (groupElement : AdelicGL) (flag : Flags .plane) :
    eisensteinSummand family parameter (rationalGroup rationalMatrix * groupElement) flag =
      eisensteinSummand family parameter groupElement (rationalMatrix⁻¹ • flag) := by
  have translated_flag : rationalMatrix⁻¹ • flag =
      QuotientGroup.mk (rationalMatrix⁻¹ * flag.out) := by
    conv_lhs => rw [← QuotientGroup.out_eq' flag]
    rfl
  rw [translated_flag, eisensteinSummand_of_representative induced]
  simp only [eisensteinSummand, _root_.mul_inv_rev, inv_inv, map_mul, mul_assoc]

theorem continuation_rational_translate
    {degree : ℕ} {inducingData : InducingData degree}
    {family continuation : ℂ → AdelicGL → ℂ}
    (induced : ∀ parameter, IsInduced inducingData .plane parameter (family parameter))
    (continuation_spec : IsEisensteinContinuation family continuation)
    (rationalMatrix : RationalGL3) :
    IsEisensteinContinuation family
      (fun parameter groupElement => continuation parameter (rationalGroup rationalMatrix * groupElement)) := by
  refine ⟨fun groupElement parameter => continuation_spec.1 _ parameter, ?_⟩
  obtain ⟨threshold, convergence⟩ := continuation_spec.2
  refine ⟨threshold, ?_⟩
  intro parameter parameter_large groupElement
  have translated_sum := convergence parameter parameter_large
    (rationalGroup rationalMatrix * groupElement)
  have sum_equal : eisensteinSummand family parameter (rationalGroup rationalMatrix * groupElement) =
      eisensteinSummand family parameter groupElement ∘
        MulAction.toPerm (β := Flags .plane) rationalMatrix⁻¹ := by
    funext flag
    exact eisensteinSummand_rational_translate (induced parameter) rationalMatrix groupElement flag
  rw [sum_equal] at translated_sum
  exact (Equiv.hasSum_iff _).mp translated_sum

theorem continuation_rational_germ
    {degree : ℕ} {inducingData : InducingData degree}
    {family continuation : ℂ → AdelicGL → ℂ}
    (flat_family : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (rationalMatrix : RationalGL3) (groupElement : AdelicGL) (parameter : ℂ) :
    (fun nearbyParameter => continuation nearbyParameter (rationalGroup rationalMatrix * groupElement))
      =ᶠ[nhdsWithin parameter {parameter}ᶜ]
        (fun nearbyParameter => continuation nearbyParameter groupElement) := by
  exact continuation_germs_agree
    (continuation_rational_translate flat_family.1 continuation_spec rationalMatrix)
    continuation_spec groupElement parameter

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
