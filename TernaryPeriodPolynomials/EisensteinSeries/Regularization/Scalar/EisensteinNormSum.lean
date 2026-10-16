module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.EisensteinQuotient
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ
local notation "PrincipalQuotient" => Quotient (MulAction.orbitRel principalRealSpecialLinear RealSL3)

instance planeFlags_countable : Countable (Flags .plane) := planeFlagIntegerRow_injective.countable

noncomputable def normalizedScalarEisensteinNormSum (degree : ℕ) (family : ℂ → AdelicGL → ℂ)
    (parameter : ℂ) (matrix : AdelicGL) : ℝ :=
  ∑' flag, ‖eisensteinSummand (unitaryNormalize degree family) parameter matrix flag‖

theorem normalizedScalarEisensteinNormSum_nonnegative (degree : ℕ) (family : ℂ → AdelicGL → ℂ)
    (parameter : ℂ) (matrix : AdelicGL) : 0 ≤ normalizedScalarEisensteinNormSum degree family parameter matrix :=
  tsum_nonneg (fun _ => norm_nonneg _)

theorem normalized_eisensteinSummand_rational_translate
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (rational : RationalGL3)
    (matrix : AdelicGL) (flag : Flags .plane) :
    eisensteinSummand (unitaryNormalize degree family) parameter (rationalGroup rational * matrix) flag =
      eisensteinSummand (unitaryNormalize degree family) parameter matrix (rational⁻¹ • flag) := by
  rw [unitaryNormalize_eisensteinSummand, unitaryNormalize_eisensteinSummand,
    eisensteinSummand_rational_translate (flat.1 _)]
  simp only [map_mul, normPower_mul, rationalGroup, GeneralLinearGroup.map_det, normPower_rational, one_mul]

theorem normalizedScalarEisensteinNormSum_rational
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (rational : RationalGL3) (matrix : AdelicGL) :
    normalizedScalarEisensteinNormSum degree family parameter (rationalGroup rational * matrix) =
      normalizedScalarEisensteinNormSum degree family parameter matrix := by
  unfold normalizedScalarEisensteinNormSum
  simp_rw [normalized_eisensteinSummand_rational_translate flat]
  exact (MulAction.toPerm (β := Flags .plane) rational⁻¹).tsum_eq
    (fun flag => ‖eisensteinSummand (unitaryNormalize degree family) parameter matrix flag‖)

theorem normalizedScalarEisensteinNormSum_finite_level
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (level : finiteLevel) (matrix : AdelicGL) :
    normalizedScalarEisensteinNormSum degree family parameter (matrix * atFinite level.val) =
      normalizedScalarEisensteinNormSum degree family parameter matrix := by
  apply tsum_congr
  intro flag
  change ‖unitaryNormalize degree family parameter (rationalGroup flag.out⁻¹ * (matrix * atFinite level.val))‖ = _
  rw [← mul_assoc, unitaryNormalize_finite_level flat.1 parameter level]
  rfl

theorem normalizedScalarEisensteinNormSum_principal_slice
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ)
    (integral : GL3 IntegralAdeles) (principal : principalRealSpecialLinear) (matrix : RealSL3) :
    normalizedScalarEisensteinNormSum degree family parameter (realSpecialIntegralSlice integral (principal.val * matrix)) =
      normalizedScalarEisensteinNormSum degree family parameter (realSpecialIntegralSlice integral matrix) := by
  obtain ⟨integer, integer_principal, represents⟩ := principal.property
  have identity : realSpecialIntegralSlice integral (principal.val * matrix) =
      atInfinity (SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) integer)) *
        realSpecialIntegralSlice integral matrix := by
    rw [← represents]
    simp only [realSpecialIntegralSlice, map_mul, atInfinity_mul, mul_assoc]
  rw [identity]
  apply Complex.ofReal_injective
  apply adelic_function_principal_integer_translation
    (fun matrix => (normalizedScalarEisensteinNormSum degree family parameter matrix : ℂ))
    (fun rational matrix => congrArg Complex.ofReal (normalizedScalarEisensteinNormSum_rational flat parameter rational matrix))
    (fun level matrix => congrArg Complex.ofReal (normalizedScalarEisensteinNormSum_finite_level flat parameter level matrix))
    ⟨integer, integer_principal⟩ _ integral
  simp only [realSpecialIntegralSlice, map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul]

noncomputable def normalizedScalarEisensteinNormPrincipalQuotient
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (integral : GL3 IntegralAdeles) : PrincipalQuotient → ℝ :=
  Quotient.lift (fun matrix => normalizedScalarEisensteinNormSum degree family parameter (realSpecialIntegralSlice integral matrix))
    (by
      intro first second relation
      obtain ⟨principal, equality⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp relation)
      change principal.val * second = first at equality
      rw [← equality]
      exact normalizedScalarEisensteinNormSum_principal_slice flat parameter integral principal second)

theorem normalizedScalarEisensteinNormPrincipalQuotient_nonnegative
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (integral : GL3 IntegralAdeles) (point : PrincipalQuotient) :
    0 ≤ normalizedScalarEisensteinNormPrincipalQuotient flat parameter integral point := by
  induction point using Quotient.inductionOn with
  | h matrix => exact normalizedScalarEisensteinNormSum_nonnegative degree family parameter _

theorem normalized_eisensteinSummand_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (flag : Flags .plane) :
    Continuous (fun matrix => eisensteinSummand (unitaryNormalize degree family) parameter matrix flag) := by
  change Continuous (fun matrix : AdelicGL => unitaryNormalize degree family parameter (rationalGroup flag.out⁻¹ * matrix))
  have input_continuous : Continuous (fun matrix : AdelicGL => (parameter, rationalGroup flag.out⁻¹ * matrix)) :=
    continuous_const.prodMk ((continuous_const (y := rationalGroup flag.out⁻¹)).mul continuous_id)
  have composed := (unitaryNormalize_joint_continuous flat).comp input_continuous
  dsimp only [Function.comp_def] at composed
  exact composed

theorem normalizedScalarEisensteinNormPrincipalQuotient_measurable
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (integral : GL3 IntegralAdeles) :
    Measurable (normalizedScalarEisensteinNormPrincipalQuotient flat parameter integral) := by
  apply measurable_from_quotient.mpr
  apply Measurable.tsum
  intro flag
  exact ((normalized_eisensteinSummand_continuous flat parameter flag).comp
    (realSpecialIntegralSlice_continuous integral)).norm.measurable

theorem normalizedScalarEisensteinNormSum_integer_inverse_slice
    {degree : ℕ} {inducingData : InducingData degree} {family : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (parameter : ℂ) (integer : SpecialLinearGroup (Fin 3) ℤ)
    (integral : GL3 IntegralAdeles) (matrix : RealSL3) :
    normalizedScalarEisensteinNormSum degree family parameter
      (realSpecialIntegralSlice integral ((SpecialLinearGroup.map (Int.castRingHom ℝ) integer)⁻¹ * matrix)) =
      normalizedScalarEisensteinNormSum degree family parameter
        (realSpecialIntegralSlice (GeneralLinearGroup.map (Int.castRingHom IntegralAdeles)
          (SpecialLinearGroup.toGL integer) * integral) matrix) := by
  rw [← integer_inverse_slice_identity, normalizedScalarEisensteinNormSum_rational flat]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
