module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.PrincipalQuotient
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ
local notation "PrincipalQuotient" => Quotient (MulAction.orbitRel principalRealSpecialLinear RealSL3)

theorem principalSpecialLinearQuotient_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : PrincipalQuotient → E) (measurable : AEStronglyMeasurable function principalSpecialLinearQuotientMeasure) :
    (∫ point, function point ∂principalSpecialLinearQuotientMeasure) =
      ∫ point in principalRealSpecialLinearDomain, function (Quotient.mk'' point) ∂realSpecialLinearHaar :=
  integral_map measurable_quotient_mk''.aemeasurable measurable

theorem normalizedBoundaryResiduePrincipalL2_coe
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (integral : GL3 IntegralAdeles) :
    (normalizedBoundaryResiduePrincipalL2 flat continuation_spec integral : PrincipalQuotient → ℂ) =ᵐ[
      principalSpecialLinearQuotientMeasure] normalizedBoundaryResiduePrincipalQuotient flat continuation_spec integral :=
  (normalizedBoundaryResiduePrincipalQuotient_memLp flat continuation_spec integral 2).coeFn_toLp

theorem normalizedBoundaryResiduePrincipalL2_inner
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (first second : GL3 IntegralAdeles) :
    inner ℂ (normalizedBoundaryResiduePrincipalL2 flat continuation_spec first)
      (normalizedBoundaryResiduePrincipalL2 flat continuation_spec second) =
      ∫ point in principalRealSpecialLinearDomain,
        inner ℂ (normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice first point))
          (normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice second point)) ∂realSpecialLinearHaar := by
  rw [L2.inner_def]
  have equality : (∫ point, inner ℂ
      ((normalizedBoundaryResiduePrincipalL2 flat continuation_spec first : PrincipalQuotient → ℂ) point)
      ((normalizedBoundaryResiduePrincipalL2 flat continuation_spec second : PrincipalQuotient → ℂ) point)
      ∂principalSpecialLinearQuotientMeasure) =
      ∫ point, inner ℂ (normalizedBoundaryResiduePrincipalQuotient flat continuation_spec first point)
        (normalizedBoundaryResiduePrincipalQuotient flat continuation_spec second point) ∂principalSpecialLinearQuotientMeasure := by
    apply integral_congr_ae
    filter_upwards [normalizedBoundaryResiduePrincipalL2_coe flat continuation_spec first,
      normalizedBoundaryResiduePrincipalL2_coe flat continuation_spec second] with point first_eq second_eq
    rw [first_eq, second_eq]
  rw [equality]
  exact principalSpecialLinearQuotient_integral _
    ((normalizedBoundaryResiduePrincipalQuotient_measurable flat continuation_spec first).inner
      (normalizedBoundaryResiduePrincipalQuotient_measurable flat continuation_spec second)).aestronglyMeasurable

theorem normalizedBoundaryResiduePrincipalL2_zero_of_self_pairing
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (integral : GL3 IntegralAdeles)
    (zero : (∫ point in principalRealSpecialLinearDomain,
      inner ℂ (normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral point))
        (normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral point)) ∂realSpecialLinearHaar) = 0) :
    normalizedBoundaryResiduePrincipalL2 flat continuation_spec integral = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rwa [normalizedBoundaryResiduePrincipalL2_inner]

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
