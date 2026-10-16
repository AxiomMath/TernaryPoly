module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.FiniteCompatibility
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.QuotientMeasure
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Boundary.ResidueMeasurable
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.DomainLp

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory
open scoped ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ
local notation "PrincipalQuotient" => Quotient (MulAction.orbitRel principalRealSpecialLinear RealSL3)

noncomputable def realSpecialIntegralSlice (integral : GL3 IntegralAdeles) (matrix : RealSL3) : AdelicGL :=
  atInfinity (SpecialLinearGroup.toGL matrix) * atFinite (GeneralLinearGroup.map integralEmbedding integral)

theorem realSpecialIntegralSlice_continuous (integral : GL3 IntegralAdeles) :
    Continuous (realSpecialIntegralSlice integral) := by
  have infinity_continuous : Continuous (atInfinity : RealGL3 → AdelicGL) :=
    combineGL_continuous.comp (continuous_id.prodMk continuous_const)
  exact (infinity_continuous.comp SpecialLinearGroup.continuous_toGL).mul continuous_const

theorem normalizedBoundaryResidue_principal_slice_invariant
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (principal : principalRealSpecialLinear) (matrix : RealSL3) :
    normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral (principal.val * matrix)) =
      normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral matrix) := by
  obtain ⟨integer, integer_principal, represents⟩ := principal.property
  have identity : realSpecialIntegralSlice integral (principal.val * matrix) =
      atInfinity (SpecialLinearGroup.toGL (SpecialLinearGroup.map (Int.castRingHom ℝ) integer)) *
        realSpecialIntegralSlice integral matrix := by
    rw [← represents]
    simp only [realSpecialIntegralSlice, map_mul, atInfinity_mul, mul_assoc]
  rw [identity]
  apply normalizedBoundaryResidue_principal_integer_translation flat continuation_spec
    ⟨integer, integer_principal⟩ _ integral
  simp only [realSpecialIntegralSlice, map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul]

noncomputable def normalizedBoundaryResiduePrincipalQuotient
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) : PrincipalQuotient → ℂ :=
  Quotient.lift (fun matrix => normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral matrix))
    (by
      intro first second relation
      obtain ⟨principal, equality⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp relation)
      change principal.val * second = first at equality
      rw [← equality]
      exact normalizedBoundaryResidue_principal_slice_invariant flat continuation_spec integral principal second)

theorem normalizedBoundaryResiduePrincipalQuotient_mk
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (matrix : RealSL3) :
    normalizedBoundaryResiduePrincipalQuotient flat continuation_spec integral (Quotient.mk'' matrix) =
      normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral matrix) := rfl

theorem normalizedBoundaryResiduePrincipalQuotient_measurable
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (integral : GL3 IntegralAdeles) :
    Measurable (normalizedBoundaryResiduePrincipalQuotient flat continuation_spec integral) := by
  apply measurable_from_quotient.mpr
  exact normalizedBoundaryResidue_measurable flat continuation_spec (realSpecialIntegralSlice_continuous integral)

theorem normalizedBoundaryResiduePrincipalQuotient_memLp
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (integral : GL3 IntegralAdeles)
    (exponent : ℝ≥0∞) :
    MemLp (normalizedBoundaryResiduePrincipalQuotient flat continuation_spec integral)
      exponent principalSpecialLinearQuotientMeasure := by
  obtain ⟨bound, _, bounded⟩ := normalizedBoundaryResidue_global_bound flat continuation_spec
  apply MemLp.of_bound (normalizedBoundaryResiduePrincipalQuotient_measurable flat continuation_spec integral).aestronglyMeasurable bound
  apply Filter.Eventually.of_forall
  intro point
  induction point using Quotient.inductionOn with
  | h matrix => exact bounded (realSpecialIntegralSlice integral matrix)

noncomputable def normalizedBoundaryResiduePrincipalL2
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation) (integral : GL3 IntegralAdeles) :
    Lp ℂ 2 principalSpecialLinearQuotientMeasure :=
  (normalizedBoundaryResiduePrincipalQuotient_memLp flat continuation_spec integral 2).toLp
    (normalizedBoundaryResiduePrincipalQuotient flat continuation_spec integral)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
