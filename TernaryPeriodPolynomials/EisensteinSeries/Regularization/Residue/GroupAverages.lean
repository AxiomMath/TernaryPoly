module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.BoundedGroupAverages
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.PlaneConstantTerm
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.PrincipalQuotient
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearUnipotent

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ
local notation "PrincipalQuotient" => Quotient (MulAction.orbitRel principalRealSpecialLinear RealSL3)

def realSpecialPlane (first second : ℝ) : RealSL3 := realSpecialUnipotent 0 second first

theorem realSpecialPlane_toGL (first second : ℝ) :
    SpecialLinearGroup.toGL (realSpecialPlane first second) = planeUnipotent first second := Units.ext rfl

theorem realSpecialPlane_continuous : Continuous (fun point : ℝ × ℝ => realSpecialPlane point.1 point.2) :=
  realSpecialUnipotent_continuous.comp (continuous_const.prodMk (continuous_snd.prodMk continuous_fst))

theorem realSpecialIntegralSlice_left_mul (integral : GL3 IntegralAdeles) (first second : RealSL3) :
    realSpecialIntegralSlice integral (first * second) =
      atInfinity (SpecialLinearGroup.toGL first) * realSpecialIntegralSlice integral second := by
  simp only [realSpecialIntegralSlice, map_mul, atInfinity_mul, mul_assoc]

theorem normalizedBoundaryResidue_realSpecialPlane_average_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (matrix : RealSL3) :
    (∫ point : ℝ × ℝ, normalizedBoundaryResidue degree continuation
      (realSpecialIntegralSlice integral (realSpecialPlane (3 * point.1) (3 * point.2) * matrix))
      ∂realPlaneUnitMeasure) = 0 := by
  simp only [realSpecialIntegralSlice_left_mul, realSpecialPlane_toGL]
  apply normalizedBoundaryResidue_real_plane_constant_term_zero flat continuation_spec integral
  simp only [realSpecialIntegralSlice, map_mul, finiteGroup_atInfinity, finiteGroup_atFinite, one_mul]

noncomputable def normalizedBoundaryResidueAverage (degree : ℕ) (continuation : ℂ → AdelicGL → ℂ)
    (integral : GL3 IntegralAdeles) (kernel : RealSL3 → ℂ) : RealSL3 → ℂ :=
  rightGroupAverage realSpecialLinearHaar
    (fun matrix => normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral matrix)) kernel

theorem normalizedBoundaryResidueAverage_measurable
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) {kernel : RealSL3 → ℂ} (kernel_measurable : Measurable kernel) :
    Measurable (normalizedBoundaryResidueAverage degree continuation integral kernel) :=
  rightGroupAverage_measurable realSpecialLinearHaar
    (normalizedBoundaryResidue_measurable flat continuation_spec (realSpecialIntegralSlice_continuous integral)) kernel_measurable

theorem normalizedBoundaryResidueAverage_bounded
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    {kernel : RealSL3 → ℂ} (kernel_integrable : Integrable kernel realSpecialLinearHaar) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ integral : GL3 IntegralAdeles, ∀ matrix : RealSL3,
      ‖normalizedBoundaryResidueAverage degree continuation integral kernel matrix‖ ≤ bound := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedBoundaryResidue_global_bound flat continuation_spec
  refine ⟨bound * ∫ shift, ‖kernel shift‖ ∂realSpecialLinearHaar,
    mul_nonneg nonnegative (integral_nonneg (fun _ => norm_nonneg _)), ?_⟩
  intro integral matrix
  exact rightGroupAverage_bound realSpecialLinearHaar _ kernel_integrable
    (fun point => bounded (realSpecialIntegralSlice integral point)) matrix

theorem normalizedBoundaryResidueAverage_principal_invariant
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (kernel : RealSL3 → ℂ)
    (principal : principalRealSpecialLinear) (matrix : RealSL3) :
    normalizedBoundaryResidueAverage degree continuation integral kernel (principal.val * matrix) =
      normalizedBoundaryResidueAverage degree continuation integral kernel matrix :=
  rightGroupAverage_left_invariant realSpecialLinearHaar _ kernel principal.val
    (normalizedBoundaryResidue_principal_slice_invariant flat continuation_spec integral principal) matrix

theorem normalizedBoundaryResidueAverage_plane_average_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) {kernel : RealSL3 → ℂ}
    (kernel_integrable : Integrable kernel realSpecialLinearHaar) (matrix : RealSL3) :
    (∫ point : ℝ × ℝ, normalizedBoundaryResidueAverage degree continuation integral kernel
      (realSpecialPlane (3 * point.1) (3 * point.2) * matrix) ∂realPlaneUnitMeasure) = 0 := by
  obtain ⟨bound, _, bounded⟩ := normalizedBoundaryResidue_global_bound flat continuation_spec
  apply rightGroupAverage_preserves_zero_average realSpecialLinearHaar realPlaneUnitMeasure
    (normalizedBoundaryResidue_measurable flat continuation_spec (realSpecialIntegralSlice_continuous integral))
    kernel_integrable (bound := bound) (fun point => bounded (realSpecialIntegralSlice integral point))
  · exact (realSpecialPlane_continuous.comp
      ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))).measurable
  · exact normalizedBoundaryResidue_realSpecialPlane_average_zero flat continuation_spec integral

noncomputable def normalizedBoundaryResidueAveragePrincipalQuotient
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (kernel : RealSL3 → ℂ) : PrincipalQuotient → ℂ :=
  Quotient.lift (normalizedBoundaryResidueAverage degree continuation integral kernel) (by
    intro first second relation
    obtain ⟨principal, equality⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp relation)
    change principal.val * second = first at equality
    rw [← equality]
    exact normalizedBoundaryResidueAverage_principal_invariant flat continuation_spec integral kernel principal second)

theorem normalizedBoundaryResidueAveragePrincipalQuotient_measurable
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family)
    (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) {kernel : RealSL3 → ℂ} (kernel_measurable : Measurable kernel) :
    Measurable (normalizedBoundaryResidueAveragePrincipalQuotient flat continuation_spec integral kernel) := by
  apply measurable_from_quotient.mpr
  exact normalizedBoundaryResidueAverage_measurable flat continuation_spec integral kernel_measurable

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
