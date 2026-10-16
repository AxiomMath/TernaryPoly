module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Principal.CorrelationContinuity
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.ContinuousApproximation
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.GroupCorrelationPairing
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Special.LinearTentDetection
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.TentOrthogonality
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.PrincipalPairing

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ
local notation "domainMeasure" => realSpecialLinearHaar.restrict principalRealSpecialLinearDomain

noncomputable def normalizedBoundaryResidueCorrelation (degree : ℕ)
    (continuation : ℂ → AdelicGL → ℂ) (integral : GL3 IntegralAdeles) (shift : RealSL3) : ℂ :=
  ∫ matrix, normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral matrix) *
    star (normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral (matrix * shift))) ∂domainMeasure

theorem normalizedBoundaryResidueCorrelation_continuous
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) : Continuous (normalizedBoundaryResidueCorrelation degree continuation integral) := by
  obtain ⟨bound, nonnegative, bounded, approximation, continuous, approximation_bounded, invariant, converges⟩ :=
    normalizedBoundaryResidue_continuous_approximation flat continuation_spec integral
  exact principal_correlation_continuous_of_approximation
    (normalizedBoundaryResidue_measurable flat continuation_spec (realSpecialIntegralSlice_continuous integral))
    (normalizedBoundaryResidue_principal_slice_invariant flat continuation_spec integral)
    nonnegative bounded continuous approximation_bounded invariant converges

theorem normalizedBoundaryResidueCorrelation_tent_integral_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (radius : ℝ) :
    (∫ shift, normalizedBoundaryResidueCorrelation degree continuation integral shift * realSpecialTent radius shift
      ∂realSpecialLinearHaar) = 0 := by
  obtain ⟨bound, nonnegative, bounded⟩ := normalizedBoundaryResidue_global_bound flat continuation_spec
  have pairing := rightGroupAverage_correlation_pairing realSpecialLinearHaar domainMeasure
    (normalizedBoundaryResidue_measurable flat continuation_spec (realSpecialIntegralSlice_continuous integral))
    (realSpecialTent_integrable radius) nonnegative (fun matrix => bounded (realSpecialIntegralSlice integral matrix))
  have quotient_pairing := normalizedBoundaryResidue_tent_pairing_zero flat continuation_spec integral radius
  rw [principalSpecialLinearQuotient_integral
    (fun point => normalizedBoundaryResiduePrincipalQuotient flat continuation_spec integral point *
      star (normalizedBoundaryResidueAveragePrincipalQuotient flat continuation_spec integral (realSpecialTent radius) point))
    ((normalizedBoundaryResiduePrincipalQuotient_measurable flat continuation_spec integral).aestronglyMeasurable.mul
      (normalizedBoundaryResidueAveragePrincipalQuotient_measurable flat continuation_spec integral
        (realSpecialTent_continuous radius).measurable).aestronglyMeasurable.star)] at quotient_pairing
  have tent_real (shift : RealSL3) : star (realSpecialTent radius shift) = realSpecialTent radius shift := by
    simp [realSpecialTent]
  simpa only [tent_real, normalizedBoundaryResidueCorrelation] using pairing.symm.trans quotient_pairing

theorem normalizedBoundaryResidueCorrelation_one
    (degree : ℕ) (continuation : ℂ → AdelicGL → ℂ) (integral : GL3 IntegralAdeles) :
    normalizedBoundaryResidueCorrelation degree continuation integral 1 =
      ((∫ matrix, ‖normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral matrix)‖ ^ 2 ∂domainMeasure : ℝ) : ℂ) := by
  simp only [normalizedBoundaryResidueCorrelation, mul_one]
  change (∫ matrix, normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral matrix) *
    (starRingEnd ℂ) (normalizedBoundaryResidue degree continuation (realSpecialIntegralSlice integral matrix)) ∂domainMeasure) = _
  simp only [Complex.mul_conj', ← Complex.ofReal_pow]
  exact integral_ofReal

theorem normalizedBoundaryResidueCorrelation_one_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) : normalizedBoundaryResidueCorrelation degree continuation integral 1 = 0 := by
  have continuous := normalizedBoundaryResidueCorrelation_continuous flat continuation_spec integral
  have real_zero : (normalizedBoundaryResidueCorrelation degree continuation integral 1).re = 0 := by
    apply realSpecialTent_detects_nonnegative_at_one (Complex.continuous_re.comp continuous)
    · dsimp only [Function.comp_def]
      rw [normalizedBoundaryResidueCorrelation_one, Complex.ofReal_re]
      exact integral_nonneg (fun matrix => sq_nonneg _)
    · intro radius
      have integrable := (continuous.mul (realSpecialTent_continuous radius)).integrable_of_hasCompactSupport
        (μ := realSpecialLinearHaar) ((realSpecialTent_compactSupport radius).mul_left)
      have real_integral := integral_re integrable
      change (∫ shift, (normalizedBoundaryResidueCorrelation degree continuation integral shift *
        realSpecialTent radius shift).re ∂realSpecialLinearHaar) =
          (∫ shift, normalizedBoundaryResidueCorrelation degree continuation integral shift *
            realSpecialTent radius shift ∂realSpecialLinearHaar).re at real_integral
      have real_product (shift : RealSL3) :
          (normalizedBoundaryResidueCorrelation degree continuation integral shift * realSpecialTent radius shift).re =
            (realSpecialTent radius shift).re * (normalizedBoundaryResidueCorrelation degree continuation integral shift).re := by
        simp [realSpecialTent, Complex.mul_re, mul_comm]
      simpa only [Function.comp_def, real_product,
        normalizedBoundaryResidueCorrelation_tent_integral_zero flat continuation_spec, Complex.zero_re] using real_integral
  rw [normalizedBoundaryResidueCorrelation_one, Complex.ofReal_re] at real_zero
  rw [normalizedBoundaryResidueCorrelation_one, real_zero, Complex.ofReal_zero]

theorem normalizedBoundaryResiduePrincipalL2_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) : normalizedBoundaryResiduePrincipalL2 flat continuation_spec integral = 0 := by
  apply normalizedBoundaryResiduePrincipalL2_zero_of_self_pairing flat continuation_spec integral
  simpa only [normalizedBoundaryResidueCorrelation, mul_one, RCLike.inner_apply, starRingEnd_apply] using
    normalizedBoundaryResidueCorrelation_one_zero flat continuation_spec integral

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
