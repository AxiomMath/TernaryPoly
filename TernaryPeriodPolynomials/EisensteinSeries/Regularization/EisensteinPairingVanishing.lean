module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.FlagStabilizerPairing
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.OrbitPairingUnfolding
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.PairingFlagExpansion

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open scoped ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

theorem normalized_flag_pairing_sum_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (parameter : ℂ) (integral : GL3 IntegralAdeles) {kernel : RealSL3 → ℂ}
    (kernel_measurable : Measurable kernel) (kernel_integrable : Integrable kernel realSpecialLinearHaar)
    (finite : (∑' flag, ∫⁻ matrix in principalRealSpecialLinearDomain,
      ‖eisensteinSummand (unitaryNormalize degree family) parameter (realSpecialIntegralSlice integral matrix) flag *
        star (normalizedBoundaryResidueAverage degree continuation integral kernel matrix)‖ₑ ∂realSpecialLinearHaar) < ⊤) :
    (∑' flag, ∫ matrix in principalRealSpecialLinearDomain,
      eisensteinSummand (unitaryNormalize degree family) parameter (realSpecialIntegralSlice integral matrix) flag *
        star (normalizedBoundaryResidueAverage degree continuation integral kernel matrix) ∂realSpecialLinearHaar) = 0 := by
  refine flag_orbit_pairing_unfolding_zero (G := principalRealSpecialLinear)
    (family := fun flag matrix =>
      eisensteinSummand (unitaryNormalize degree family) parameter (realSpecialIntegralSlice integral matrix) flag *
        star (normalizedBoundaryResidueAverage degree continuation integral kernel matrix))
    principalRealSpecialLinearDomain_measurable principalRealSpecialLinearDomain_fundamental
    principalFlagDomain principalFlagDomain_isFundamental ?_ ?_ finite ?_
  · intro flag
    exact (((normalized_eisensteinSummand_continuous flat parameter flag).comp
      (realSpecialIntegralSlice_continuous integral)).measurable).mul
        (continuous_star.measurable.comp
          (normalizedBoundaryResidueAverage_measurable flat continuation_spec integral kernel_measurable))
  · intro element flag matrix
    change eisensteinSummand (unitaryNormalize degree family) parameter
      (realSpecialIntegralSlice integral (element.val * matrix)) flag *
        star (normalizedBoundaryResidueAverage degree continuation integral kernel (element.val * matrix)) = _
    rw [normalized_eisensteinSummand_principal_slice_translate flat,
      normalizedBoundaryResidueAverage_principal_invariant flat continuation_spec]
  · exact normalized_flag_stabilizer_pairing_zero flat continuation_spec parameter integral kernel_measurable kernel_integrable

theorem normalized_scalar_tent_pairing_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (radius : ℝ) :
    ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∫ point, normalizedScalarEisensteinPrincipalQuotient flat ((3 : ℂ) / 2 + (displacement : ℂ)) integral point *
        star (normalizedBoundaryResidueAveragePrincipalQuotient flat continuation_spec integral (realSpecialTent radius) point)
          ∂principalSpecialLinearQuotientMeasure) = 0 := by
  filter_upwards [normalized_scalar_tent_pairing_flag_expansion flat continuation_spec integral radius]
    with displacement expansion
  rw [expansion.2]
  exact normalized_flag_pairing_sum_zero flat continuation_spec _ integral
    (realSpecialTent_continuous radius).measurable (realSpecialTent_integrable radius) expansion.1

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
