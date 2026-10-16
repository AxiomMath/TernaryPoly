module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Scalar.AbsolutePairing
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.AbsoluteSeriesPairing
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.PrincipalPairing

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open scoped ENNReal

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

local notation "RealSL3" => SpecialLinearGroup (Fin 3) ℝ

theorem normalized_scalar_tent_pairing_flag_expansion
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (radius : ℝ) :
    ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∑' flag, ∫⁻ matrix in principalRealSpecialLinearDomain,
        ‖eisensteinSummand (unitaryNormalize degree family) ((3 : ℂ) / 2 + (displacement : ℂ))
          (realSpecialIntegralSlice integral matrix) flag *
          star (normalizedBoundaryResidueAverage degree continuation integral (realSpecialTent radius) matrix)‖ₑ
          ∂realSpecialLinearHaar) < ⊤ ∧
      (∫ point, normalizedScalarEisensteinPrincipalQuotient flat ((3 : ℂ) / 2 + (displacement : ℂ)) integral point *
        star (normalizedBoundaryResidueAveragePrincipalQuotient flat continuation_spec integral (realSpecialTent radius) point)
          ∂principalSpecialLinearQuotientMeasure) =
        ∑' flag, ∫ matrix in principalRealSpecialLinearDomain,
          eisensteinSummand (unitaryNormalize degree family) ((3 : ℂ) / 2 + (displacement : ℂ))
            (realSpecialIntegralSlice integral matrix) flag *
            star (normalizedBoundaryResidueAverage degree continuation integral (realSpecialTent radius) matrix)
              ∂realSpecialLinearHaar := by
  filter_upwards [normalizedScalarEisensteinNormPrincipalQuotient_tent_integrable flat continuation_spec integral radius,
    self_mem_nhdsWithin] with displacement norm_integrable positive
  have large : 3 / 2 < ((3 : ℂ) / 2 + (displacement : ℂ)).re := by norm_num; exact positive
  have test_measurable := continuous_star.measurable.comp
    (normalizedBoundaryResidueAverage_measurable flat continuation_spec integral (realSpecialTent_continuous radius).measurable)
  have quotient_test_measurable := continuous_star.measurable.comp
    (normalizedBoundaryResidueAveragePrincipalQuotient_measurable flat continuation_spec integral
      (realSpecialTent_continuous radius).measurable)
  have domain_norm_integrable : Integrable (fun matrix : RealSL3 =>
      (∑' flag, ‖eisensteinSummand (unitaryNormalize degree family) ((3 : ℂ) / 2 + (displacement : ℂ))
        (realSpecialIntegralSlice integral matrix) flag‖) *
        ‖star (normalizedBoundaryResidueAverage degree continuation integral (realSpecialTent radius) matrix)‖)
      (realSpecialLinearHaar.restrict principalRealSpecialLinearDomain) := by
    have pulled := (integrable_map_measure norm_integrable.aestronglyMeasurable
      measurable_quotient_mk''.aemeasurable).mp norm_integrable
    simpa only [Function.comp_def, normalizedScalarEisensteinNormPrincipalQuotient,
      normalizedScalarEisensteinNormSum, normalizedBoundaryResidueAveragePrincipalQuotient,
      Quotient.lift_mk, norm_star] using pulled
  have expansion := absolute_series_pairing (realSpecialLinearHaar.restrict principalRealSpecialLinearDomain)
    (family := fun flag matrix => eisensteinSummand (unitaryNormalize degree family)
      ((3 : ℂ) / 2 + (displacement : ℂ)) (realSpecialIntegralSlice integral matrix) flag)
    (test := fun matrix => star (normalizedBoundaryResidueAverage degree continuation integral (realSpecialTent radius) matrix))
    (fun flag => ((normalized_eisensteinSummand_continuous flat _ flag).comp
      (realSpecialIntegralSlice_continuous integral)).measurable.aestronglyMeasurable)
    test_measurable.aestronglyMeasurable
    (fun matrix => (normalized_scalar_sum_analytic flat (realSpecialIntegralSlice integral matrix)).2 _ large)
    domain_norm_integrable
  refine ⟨expansion.1, ?_⟩
  rw [principalSpecialLinearQuotient_integral
    (fun point => normalizedScalarEisensteinPrincipalQuotient flat ((3 : ℂ) / 2 + (displacement : ℂ)) integral point *
      star (normalizedBoundaryResidueAveragePrincipalQuotient flat continuation_spec integral (realSpecialTent radius) point))
    ((normalizedScalarEisensteinPrincipalQuotient_measurable flat _ large integral).mul
      quotient_test_measurable).aestronglyMeasurable]
  exact expansion.2

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
