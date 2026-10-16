module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.EisensteinPairingVanishing
public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Residue.AveragePairing

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

theorem normalizedBoundaryResidue_tent_pairing_zero
    {degree : ℕ} {inducingData : InducingData degree} {family continuation : ℂ → AdelicGL → ℂ}
    (flat : IsFlatSection inducingData family) (continuation_spec : IsEisensteinContinuation family continuation)
    (integral : GL3 IntegralAdeles) (radius : ℝ) :
    (∫ point, normalizedBoundaryResiduePrincipalQuotient flat continuation_spec integral point *
      star (normalizedBoundaryResidueAveragePrincipalQuotient flat continuation_spec integral (realSpecialTent radius) point)
        ∂principalSpecialLinearQuotientMeasure) = 0 := by
  have converges := normalizedScalarEisensteinPrincipalQuotient_tent_pairing_tendsto flat continuation_spec integral radius
  have zero : ∀ᶠ displacement : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (∫ point, ((displacement : ℂ) * normalizedScalarEisensteinPrincipalQuotient flat
        ((3 : ℂ) / 2 + (displacement : ℂ)) integral point) *
        star (normalizedBoundaryResidueAveragePrincipalQuotient flat continuation_spec integral (realSpecialTent radius) point)
          ∂principalSpecialLinearQuotientMeasure) = 0 := by
    filter_upwards [normalized_scalar_tent_pairing_zero flat continuation_spec integral radius] with displacement pairing_zero
    simp only [mul_assoc, integral_const_mul, pairing_zero, mul_zero]
  apply tendsto_nhds_unique converges
  apply tendsto_const_nhds.congr'
  filter_upwards [zero] with displacement zero_at
  exact zero_at.symm

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
