module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.CoverIntegration

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open scoped TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementUnfolding

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelIntegration

theorem lintegral_le (function : BinaryAdelicGL → ENNReal) (measurable : Measurable function)
    (invariant : ∀ rational : BinaryRationalGL, ∀ point,
      function (Matrix.GeneralLinearGroup.map rationalAdele rational * point) = function point) :
    ∫⁻ point in BinaryFundamentalDomain.domain, function point ∂BinaryHaar.measure ≤
      ∫⁻ point in AdelicSiegelCover.region, function point ∂BinaryHaar.measure :=
  CoverIntegration.lintegral_le BinaryFundamentalDomain.domain_fundamental SiegelMeasurability.region_measurable
    AdelicSiegelCover.covers function measurable invariant

theorem integrableOn (function : BinaryAdelicGL → ℂ) (measurable : Measurable function)
    (invariant : ∀ rational : BinaryRationalGL, ∀ point,
      function (Matrix.GeneralLinearGroup.map rationalAdele rational * point) = function point)
    (integrable : IntegrableOn function AdelicSiegelCover.region BinaryHaar.measure) :
    IntegrableOn function BinaryFundamentalDomain.domain BinaryHaar.measure :=
  CoverIntegration.integrableOn BinaryFundamentalDomain.domain_fundamental SiegelMeasurability.region_measurable
    AdelicSiegelCover.covers function measurable invariant integrable

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.SiegelIntegration
