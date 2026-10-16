module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.UnipotentCompactDomain
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.InducedContinuity
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.HeightMajorant

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineConstantTerm

abbrev parameterMeasure := TernaryPeriodPolynomials.PlaneEisensteinContinuation.PlaneConstantTerm.parameterMeasure

def average (function : AdelicGL → ℂ) (point : AdelicGL) : ℂ :=
  ∫ pair, function (lineUnipotent pair.1 pair.2 * point) ∂parameterMeasure

theorem parameterMeasure_eq :
    parameterMeasure = radicalMeasure.restrict (additiveDomain ×ˢ additiveDomain) := by
  exact Measure.prod_restrict _ _

theorem average_eq (function : AdelicGL → ℂ) (point : AdelicGL) :
    average function point = ∫ pair in additiveDomain ×ˢ additiveDomain,
      function (lineUnipotent pair.1 pair.2 * point) ∂radicalMeasure := by
  rw [average, parameterMeasure_eq]

end TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.LineConstantTerm
