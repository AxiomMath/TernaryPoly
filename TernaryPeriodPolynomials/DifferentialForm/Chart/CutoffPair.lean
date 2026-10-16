module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.LimitPredicate

@[expose] public section


/-! Actual smooth compact inner and outer coordinate cutoffs in a specified quotient chart. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive
open scoped ContDiff

structure ChartCutoffPair (S : Space) where
  inner : Coordinates → ℝ
  outer : Coordinates → ℝ
  inner_smooth : ContDiff ℝ ∞ inner
  inner_compact : HasCompactSupport inner
  inner_support : tsupport inner ⊆ (quotientChart S).target
  outer_smooth : ContDiff ℝ ∞ outer
  outer_compact : HasCompactSupport outer
  outer_support : tsupport outer ⊆ (quotientChart S).target

end TernaryPoly.PolynomialFormCoordinates
