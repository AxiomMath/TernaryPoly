module

public import TernaryPeriodPolynomials.DifferentialForm.Coefficient.CompactForget
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.PositiveExactness

@[expose] public section

/-! The exact positive-degree rational compact-to-ordinary vanishing gate. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceAllTopBoundary

theorem positivePolynomialInnerVanishing : PositivePolynomialInnerVanishing :=
  PolynomialCoefficientMetric.positivePolynomialInnerVanishing_of_smooth_exact
    (fun _ hn => PolynomialFormWeakSmooth.positive_degree_compact_smooth_exact hn)

end TernaryPoly.SymmetricSpaceAllTopBoundary
