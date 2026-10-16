module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Localization
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier.Formula
public import TernaryPeriodPolynomials.DifferentialForm.Chart.HilbertNorm
public import TernaryPeriodPolynomials.DifferentialForm.WeightedSquare

@[expose] public section


/-! Exact weighted-square formulas for the actual localized and mollified Hilbert vectors. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert
open scoped ContDiff

theorem norm_chartCutoff_eq_weightedSquare (n k : ℕ) (S : Space) (χ : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    ‖inclusion n k (chartCutoff n k S χ hχ hcχ hsχ w)‖^2 =
      ∫ x, weightedSquare n k (cutoffChartRaw n k S χ w) x := by
  have hh := norm_inclusion_square_chart n k S (chartCutoff n k S χ hχ hcχ hsχ w)
    (quotientSupport_chartCutoff n k S χ hχ hcχ hsχ w)
  exact hh.trans (congrArg (fun z : Coordinates → FormValue n k => ∫ x, weightedSquare n k z x)
    (globalChartRepresentative_chartCutoff n k S χ hχ hcχ hsχ w))

theorem norm_chartMollifier_eq_weightedSquare (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    ‖inclusion n k (chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη w)‖^2 =
      ∫ x, weightedSquare n k (mollifiedChartRaw n k S χ η c w) x := by
  have hh := norm_inclusion_square_chart n k S (chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη w)
    (quotientSupport_chartMollifier_source n k S χ η c hc hχ hsχ hη hcη hsη w)
  exact hh.trans (congrArg (fun z : Coordinates → FormValue n k => ∫ x, weightedSquare n k z x)
    (globalChartRepresentative_chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη w))

end TernaryPoly.PolynomialFormCoordinates
