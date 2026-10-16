module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.TransposeFormula
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier.Formula
public import TernaryPeriodPolynomials.DifferentialForm.Chart.Inner
public import TernaryPeriodPolynomials.DifferentialForm.Chart.TransposeIntegral

@[expose] public section

/-! The actual compact transpose satisfies the literal Hilbert test identity. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive PolynomialFormHilbert CompactCoordinateIntegration
open scoped ContDiff

theorem inner_chartMollifier_transpose (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ) (c : ℝ)
    (hc : c ≠ 0) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (a b : Core n k) :
    inner ℝ (inclusion n k (chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη a.val)) (inclusion n k b) =
      inner ℝ (inclusion n k a) (inclusion n k (chartTranspose n k S χ η c hc hχ hcχ hsχ hη hsη b.val)) := by
  have hleft := inner_inclusion_chart n k S
    (chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη a.val) b
    (quotientSupport_chartMollifier_source n k S χ η c hc hχ hsχ hη hcη hsη a.val)
  have hright := inner_inclusion_chart_right n k S a
    (chartTranspose n k S χ η c hc hχ hcχ hsχ hη hsη b.val)
    (quotientSupport_chartTranspose_source n k S χ η c hc hχ hcχ hsχ hη hsη b.val)
  have hl := hleft.trans (congrArg (fun z : Coordinates → FormValue n k =>
    ∫ x, weightedPairing (weightedGram n k) (components n k z)
      (components n k (globalChartRepresentative (deckRepresentation n) S k b.val).val) x)
    (globalChartRepresentative_chartMollifier n k S χ η c hc hχ hsχ hη hcη hsη a.val))
  have hr := hright.trans (congrArg (fun z : Coordinates → FormValue n k =>
    ∫ x, weightedPairing (weightedGram n k)
      (components n k (globalChartRepresentative (deckRepresentation n) S k a.val).val)
      (components n k z) x)
    (globalChartRepresentative_chartTranspose n k S χ η c hc hχ hcχ hsχ hη hsη b.val))
  exact hl.trans ((integral_chartMollifier_transpose n k S χ η c hc hχ hcχ hsχ hη hcη hsη a.val b.val).trans hr.symm)

end TernaryPoly.PolynomialFormCoordinates
