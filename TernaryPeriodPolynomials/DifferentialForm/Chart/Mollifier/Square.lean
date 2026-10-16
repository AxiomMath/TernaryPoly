module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier.Formula
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionSquare
public import TernaryPeriodPolynomials.Analysis.Compact.SquareIntegral
public import TernaryPeriodPolynomials.Analysis.Finite.CoordinateIntegral
public import TernaryPeriodPolynomials.Analysis.Compact.FiniteMollifier
public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Norm

@[expose] public section


/-! Actual uniform coordinate L2 bound for the genuine chart mollifier. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothLocalDeRham SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive SymmetricSpaceQuotientManifold
  CompactCoordinateIntegration CompactSquareIntegral
open scoped ContDiff

theorem mollifiedChartRaw_square_bound (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (M : ℝ) (hM : 0 ≤ M) (hηM : ∀ x, ‖η x‖ ≤ M)
    (c : ℝ) (hc : 0 < c) (w : EquivariantForm (deckRepresentation n) univ k) :
    ∫ x, ‖mollifiedChartRaw n k S χ η c w x‖ ^ 2 ≤
      ‖(coordinates n k).symm.toContinuousLinearMap‖ ^ 2 * M^2 *
        ∑ i, ∫ x, ‖components n k (cutoffChartRaw n k S χ w) i x‖ ^ 2 := by
  have h := finite_mollifier_square_bound (E := Coordinates) (F := FormValue n k) (I := Index n k) volume (coordinates n k)
    (components n k (cutoffChartRaw n k S χ w))
    (fun i => (contDiff_cutoffChartComponents n k S χ hχ hsχ w i).continuous)
    (fun i => compact_cutoffChartComponents n k S χ hcχ w i)
    η hη.continuous hcη M hM hηM c hc
  simpa only [mollifiedChartRaw, convolvedChartRaw] using h

end TernaryPoly.PolynomialFormCoordinates
