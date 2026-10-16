module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier
public import TernaryPeriodPolynomials.DifferentialForm.Coordinate.Norm
public import TernaryPeriodPolynomials.Analysis.Compact.FiniteMollifierApproximation

@[expose] public section


/-! Actual local form convergence under the outer cutoff for the genuine chart mollifier. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory Filter SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive CompactCoordinateIntegration
open scoped ContDiff

theorem mollifiedChartRaw_square_tendsto (n k : ℕ) (S : Space) (χ η : Coordinates → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ (quotientChart S).target)
    (hη : Continuous η) (hcη : HasCompactSupport η)
    (w : EquivariantForm (deckRepresentation n) univ k) :
    Tendsto (fun c : ℝ => ∫ x, ‖mollifiedChartRaw n k S χ η c w x -
      η x • cutoffChartRaw n k S χ w x‖^2) atTop (nhds 0) := by
  have h := cutoff_finite_mollifier_square_tendsto (E := Coordinates) (F := FormValue n k)
    (I := Index n k) volume (coordinates n k) (components n k (cutoffChartRaw n k S χ w))
    (fun i => (contDiff_cutoffChartComponents n k S χ hχ hsχ w i).continuous)
    (fun i => compact_cutoffChartComponents n k S χ hcχ w i) η hη hcη
  simpa only [mollifiedChartRaw, convolvedChartRaw, components,
    ContinuousLinearEquiv.symm_apply_apply, smul_sub] using h

end TernaryPoly.PolynomialFormCoordinates
