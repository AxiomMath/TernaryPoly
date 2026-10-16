module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Mollifier.Formula
public import TernaryPeriodPolynomials.Analysis.Compact.Weighted.ConvolutionTranspose

@[expose] public section


noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set MeasureTheory SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive CompactCoordinateIntegration
open scoped ContDiff

theorem components_cutoffChartRaw (n k : ℕ) (S : Space) (χ : Coordinates → ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) (i : Index n k) (x : Coordinates) :
    components n k (cutoffChartRaw n k S χ w) i x =
      χ x * components n k (globalChartRepresentative (deckRepresentation n) S k w).val i x := by
  change (coordinates n k (χ x • (globalChartRepresentative (deckRepresentation n) S k w).val x)) i = _
  rw [map_smul]
  rfl

theorem components_mollifiedChartRaw_eq_cutoffConvolution (n k : ℕ) (S : Space)
    (χ η : Coordinates → ℝ) (c : ℝ) (a : EquivariantForm (deckRepresentation n) univ k) :
    components n k (mollifiedChartRaw n k S χ η c a) =
      cutoffConvolution volume (CompactScalarMollifier.kernel Coordinates volume c) χ η
        (components n k (globalChartRepresentative (deckRepresentation n) S k a).val) := by
  funext i x
  have hf : (fun y => χ y * components n k (globalChartRepresentative (deckRepresentation n) S k a).val i y) =
      components n k (cutoffChartRaw n k S χ a) i :=
    funext (fun y => (components_cutoffChartRaw n k S χ a i y).symm)
  rw [components_mollifiedChartRaw]
  unfold cutoffConvolution
  rw [hf]

end TernaryPoly.PolynomialFormCoordinates
