module

public import TernaryPeriodPolynomials.DifferentialForm.Chart.Cutoff
public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Basic
public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.LocalRegularity
public import TernaryPeriodPolynomials.Analysis.Compact.Weighted.ConvolutionTranspose

@[expose] public section


/-! Smooth compact metric-dual input for the actual chart transpose. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open Set SmoothCoveringDeRham PolynomialCoefficientMetric PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpacePositive CompactCoordinateIntegration
open scoped ContDiff

def chartDualInput (n k : ℕ) (S : Space) (η : Coordinates → ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) (i : Index n k) (x : Coordinates) : ℝ :=
  η x * metricDual (weightedGram n k)
    (components n k (globalChartRepresentative (deckRepresentation n) S k w).val) i x

theorem tsupport_chartDualInput (n k : ℕ) (S : Space) (η : Coordinates → ℝ)
    (w : EquivariantForm (deckRepresentation n) univ k) (i : Index n k) :
    tsupport (chartDualInput n k S η w i) ⊆ tsupport η :=
  tsupport_mul_subset_left

theorem contDiff_chartDualInput (n k : ℕ) (S : Space) (η : Coordinates → ℝ)
    (hη : ContDiff ℝ ∞ η) (hsη : tsupport η ⊆ (quotientChart S).target)
    (w : EquivariantForm (deckRepresentation n) univ k) (i : Index n k) :
    ContDiff ℝ ∞ (chartDualInput n k S η w i) := by
  apply contDiff_of_tsupport_subset (quotientChart S).open_target _
    ((tsupport_chartDualInput n k S η w i).trans hsη)
  apply hη.contDiffOn.mul
  apply contDiffOn_metricDual
  · intro j l
    exact (contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram n k) j) l).mono
      (quotientChart_target_subset S)
  · intro j
    exact contDiffOn_components n k
      (SmoothLocalDeRham.Form.smooth (globalChartRepresentative (deckRepresentation n) S k w)) j

theorem compact_chartDualInput (n k : ℕ) (S : Space) (η : Coordinates → ℝ)
    (hcη : HasCompactSupport η) (w : EquivariantForm (deckRepresentation n) univ k) (i : Index n k) :
    HasCompactSupport (chartDualInput n k S η w i) :=
  hcη.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartDualInput n k S η w i)

end TernaryPoly.PolynomialFormCoordinates
