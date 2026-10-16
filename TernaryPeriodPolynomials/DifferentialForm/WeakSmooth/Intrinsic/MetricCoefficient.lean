module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.CoordinateSupport

@[expose] public section


/-! The actual weighted-Gram scalar coefficients of actual supported quotient test forms. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham
  CompactCoordinateIntegration
open scoped ContDiff Distributions

/-- The literal metric-dual chart coefficient of an actual supported compact test form. -/
def intrinsicMetricCoefficient (n k : ℕ) (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (w : supportedCompactCore n k (chartOpen S Ω)) (i : Index n k) (x : Coordinates) : ℝ :=
  (weightedGram n k x).mulVec
    (coordinates n k ((globalChartRepresentative (deckRepresentation n) S k w.val.val).val x)) i

/-- The actual weighted coefficient has actual compact support in the scalar-test domain. -/
theorem intrinsicMetricCoefficient_tsupport (n k : ℕ) (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (w : supportedCompactCore n k (chartOpen S Ω)) (i : Index n k) :
    tsupport (intrinsicMetricCoefficient n k S Ω w i) ⊆ Ω :=
  (metricCoefficient_tsupport n k _ i).trans (intrinsicTest_chart_tsupport n k S Ω w)

/-- The actual weighted coefficient of the chart test is globally smooth, including its true
zero extension beyond the compact coordinate support. -/
theorem intrinsicMetricCoefficient_smooth (n k : ℕ) (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (w : supportedCompactCore n k (chartOpen S Ω)) (i : Index n k) :
    ContDiff ℝ ∞ (intrinsicMetricCoefficient n k S Ω w i) := by
  apply contDiff_of_tsupport_subset (quotientChart S).open_target
  · apply contDiffOn_metricDual
    · intro j l
      exact (contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram n k) j) l).mono
        (quotientChart_target_subset S)
    · intro j
      exact contDiffOn_components n k
        (Form.smooth (globalChartRepresentative (deckRepresentation n) S k w.val.val)) j
  · exact (metricCoefficient_tsupport n k _ i).trans
      (tsupport_globalChartRepresentative_target n k S w.val (w.property.trans (chartOpen_subset S Ω)))

/-- The actual weighted coefficient has genuine compact coordinate support. -/
theorem intrinsicMetricCoefficient_compact (n k : ℕ) (S : Space) (Ω : TopologicalSpace.Opens Coordinates)
    (w : supportedCompactCore n k (chartOpen S Ω)) (i : Index n k) :
    HasCompactSupport (intrinsicMetricCoefficient n k S Ω w i) :=
  (hasCompactSupport_globalChartRepresentative n k S w.val (w.property.trans (chartOpen_subset S Ω))).of_isClosed_subset
    (isClosed_tsupport _) (metricCoefficient_tsupport n k _ i)

end TernaryPoly.PolynomialFormWeakSmooth
