module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.CoefficientTest
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.TestSynthesis

@[expose] public section


/-! Exact pointwise reconstruction of actual supported compact test forms from metric coefficients. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham

/-- The actual inverse-Gram tests of the actual weighted coefficients reconstruct the actual
compact test form at each genuine chart coordinate. -/
theorem intrinsicMetricCoefficient_reconstruct_point (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (w : supportedCompactCore n k (chartOpen S Ω))
    {x : Coordinates} (hx : x ∈ positiveCoordinates) :
    (∑ i : Index n k, metricDualTestRaw n k Ω i (intrinsicMetricCoefficientTest n k S Ω i w) x) =
      (globalChartRepresentative (deckRepresentation n) S k w.val.val).val x := by
  apply (coordinates n k).injective
  apply (metricDualTestRaw_sum_coordinates n k Ω
    (fun i => intrinsicMetricCoefficientTest n k S Ω i w) x).trans
  change (weightedGram n k x)⁻¹.mulVec ((weightedGram n k x).mulVec
    (coordinates n k ((globalChartRepresentative (deckRepresentation n) S k w.val.val).val x))) = _
  exact (Matrix.mulVec_mulVec _ _ _).trans
    ((congrArg (fun M : Matrix (Index n k) (Index n k) ℝ => M.mulVec
      (coordinates n k ((globalChartRepresentative (deckRepresentation n) S k w.val.val).val x)))
      (Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (weightedGram_isUnit n k x hx)))).trans
        (Matrix.one_mulVec _))

end TernaryPoly.PolynomialFormWeakSmooth
