module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.Tests
public import TernaryPeriodPolynomials.DifferentialForm.Compact.Chart
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.DualTest

@[expose] public section


/-! Actual compact chart representatives and their true metric coefficient supports. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham

/-- Intrinsically supported tests over a smaller chart open have actual chart support in its
literal coordinate domain. -/
theorem intrinsicTest_chart_tsupport (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates)
    (w : supportedCompactCore n k (chartOpen S Ω)) :
    tsupport (globalChartRepresentative (deckRepresentation n) S k w.val.val).val ⊆ Ω := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := tsupport_globalChartRepresentative n k S w.val
    (w.property.trans (chartOpen_subset S Ω)) hx
  exact (w.property hq).2

/-- Multiplication by the true weighted Gram matrix cannot enlarge the actual support of a
form-valued coefficient field. -/
theorem metricCoefficient_tsupport (n k : ℕ) (f : Coordinates → FormValue n k) (i : Index n k) :
    tsupport (fun x => (weightedGram n k x).mulVec (coordinates n k (f x)) i) ⊆ tsupport f := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  simp only [hx, ContinuousLinearEquiv.map_zero, Matrix.mulVec_zero, Pi.zero_apply]

end TernaryPoly.PolynomialFormWeakSmooth
