module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.Tests
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.ChartTest

@[expose] public section


/-! Genuine inverse-Gram tests lie in the actual smaller quotient-open supported test space. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormHilbert
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham
open scoped Distributions

/-- The actual inverse-Gram chart test is supported in the genuine smaller quotient neighborhood
cut out by its actual scalar-test domain. -/
theorem metricDualChartTest_support_chartOpen (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (i : Index n k) (φ : 𝓓(Ω, ℝ)) :
    quotientSupport (metricDualChartTest n k S Ω hΩ i φ).val ⊆ chartOpen S Ω := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := quotientSupport_compactChartExtend (deckRepresentation n) S
    (metricDualChartForm n k S Ω hΩ i φ)
    (metricDualTestRaw_hasCompactSupport n k Ω i φ)
    ((metricDualTestRaw_tsupport n k Ω i φ).trans (φ.tsupport_subset.trans hΩ)) hq
  have hxΩ := φ.tsupport_subset (metricDualTestRaw_tsupport n k Ω i φ hx)
  refine ⟨(quotientChart S).map_target (hΩ hxΩ), ?_⟩
  change (quotientChart S) ((quotientChart S).symm x) ∈ (Ω : Set Coordinates)
  rw [(quotientChart S).right_inv (hΩ hxΩ)]
  exact hxΩ

/-- The literal inverse-Gram chart test as an element of the intrinsic supported test space. -/
def intrinsicMetricDualChartTest (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (i : Index n k) : 𝓓(Ω, ℝ) →ₗ[ℝ] supportedCompactCore n k (chartOpen S Ω) :=
  (metricDualChartTest n k S Ω hΩ i).codRestrict (supportedCompactCore n k (chartOpen S Ω))
    (metricDualChartTest_support_chartOpen n k S Ω hΩ i)

end TernaryPoly.PolynomialFormWeakSmooth
