module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.CoefficientTest
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.ChartTest
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.DualCancellation

@[expose] public section


/-! Exact actual weighted coordinate extraction on the actual inverse-Gram supported tests. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham
open scoped Distributions

/-- The actual weighted coordinate of an actual inverse-Gram test is the actual scalar test in
its own coordinate, and zero in every other coordinate. -/
theorem intrinsicMetricCoefficientTest_basis (n : ℕ) (k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (i j : Index n k) (φ : 𝓓(Ω, ℝ)) :
    intrinsicMetricCoefficientTest n k S Ω j (intrinsicMetricDualChartTest n k S Ω hΩ i φ) =
      if j = i then φ else 0 := by
  apply TestFunction.ext
  intro x
  have hrep := congrArg (fun z : Form (F := Coefficients n) (quotientChart S).target k => z.val)
    (metricDualChartTest_representative n k S Ω hΩ i φ)
  have hcoord := congrFun (congrFun (metricDualTestRaw_metricDual n k Ω
    (hΩ.trans (quotientChart_target_subset S)) i φ) j) x
  have he := congrArg (fun f : Coordinates → FormValue n k =>
    (weightedGram n k x).mulVec (coordinates n k (f x)) j) hrep
  change intrinsicMetricCoefficientTest n k S Ω j (intrinsicMetricDualChartTest n k S Ω hΩ i φ) x = _ at he
  apply he.trans
  convert hcoord using 1 <;> first | rfl | (split_ifs <;> rfl)

end TernaryPoly.PolynomialFormWeakSmooth
