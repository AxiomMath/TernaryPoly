module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.ReconstructPoint
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.ChartTest
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CompactChartSum

@[expose] public section


/-! Actual inverse-weighted-Gram chart tests span the genuine intrinsic supported compact tests. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormMetric PolynomialFormHilbert
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SmoothLocalDeRham SmoothCoveringDeRham

/-- Every actual compact quotient form supported in the smaller chart open is exactly the finite
sum of actual inverse-Gram compact tests of its actual weighted-Gram scalar coefficient tests. -/
theorem intrinsicMetricCoefficient_reconstruct (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (w : supportedCompactCore n k (chartOpen S Ω)) :
    (∑ i : Index n k, metricDualChartTest n k S Ω hΩ i
      (intrinsicMetricCoefficientTest n k S Ω i w)) = w.val := by
  let t (i : Index n k) := metricDualChartTest n k S Ω hΩ i
    (intrinsicMetricCoefficientTest n k S Ω i w)
  apply Subtype.ext
  apply eq_of_globalChartRepresentative_eq (deckRepresentation n) S
  · exact quotientSupport_compact_sum (deckRepresentation n) k Finset.univ t _
      (fun i _ => metricDualChartTest_support n k S Ω hΩ i _)
  · exact w.property.trans (chartOpen_subset S Ω)
  · apply Form.ext
    intro x hx
    apply (compactChartRepresentative_sum_apply (deckRepresentation n) S k Finset.univ t x).trans
    apply Eq.trans _ (intrinsicMetricCoefficient_reconstruct_point n k S Ω w (quotientChart_target_subset S hx))
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z : Form (F := Coefficients n) (quotientChart S).target k => z.val x)
      (metricDualChartTest_representative n k S Ω hΩ i _)

/-- The same actual reconstruction holds inside the intrinsic supported-test subtype itself. -/
theorem intrinsicMetricCoefficient_reconstruct_supported (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (w : supportedCompactCore n k (chartOpen S Ω)) :
    (∑ i : Index n k, intrinsicMetricDualChartTest n k S Ω hΩ i
      (intrinsicMetricCoefficientTest n k S Ω i w)) = w := by
  apply Subtype.ext
  exact (map_sum (supportedCompactCore n k (chartOpen S Ω)).subtype
    (fun i => intrinsicMetricDualChartTest n k S Ω hΩ i
      (intrinsicMetricCoefficientTest n k S Ω i w)) Finset.univ).trans
        (intrinsicMetricCoefficient_reconstruct n k S Ω hΩ w)

end TernaryPoly.PolynomialFormWeakSmooth
