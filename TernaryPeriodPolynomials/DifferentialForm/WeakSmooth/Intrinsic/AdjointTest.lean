module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.Differential
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.ChartTest
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CompactAdjointTest

@[expose] public section


/-! The exact genuine compact adjoint formula inside intrinsic supported test spaces. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialFormCoordinates SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering
  SmoothCoveringDeRham
open scoped Distributions

/-- The true support-preserving compact adjoint of an actual intrinsic inverse-Gram test is the
actual finite sum of lower-degree inverse-Gram tests of the actual scalar transpose derivatives. -/
theorem supportedCompactAdjoint_metricTest (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (j : Index n (k+1)) (φ : 𝓓(Ω, ℝ)) :
    supportedCompactAdjoint n k (chartOpen S Ω) (intrinsicMetricDualChartTest n (k+1) S Ω hΩ j φ) =
      ∑ i : Index n k, intrinsicMetricDualChartTest n k S Ω hΩ i
        (scalarMatrixTransposeTest Ω (fun d : Fin 5 => Pi.single d 1)
          (fun j i d => symbolMatrix n k d j i) j φ i) := by
  apply Subtype.ext
  exact (compactAdjoint_metricDualChartTest n k S Ω hΩ j φ).trans
    (map_sum (supportedCompactCore n k (chartOpen S Ω)).subtype
      (fun i => intrinsicMetricDualChartTest n k S Ω hΩ i
        (scalarMatrixTransposeTest Ω (fun d : Fin 5 => Pi.single d 1)
          (fun j i d => symbolMatrix n k d j i) j φ i)) Finset.univ).symm

end TernaryPoly.PolynomialFormWeakSmooth
