module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.CurrentCoordinates
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.AdjointTest

@[expose] public section


/-! The intrinsic local current differential has the exact true exterior-symbol coordinates. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialFormCoordinates SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering
  SmoothCoveringDeRham
open scoped Distributions

/-- The intrinsic support-local differential is exactly the genuine constant-symbol weak
exterior derivative in actual scalar chart-current coordinates. -/
theorem intrinsicCurrentCoordinates_differential (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (j : Index n (k+1)) (T : IntrinsicCurrent n k (chartOpen S Ω)) :
    intrinsicCurrentCoordinates n (k+1) S Ω hΩ (intrinsicCurrentDifferential n k (chartOpen S Ω) T) j =
      ∑ i : Index n k, ∑ d : Fin 5, symbolMatrix n k d j i •
        scalarWeakDerivative Ω (Pi.single d 1) (intrinsicCurrentCoordinates n k S Ω hΩ T i) := by
  apply LinearMap.ext
  intro φ
  change T (supportedCompactAdjoint n k (chartOpen S Ω)
    (intrinsicMetricDualChartTest n (k+1) S Ω hΩ j φ)) = _
  apply (congrArg T (supportedCompactAdjoint_metricTest n k S Ω hΩ j φ)).trans
  simp only [map_sum, scalarMatrixTransposeTest, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, scalarWeakDerivative_apply, intrinsicCurrentCoordinates,
    LinearMap.comp_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro d _
  ring

end TernaryPoly.PolynomialFormWeakSmooth
