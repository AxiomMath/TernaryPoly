module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.CompactAdjointTest
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.ChartCurrent

@[expose] public section

/-! Genuine quotient weak differentiation in actual scalar coordinate currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormMetric PolynomialFormHilbert
  SymmetricSpaceCharts SymmetricSpacePositive SymmetricSpaceCovering SmoothCoveringDeRham
open scoped Distributions

@[simp] theorem coordinateTestCurrent_apply (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (i : Index n k) (T : TestDual n k) (φ : 𝓓(Ω, ℝ)) :
    coordinateTestCurrent n k S Ω hΩ i T φ = T (metricDualChartTest n k S Ω hΩ i φ) := rfl

/-- The actual transpose of the genuine compact adjoint becomes the literal constant-symbol
weak exterior derivative of the genuine scalar coordinate currents. -/
theorem coordinateTestCurrent_differential (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (j : Index n (k+1)) (T : TestDual n k) :
    coordinateTestCurrent n (k+1) S Ω hΩ j (testDifferential n k T) =
      ∑ i : Index n k, ∑ d : Fin 5, symbolMatrix n k d j i •
        scalarWeakDerivative Ω (Pi.single d 1) (coordinateTestCurrent n k S Ω hΩ i T) := by
  apply LinearMap.ext
  intro φ
  change T (compactAdjoint n k (metricDualChartTest n (k+1) S Ω hΩ j φ)) = _
  rw [compactAdjoint_metricDualChartTest n k S Ω hΩ j φ]
  simp only [map_sum, scalarMatrixTransposeTest, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, scalarWeakDerivative_apply, coordinateTestCurrent_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- The actual maximal Hilbert graph equation gives the genuine distributional coordinate
exterior differential equation, with no smoothness assumption on the Hilbert input. -/
theorem maximal_graph_coordinate_differential (n k : ℕ) (S : Space)
    (Ω : TopologicalSpace.Opens Coordinates) (hΩ : (Ω : Set Coordinates) ⊆ (quotientChart S).target)
    (u : Hilbert n k) (z : Hilbert n (k+1))
    (h : (u,z) ∈ (maximalDifferential n k).graph) (j : Index n (k+1)) :
    coordinateHilbertCurrent n (k+1) S Ω hΩ j z =
      ∑ i : Index n k, ∑ d : Fin 5, symbolMatrix n k d j i •
        scalarWeakDerivative Ω (Pi.single d 1) (coordinateHilbertCurrent n k S Ω hΩ i u) := by
  have he := (maximal_graph_iff_testDifferential n k u z).mp h
  exact (congrArg (coordinateTestCurrent n (k+1) S Ω hΩ j) he).symm.trans
    (coordinateTestCurrent_differential n k S Ω hΩ j (hilbertTest n k u))

end TernaryPoly.PolynomialFormWeakSmooth
