module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.DualTest

@[expose] public section



/-! Exact finite synthesis by the columns of the actual inverse weighted Gram matrix. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open PolynomialFormCoordinates PolynomialFormMetric SymmetricSpaceCharts
open scoped Distributions

/-- The actual finite inverse-Gram test sum has the actual inverse-matrix coordinate vector. -/
theorem metricDualTestRaw_sum_coordinates (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (φ : Index n k → 𝓓(Ω, ℝ)) (x : Coordinates) :
    coordinates n k (∑ i : Index n k, metricDualTestRaw n k Ω i (φ i) x) =
      (weightedGram n k x)⁻¹.mulVec (fun i => φ i x) := by
  funext j
  rw [coordinates_sum]
  simp only [Finset.sum_apply, metricDualTestRaw_coordinates, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

end TernaryPoly.PolynomialFormWeakSmooth
