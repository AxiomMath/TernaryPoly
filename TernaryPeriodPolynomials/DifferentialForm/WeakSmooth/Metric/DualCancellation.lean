module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.DualPairing

@[expose] public section


/-! Global cancellation of the true weighted Gram matrix on supported inverse-Gram tests. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialFormCoordinates PolynomialFormMetric SymmetricSpaceCharts CompactCoordinateIntegration
open scoped Distributions

/-- Weighted test coordinates equal the actual scalar single-coordinate test everywhere. The
support hypothesis controls the region where the genuine Gram inverse need not be invertible. -/
theorem metricDualTestRaw_metricDual (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (i : Index n k) (φ : 𝓓(Ω, ℝ)) :
    metricDual (weightedGram n k) (components n k (metricDualTestRaw n k Ω i φ)) =
      fun j x => if j = i then φ x else 0 := by
  funext j x
  change ((weightedGram n k x).mulVec (coordinates n k (metricDualTestRaw n k Ω i φ x))) j = _
  by_cases hx : x ∈ positiveCoordinates
  · rw [metricDualTestRaw_gram n k Ω i φ hx]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hΩ (φ.tsupport_subset ht)))
    have hr : metricDualTestRaw n k Ω i φ x = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hΩ (φ.tsupport_subset (metricDualTestRaw_tsupport n k Ω i φ ht))))
    rw [hr, ContinuousLinearEquiv.map_zero, Matrix.mulVec_zero]
    simp only [Pi.zero_apply, hz, ite_self]

end TernaryPoly.PolynomialFormWeakSmooth
