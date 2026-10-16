module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Metric.DualCancellation
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.TransposeTest

@[expose] public section



/-! The actual weighted local adjoint on inverse-Gram coordinate tests. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialFormCoordinates PolynomialFormMetric SymmetricSpaceCharts CompactCoordinateIntegration
open scoped Distributions

/-- The actual local formal adjoint applied to an inverse-Gram test is the finite sum of genuine
inverse-Gram tests of the constant exterior-symbol transpose derivatives. -/
theorem localAdjoint_metricDualTestRaw (n k : ℕ) (Ω : TopologicalSpace.Opens Coordinates)
    (hΩ : (Ω : Set Coordinates) ⊆ positiveCoordinates) (j : Index n (k + 1)) (φ : 𝓓(Ω, ℝ)) :
    localAdjoint n k (metricDualTestRaw n (k + 1) Ω j φ) =
      fun x => ∑ i : Index n k, metricDualTestRaw n k Ω i
        (scalarMatrixTransposeTest Ω (fun d : Fin 5 => Pi.single d 1)
          (fun j i d => symbolMatrix n k d j i) j φ i) x := by
  funext x
  apply (coordinates n k).injective
  change coordinates n k ((coordinates n k).symm _) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, coordinates_sum]
  unfold weightedMatrixAdjoint
  rw [metricDualTestRaw_metricDual n (k + 1) Ω hΩ j φ]
  funext r
  change (∑ l : Index n k, (weightedGram n k x)⁻¹ r l *
    matrixTranspose (fun d : Fin 5 => Pi.single d 1) (differentialCoefficients n k)
      (fun _ _ _ _ => 0) (fun l y => if l = j then φ y else 0) l x) = _
  simp only [Finset.sum_apply, metricDualTestRaw_coordinates, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [show differentialCoefficients n k = (fun j i d _ => symbolMatrix n k d j i) from rfl,
    scalarMatrixTransposeTest_eq]
  exact mul_comm _ _

end TernaryPoly.PolynomialFormWeakSmooth
