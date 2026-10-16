module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionSquare
public import TernaryPeriodPolynomials.Analysis.Compact.SquareIntegral
public import TernaryPeriodPolynomials.Analysis.Finite.CoordinateIntegral

@[expose] public section


/-! Uniform L2 control for actual finite-coordinate mollification with an outer cutoff. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory CompactSquareIntegral
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype I]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem finite_mollifier_square_bound (e : F ≃L[ℝ] (I → ℝ))
    (f : I → E → ℝ) (hf : ∀ i, Continuous (f i)) (hcf : ∀ i, HasCompactSupport (f i))
    (η : E → ℝ) (hη : Continuous η) (hcη : HasCompactSupport η)
    (M : ℝ) (hM : 0 ≤ M) (hηM : ∀ x, ‖η x‖ ≤ M) (c : ℝ) (hc : 0 < c) :
    ∫ x, ‖η x • e.symm (fun i => scalarConvolution μ (CompactScalarMollifier.kernel E μ c) (f i) x)‖^2 ∂μ ≤
      ‖e.symm.toContinuousLinearMap‖^2 * M^2 * ∑ i, ∫ x, ‖f i x‖^2 ∂μ := by
  let v (i : I) := scalarConvolution μ (CompactScalarMollifier.kernel E μ c) (f i)
  let z (x : E) := η x • e.symm (fun i => v i x)
  have hv i : Continuous (v i) := (contDiff_scalarConvolution μ _ _
    (CompactScalarMollifier.kernel_contDiff E μ c)
    (CompactScalarMollifier.kernel_compact E μ c hc.ne') (hf i)).continuous
  have hcv i : HasCompactSupport (v i) := compact_scalarConvolution μ _ _
    (CompactScalarMollifier.kernel_compact E μ c hc.ne') (hcf i)
  have hzcont : Continuous z := hη.smul (e.symm.continuous.comp (continuous_pi hv))
  have hzc : HasCompactSupport z := hcη.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_smul_subset_left η (fun x => e.symm (fun i => v i x)))
  have hform i : (fun x => e (z x) i) = η • v i := by
    funext x
    change e (η x • e.symm (fun i => v i x)) i = _
    rw [map_smul, e.apply_symm_apply]
    rfl
  have hci i : Integrable (fun x => ‖e (z x) i‖^2) μ := by
    change Integrable (fun x => ‖(fun y => e (z y) i) x‖^2) μ
    rw [hform i]
    exact integrable_norm_square _ (hη.smul (hv i)) hcη.smul_right
  have hi (i : I) : (∫ x, ‖e (z x) i‖^2 ∂μ) ≤ M^2 * ∫ x, ‖f i x‖^2 ∂μ := by
    change (∫ x, ‖(fun y => e (z y) i) x‖^2 ∂μ) ≤ _
    rw [hform i]
    exact (cutoff_square_le η (v i) hη hcη (hv i)
      (integrable_norm_square _ (hv i) (hcv i)) M hM hηM).trans
      (mul_le_mul_of_nonneg_left (mollifier_square_le μ c hc (f i) (hf i) (hcf i)) (sq_nonneg M))
  calc
    _ ≤ ‖e.symm.toContinuousLinearMap‖^2 * ∑ i, ∫ x, ‖e (z x) i‖^2 ∂μ :=
      FiniteCoordinateSquare.integral_square_le_coordinates e z (integrable_norm_square z hzcont hzc) hci
    _ ≤ ‖e.symm.toContinuousLinearMap‖^2 * ∑ i, M^2 * ∫ x, ‖f i x‖^2 ∂μ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, ← mul_assoc]

end TernaryPoly.CompactCoordinateIntegration
