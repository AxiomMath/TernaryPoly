module

public import TernaryPeriodPolynomials.Analysis.Compact.FirstOrderSquare
public import TernaryPeriodPolynomials.Analysis.Compact.ConvolutionDerivativeSquare
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Bound

@[expose] public section


/-! Fixed-scale first-order convolution is bounded by the undifferentiated input L2 norm. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem exists_firstOrder_convolution_bound (v : E) (κ a b : E → ℝ)
    (hκ : ContDiff ℝ 1 κ) (hcκ : HasCompactSupport κ)
    (ha : Continuous a) (hb : Continuous b) (hca : HasCompactSupport a) (hcb : HasCompactSupport b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : E → ℝ, Continuous f → HasCompactSupport f →
      ∫ x, ‖firstOrder v a b (scalarConvolution μ κ f) x‖^2 ∂μ ≤ C * ∫ x, ‖f x‖^2 ∂μ := by
  obtain ⟨A,_,hA⟩ := CompactScalarBound.exists_bound a ha hca
  obtain ⟨B,_,hB⟩ := CompactScalarBound.exists_bound b hb hcb
  let D := (∫ z, ‖fderiv ℝ κ z v‖ ∂μ)^2
  let K := (∫ z, ‖κ z‖ ∂μ)^2
  refine ⟨2*(A^2*D+B^2*K), by dsimp [D,K]; positivity, ?_⟩
  intro f hf hcf
  have h0 := scalarConvolution_signed_square_le μ κ f (hκ.of_le (by norm_num)) hcκ hf hcf
  have h1 := scalarConvolution_derivative_square_le μ κ f hκ hcκ hf hcf v
  have h2 := integral_firstOrder_square_le μ v a b (scalarConvolution μ κ f) ha hb
    (contDiff_scalarConvolution μ κ f hκ hcκ hf) (compact_scalarConvolution μ κ f hcκ hcf) A B hA hB
  calc
    _ ≤ 2*(A^2*(∫ x, ‖fderiv ℝ (scalarConvolution μ κ f) x v‖^2 ∂μ) +
        B^2*(∫ x, ‖scalarConvolution μ κ f x‖^2 ∂μ)) := h2
    _ ≤ 2*(A^2*(D*∫ x, ‖f x‖^2 ∂μ) + B^2*(K*∫ x, ‖f x‖^2 ∂μ)) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (mul_le_mul_of_nonneg_left h1 (sq_nonneg A))
        (mul_le_mul_of_nonneg_left h0 (sq_nonneg B))) (by norm_num)
    _ = _ := by ring

end TernaryPoly.CompactCoordinateIntegration
