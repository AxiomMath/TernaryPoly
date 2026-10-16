module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionRegularity
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Exact transposition of the actual compact scalar convolution. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem integral_scalarConvolution_mul (κ f g : E → ℝ)
    (hκ : Continuous κ) (hf : Continuous f) (hg : Continuous g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    ∫ x, scalarConvolution μ κ f x * g x ∂μ =
      ∫ y, f y * scalarConvolution μ (fun z => κ (-z)) g y ∂μ := by
  let F : E × E → ℝ := fun p => f p.2 * κ (p.1-p.2) * g p.1
  have hF : Continuous F :=
    ((hf.comp continuous_snd).mul (hκ.comp (continuous_fst.sub continuous_snd))).mul
      (hg.comp continuous_fst)
  have hcF : HasCompactSupport F := by
    apply (hcg.prod hcf).of_isClosed_subset (isClosed_tsupport F)
    apply closure_minimal _ (isClosed_tsupport g |>.prod (isClosed_tsupport f))
    intro p hp
    have hne : f p.2 * κ (p.1-p.2) * g p.1 ≠ 0 := hp
    exact ⟨subset_tsupport _ ((mul_ne_zero_iff.mp hne).2),
      subset_tsupport _ ((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1)⟩
  have hi : Integrable F (μ.prod μ) := hF.integrable_of_hasCompactSupport hcF
  calc
    _ = ∫ x, ∫ y, f y * κ (x-y) * g x ∂μ ∂μ := by
      simp only [scalarConvolution_apply, integral_mul_const]
    _ = ∫ y, ∫ x, f y * κ (x-y) * g x ∂μ ∂μ := integral_integral_swap hi
    _ = _ := by
      simp only [scalarConvolution_apply, ← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => integral_congr_ae
        (Filter.Eventually.of_forall (fun x => by dsimp only; rw [neg_sub]; ring)))

end TernaryPoly.CompactCoordinateIntegration
