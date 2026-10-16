module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.ConvolutionRegularity

@[expose] public section


/-! The literal scalar commutator and its genuine smooth compact-input regularity. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def scalarCommutator (κ : E → ℝ) (v : E) (a b f : E → ℝ) (x : E) : ℝ :=
  firstOrder v a b (scalarConvolution μ κ f) x - scalarConvolution μ κ (firstOrder v a b f) x

theorem continuous_scalarCommutator (κ : E → ℝ) (v : E) (a b f : E → ℝ)
    (hκ : ContDiff ℝ 1 κ) (hcκ : HasCompactSupport κ)
    (ha : Continuous a) (hb : Continuous b) (hf : ContDiff ℝ 1 f) :
    Continuous (scalarCommutator μ κ v a b f) :=
  (continuous_firstOrder v ha hb (contDiff_scalarConvolution μ κ f hκ hcκ hf.continuous)).sub
    (contDiff_scalarConvolution μ κ (firstOrder v a b f) hκ hcκ
      (continuous_firstOrder v ha hb hf)).continuous

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem compact_scalarCommutator (κ : E → ℝ) (v : E) (a b f : E → ℝ)
    (hcκ : HasCompactSupport κ) (hcf : HasCompactSupport f) :
    HasCompactSupport (scalarCommutator μ κ v a b f) :=
  (compact_firstOrder v a b (compact_scalarConvolution μ κ f hcκ hcf)).sub
    (compact_scalarConvolution μ κ (firstOrder v a b f) hcκ (compact_firstOrder v a b hcf))

theorem integrable_square_scalarCommutator (κ : E → ℝ) (v : E) (a b f : E → ℝ)
    (hκ : ContDiff ℝ 1 κ) (hcκ : HasCompactSupport κ)
    (ha : Continuous a) (hb : Continuous b) (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f) :
    Integrable (fun x => scalarCommutator μ κ v a b f x ^ 2) μ := by
  apply ((continuous_scalarCommutator μ κ v a b f hκ hcκ ha hb hf).pow 2).integrable_of_hasCompactSupport
  simpa only [pow_two, Pi.mul_apply] using
    (compact_scalarCommutator μ κ v a b f hcκ hcf).mul_right (f' := scalarCommutator μ κ v a b f)

end TernaryPoly.CompactCoordinateIntegration
