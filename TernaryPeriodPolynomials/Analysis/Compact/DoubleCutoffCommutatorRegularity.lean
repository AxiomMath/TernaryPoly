module

public import TernaryPeriodPolynomials.Analysis.Compact.DoubleCutoffCommutatorIdentity
public import TernaryPeriodPolynomials.Analysis.Compact.SquareIntegral

@[expose] public section

/-! Continuity and compact support of the literal double-cutoff commutator. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

def doubleCutoffCommutator (κ : E → ℝ) (v : E) (a b χ η f : E → ℝ) (x : E) : ℝ :=
  firstOrder v a b (fun y => η y * scalarConvolution μ κ (fun z => χ z * f z) y) x -
    η x * scalarConvolution μ κ (fun z => χ z * firstOrder v a b f z) x

theorem continuous_doubleCutoffCommutator (κ : E → ℝ) (v : E) (a b χ η f : E → ℝ)
    (hκ : ContDiff ℝ 1 κ) (hcκ : HasCompactSupport κ) (ha : Continuous a) (hb : Continuous b)
    (hχ : Continuous χ) (hη : ContDiff ℝ 1 η) (hf : ContDiff ℝ 1 f) :
    Continuous (doubleCutoffCommutator μ κ v a b χ η f) :=
  (continuous_firstOrder v ha hb (hη.mul (contDiff_scalarConvolution μ κ _ hκ hcκ (hχ.mul hf.continuous)))).sub
    (hη.continuous.mul (contDiff_scalarConvolution μ κ _ hκ hcκ
      (hχ.mul (continuous_firstOrder v ha hb hf))).continuous)

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
theorem compact_doubleCutoffCommutator (κ : E → ℝ) (v : E) (a b χ η f : E → ℝ)
    (hcη : HasCompactSupport η) :
    HasCompactSupport (doubleCutoffCommutator μ κ v a b χ η f) :=
  (compact_firstOrder v a b hcη.mul_right).sub hcη.mul_right

theorem integrable_square_doubleCutoffCommutator (κ : E → ℝ) (v : E) (a b χ η f : E → ℝ)
    (hκ : ContDiff ℝ 1 κ) (hcκ : HasCompactSupport κ) (ha : Continuous a) (hb : Continuous b)
    (hχ : Continuous χ) (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hf : ContDiff ℝ 1 f) :
    Integrable (fun x => doubleCutoffCommutator μ κ v a b χ η f x ^ 2) μ := by
  have h := CompactSquareIntegral.integrable_norm_square _
    (continuous_doubleCutoffCommutator μ κ v a b χ η f hκ hcκ ha hb hχ hη hf)
    (compact_doubleCutoffCommutator μ κ v a b χ η f hcη) (μ := μ)
  simpa only [Real.norm_eq_abs, sq_abs] using h

end TernaryPoly.CompactCoordinateIntegration
