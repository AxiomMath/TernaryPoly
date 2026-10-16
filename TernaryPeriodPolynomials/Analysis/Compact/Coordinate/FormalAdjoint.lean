module

public import TernaryPeriodPolynomials.Analysis.Compact.Coordinate.Integration

@[expose] public section


/-! Explicit first-order scalar formal adjoints, including variable coefficients. -/
noncomputable section
namespace TernaryPoly.CompactCoordinateIntegration
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The actual first-order expression, not an abstract adjoint assumption. -/
def firstOrder (v : E) (a b f : E → ℝ) (x : E) : ℝ :=
  a x * fderiv ℝ f x v + b x * f x

/-- Its actual transpose divergence expression. -/
def transposeOrder (v : E) (a b g : E → ℝ) (x : E) : ℝ :=
  b x * g x - fderiv ℝ (fun y => a y * g y) x v

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_firstOrder {a b f : E → ℝ} (v : E)
    (ha : Continuous a) (hb : Continuous b) (hf : ContDiff ℝ 1 f) :
    Continuous (firstOrder v a b f) :=
  (ha.mul ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)).add
    (hb.mul hf.continuous)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_transposeOrder {a b g : E → ℝ} (v : E)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hg : ContDiff ℝ 1 g) :
    Continuous (transposeOrder v a b g) :=
  (hb.mul hg.continuous).sub
    ((ha.mul hg).continuous_fderiv one_ne_zero |>.clm_apply continuous_const)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem compact_firstOrder (v : E) (a b : E → ℝ) {f : E → ℝ}
    (hc : HasCompactSupport f) : HasCompactSupport (firstOrder v a b f) :=
  (hc.fderiv_apply ℝ v).mul_left.add hc.mul_left

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem compact_transposeOrder (v : E) (a b : E → ℝ) {g : E → ℝ}
    (hc : HasCompactSupport g) : HasCompactSupport (transposeOrder v a b g) :=
  hc.mul_left.sub (hc.mul_left.fderiv_apply ℝ v)

/-- Integration by parts gives the actual transpose expression for variable scalar coefficients. -/
theorem integral_firstOrder_mul {a b f g : E → ℝ} (v : E)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport f) :
    ∫ x, firstOrder v a b f x * g x ∂μ =
      ∫ x, f x * transposeOrder v a b g x ∂μ := by
  have hdf := (hf.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := v))
  have hdag := ((ha.mul hg).continuous_fderiv one_ne_zero).clm_apply
    (continuous_const (y := v))
  have h1 : Integrable (fun x => fderiv ℝ f x v * (a x * g x)) μ :=
    (hdf.mul (ha.continuous.mul hg.continuous)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_right
  have h2 : Integrable (fun x => f x * (b x * g x)) μ :=
    (hf.continuous.mul (hb.mul hg.continuous)).integrable_of_hasCompactSupport hc.mul_right
  have h3 : Integrable (fun x => f x * fderiv ℝ (fun y => a y * g y) x v) μ :=
    (hf.continuous.mul hdag).integrable_of_hasCompactSupport hc.mul_right
  have hpoint : (fun x => firstOrder v a b f x * g x) =
      (fun x => fderiv ℝ f x v * (a x * g x) + f x * (b x * g x)) := by
    funext x; dsimp [firstOrder]; ring
  have hpoint' : (fun x => f x * transposeOrder v a b g x) =
      (fun x => f x * (b x * g x) - f x * fderiv ℝ (fun y => a y * g y) x v) := by
    funext x; dsimp [transposeOrder]; ring
  rw [hpoint, hpoint', integral_add h1 h2, integral_sub h2 h3,
    integral_fderiv_mul hf (ha.mul hg) hc v]
  ring

end TernaryPoly.CompactCoordinateIntegration
