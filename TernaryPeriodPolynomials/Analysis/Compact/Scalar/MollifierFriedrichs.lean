module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.Mollifier
public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.FriedrichsConvergence

@[expose] public section


/-! Uniform boundedness and strong compact-input convergence for a fully constructed mollifier. -/
noncomputable section
namespace TernaryPoly.CompactScalarMollifier
open MeasureTheory Filter CompactCoordinateIntegration ScalarFriedrichsEnvelope
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A fully constructed compact smooth mollifier has a uniform true derivative-commutator bound. -/
theorem kernel_commutator_uniform (a b f : E → ℝ) (v : E)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f)
    (L A B : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haL : ∀ x y, ‖a x - a y‖ ≤ L * ‖x-y‖)
    (hda : ∀ y, ‖fderiv ℝ a y v‖ ≤ A) (hbB : ∀ y, ‖b y‖ ≤ B) (c : ℝ) (hc : 0 < c) :
    ∫ x, ‖firstOrder v a b (scalarConvolution μ (kernel E μ c) f) x -
      scalarConvolution μ (kernel E μ c) (firstOrder v a b f) x‖ ^ 2 ∂μ ≤
      (∫ z, envelope ((bump E).normed μ) v L A B z ∂μ) ^ 2 * ∫ y, ‖f y‖ ^ 2 ∂μ :=
  firstOrder_convolution_commutator_uniform μ _ a b f v ha hb hf (bump E).contDiff_normed hcf
    (bump E).hasCompactSupport_normed L A B hL hA hB haL hda hbB c hc

/-- The actual constructed mollifier's full first-order commutator converges to zero in L2. -/
theorem kernel_commutator_tendsto (a b f : E → ℝ) (v : E)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hf : ContDiff ℝ 1 f) (hcf : HasCompactSupport f)
    (L A B : ℝ) (hL : 0 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (haL : ∀ x y, ‖a x - a y‖ ≤ L * ‖x-y‖)
    (hda : ∀ y, ‖fderiv ℝ a y v‖ ≤ A) (hbB : ∀ y, ‖b y‖ ≤ B) :
    Tendsto (fun c : ℝ => ∫ x, ‖firstOrder v a b (scalarConvolution μ (kernel E μ c) f) x -
      scalarConvolution μ (kernel E μ c) (firstOrder v a b f) x‖ ^ 2 ∂μ) atTop (nhds 0) :=
  firstOrder_convolution_commutator_integral_tendsto μ _ a b f v ha hb hf (bump E).contDiff_normed hcf
    (bump E).hasCompactSupport_normed (bump E).nonneg_normed (bump E).integral_normed L A B hL hA hB haL hda hbB

end TernaryPoly.CompactScalarMollifier
