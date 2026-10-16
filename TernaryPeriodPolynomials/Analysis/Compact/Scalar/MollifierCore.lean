module

public import TernaryPeriodPolynomials.Analysis.Compact.Scalar.MollifierFriedrichs
public import TernaryPeriodPolynomials.Analysis.Compact.FirstOrderCoefficients

@[expose] public section


/-! A true uniform scalar regularization theorem for compact first-order coefficients. -/
noncomputable section
namespace TernaryPoly.CompactScalarMollifier
open MeasureTheory Filter CompactCoordinateIntegration ScalarFriedrichsEnvelope
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- For fixed compact C1 coefficients there is a single true commutator bound, independent
of both smoothing scale and smooth compact input, and the same commutators converge in L2. -/
theorem compact_coefficients_friedrichs (a b : E → ℝ) (v : E)
    (ha : ContDiff ℝ 1 a) (hb : Continuous b) (hca : HasCompactSupport a) (hcb : HasCompactSupport b) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (f : E → ℝ), ContDiff ℝ 1 f → HasCompactSupport f → ∀ (c : ℝ), 0 < c →
        ∫ x, ‖firstOrder v a b (scalarConvolution μ (kernel E μ c) f) x -
          scalarConvolution μ (kernel E μ c) (firstOrder v a b f) x‖ ^ 2 ∂μ ≤
          C * ∫ y, ‖f y‖ ^ 2 ∂μ) ∧
      (∀ (f : E → ℝ), ContDiff ℝ 1 f → HasCompactSupport f →
        Tendsto (fun c : ℝ => ∫ x, ‖firstOrder v a b (scalarConvolution μ (kernel E μ c) f) x -
          scalarConvolution μ (kernel E μ c) (firstOrder v a b f) x‖ ^ 2 ∂μ) atTop (nhds 0)) := by
  obtain ⟨L, A, B, hL, hA, hB, haL, hda, hbB⟩ :=
    CompactFirstOrderCoefficients.exists_bounds a b v ha hb hca hcb
  refine ⟨(∫ z, envelope ((bump E).normed μ) v L A B z ∂μ) ^ 2, sq_nonneg _, ?_, ?_⟩
  · intro f hf hcf c hc
    exact kernel_commutator_uniform μ a b f v ha hb hf hcf L A B hL hA hB haL hda hbB c hc
  · intro f hf hcf
    exact kernel_commutator_tendsto μ a b f v ha hb hf hcf L A B hL hA hB haL hda hbB

end TernaryPoly.CompactScalarMollifier
