module

public import TernaryPeriodPolynomials.Analysis.Compact.SquareIntegral

@[expose] public section


/-! Square-integral control of sums of compact continuous scalar functions. -/
namespace TernaryPoly.CompactSquareIntegral
open MeasureTheory
variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

theorem integral_add_square_le (f g : E → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hcf : HasCompactSupport f) (hcg : HasCompactSupport g) :
    ∫ x, ‖f x + g x‖ ^ 2 ∂μ ≤
      2 * ((∫ x, ‖f x‖ ^ 2 ∂μ) + ∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hfi := integrable_norm_square f hf hcf (μ := μ)
  have hgi := integrable_norm_square g hg hcg (μ := μ)
  have h := integral_mono (integrable_norm_square (fun x => f x + g x) (hf.add hg) (hcf.add hcg))
    ((hfi.add hgi).const_mul 2) (fun x => by
      simpa only [Pi.add_apply, Real.norm_eq_abs, sq_abs] using (add_sq_le (a := f x) (b := g x)))
  simpa only [Pi.add_apply, integral_const_mul, integral_add hfi hgi] using h

end TernaryPoly.CompactSquareIntegral
