module

public import TernaryPeriodPolynomials.Analysis.Finite.CoordinateIntegral
public import TernaryPeriodPolynomials.Analysis.Compact.SquareIntegral

@[expose] public section


/-! Coordinate-square estimates for an arbitrary compactly supported continuous vector field. -/
noncomputable section
namespace TernaryPoly.FiniteCoordinateSquare
open MeasureTheory CompactSquareIntegral
variable {E F I : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype I]
  (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

theorem compact_integral_square_le_coordinates (e : F ≃L[ℝ] (I → ℝ))
    (f : E → F) (hf : Continuous f) (hcf : HasCompactSupport f) :
    (∫ x, ‖f x‖^2 ∂μ) ≤
      ‖e.symm.toContinuousLinearMap‖^2 * ∑ i, ∫ x, ‖e (f x) i‖^2 ∂μ := by
  have hc (i : I) : Integrable (fun x => ‖e (f x) i‖^2) μ := by
    have hcont : Continuous (fun x => e (f x) i) := (continuous_apply i).comp (e.continuous.comp hf)
    have hs : HasCompactSupport (fun x => e (f x) i) :=
      hcf.comp_left (g := fun z => e z i) (by simp)
    exact integrable_norm_square _ hcont hs
  exact integral_square_le_coordinates e f (integrable_norm_square f hf hcf) hc

end TernaryPoly.FiniteCoordinateSquare
