module

public import TernaryPeriodPolynomials.Analysis.Compact.Pairing.BoundedTarget

@[expose] public section

/-! Bounded completion extensions with arbitrary complete targets preserve the proven norm bound. -/
noncomputable section
namespace TernaryPoly.CompactPairingCompletion
open MeasureTheory
variable {X V F : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (d : Data X V)

theorem boundedTargetExtension_bound (L : V →ₗ[ℝ] F) (C : ℝ)
    (hL : ∀ v : V, ‖L v‖ ≤ C * ‖inclusion μ d v‖) (w : Hilbert μ d) :
    ‖boundedTargetExtension μ d L C hL w‖ ≤ C * ‖w‖ := by
  refine (denseRange_inclusion μ d).induction_on
    (p := fun z => ‖boundedTargetExtension μ d L C hL z‖ ≤ C * ‖z‖) w
    (isClosed_le (boundedTargetExtension μ d L C hL).continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro v
  rw [boundedTargetExtension_inclusion μ d L C hL v]
  exact hL v

theorem boundedTargetExtension_opNorm_le (L : V →ₗ[ℝ] F) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ v : V, ‖L v‖ ≤ C * ‖inclusion μ d v‖) :
    ‖boundedTargetExtension μ d L C hL‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (boundedTargetExtension_bound μ d L C hL)

end TernaryPoly.CompactPairingCompletion
